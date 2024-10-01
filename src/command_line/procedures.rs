use {
    crate::{
        analyzing::tightness::Tightness,
        command_line::{
            arguments::{Arguments, Command, Equivalence, Format, Property, Role, Translation},
            files::Files,
        },
        syntax_tree::{
            asp,
            fol::{self, Theory},
            Node as _,
        },
        translating::{completion::completion, gamma::gamma, tau_star::tau_star},
        verifying::{
            problem,
            prover::{vampire::Vampire, Prover, Report, Status, Success},
            task::{
                external_equivalence::ExternalEquivalenceTask,
                strong_equivalence::{transition, StrongEquivalenceTask},
                Task,
            },
        },
    },
    anyhow::{anyhow, Context, Result},
    clap::Parser as _,
    either::Either,
};

fn output_theory(theory: Theory, helper_axioms: Option<Theory>, format: Format, role: Role) {
    match format {
        Format::Default => print!("{theory}"),
        Format::TPTP => {
            let role_string = match role {
                Role::Axiom => "axiom",
                Role::Conjecture => "conjecture",
            };

            let axioms = match helper_axioms {
                Some(x) => x,
                None => Theory { formulas: vec![] },
            };

            let problem = problem::Problem::with_name("theory")
                .add_theory(axioms, |i, formula| problem::AnnotatedFormula {
                    name: format!("helper_axiom_{i}"),
                    role: problem::Role::Axiom,
                    formula,
                })
                .add_theory(theory, |i, formula| problem::AnnotatedFormula {
                    name: format!("{role_string}_{i}"),
                    role: match role {
                        Role::Axiom => problem::Role::Axiom,
                        Role::Conjecture => problem::Role::Conjecture,
                    },
                    formula,
                });

            print!("{problem}");
        }
    }
}

pub fn main() -> Result<()> {
    match Arguments::parse().command {
        Command::Analyze { property, input } => {
            match property {
                Property::Tightness => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let is_tight = program.is_tight();
                    println!("{is_tight}");
                }
            }

            Ok(())
        }

        Command::Translate {
            with,
            input,
            format,
            role,
        } => {
            match with {
                Translation::Completion => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let completed_theory =
                        completion(theory).context("the given theory is not completable")?;
                    output_theory(completed_theory, None, format, role)
                }

                Translation::Gamma => {
                    let theory =
                        input.map_or_else(fol::Theory::from_stdin, fol::Theory::from_file)?;
                    let transition_axioms = Theory {
                        formulas: theory.prediates().into_iter().map(transition).collect(),
                    };
                    let gamma_theory = gamma(theory);
                    output_theory(gamma_theory, Some(transition_axioms), format, role)
                }

                Translation::TauStar => {
                    let program =
                        input.map_or_else(asp::Program::from_stdin, asp::Program::from_file)?;
                    let theory = tau_star(program);
                    output_theory(theory, None, format, role)
                }
            }

            Ok(())
        }

        Command::Verify {
            equivalence,
            decomposition,
            direction,
            bypass_tightness,
            no_simplify,
            no_eq_break,
            no_proof_search,
            time_limit,
            prover_instances,
            prover_cores,
            save_problems: out_dir,
            files,
        } => {
            let files =
                Files::sort(files).context("unable to sort the given files by their function")?;

            let problems = match equivalence {
                Equivalence::Strong => StrongEquivalenceTask {
                    left: asp::Program::from_file(
                        files
                            .left()
                            .ok_or(anyhow!("no left program was provided"))?,
                    )?,
                    right: asp::Program::from_file(
                        files
                            .right()
                            .ok_or(anyhow!("no right program was provided"))?,
                    )?,
                    decomposition,
                    direction,
                    simplify: !no_simplify,
                    break_equivalences: !no_eq_break,
                }
                .decompose()?
                .report_warnings(),
                Equivalence::External => ExternalEquivalenceTask {
                    specification: match files
                        .specification()
                        .ok_or(anyhow!("no specification was provided"))?
                    {
                        Either::Left(program) => Either::Left(asp::Program::from_file(program)?),
                        Either::Right(specification) => {
                            Either::Right(fol::Specification::from_file(specification)?)
                        }
                    },
                    program: asp::Program::from_file(
                        files.program().ok_or(anyhow!("no program was provided"))?,
                    )?,
                    user_guide: fol::UserGuide::from_file(
                        files
                            .user_guide()
                            .ok_or(anyhow!("no user guide was provided"))?,
                    )?,
                    proof_outline: files
                        .proof_outline()
                        .map(fol::Specification::from_file)
                        .unwrap_or_else(|| Ok(fol::Specification::empty()))?,
                    decomposition,
                    direction,
                    bypass_tightness,
                    simplify: !no_simplify,
                    break_equivalences: !no_eq_break,
                }
                .decompose()?
                .report_warnings(),
            };

            if let Some(out_dir) = out_dir {
                for problem in &problems {
                    let mut path = out_dir.clone();
                    path.push(format!("{}.p", problem.name));
                    problem.to_file(path)?;
                }
            }

            if !no_proof_search {
                let prover = Vampire {
                    time_limit,
                    instances: prover_instances,
                    cores: prover_cores,
                };

                let problems = problems.into_iter().inspect(|problem| {
                    println!("> Proving {}...", problem.name);
                    println!("Axioms:");
                    for axiom in problem.axioms() {
                        println!("    {}", axiom.formula);
                    }
                    println!();
                    println!("Conjectures:");
                    for conjecture in problem.conjectures() {
                        println!("    {}", conjecture.formula);
                    }
                    println!();
                });

                let mut success = true;
                for result in prover.prove_all(problems) {
                    match result {
                        Ok(report) => match report.status() {
                            Ok(status) => {
                                println!(
                                    "> Proving {} ended with a SZS status",
                                    report.problem.name
                                );
                                println!("Status: {status}");
                                if !matches!(status, Status::Success(Success::Theorem)) {
                                    success = false;
                                }
                            }
                            Err(error) => {
                                println!(
                                    "> Proving {} ended without a SZS status",
                                    report.problem.name
                                );
                                println!("Output/stdout:");
                                println!("{}", report.output.stdout);
                                println!("Output/stderr:");
                                println!("{}", report.output.stderr);
                                println!("Error: {error}");
                                success = false;
                            }
                        },
                        Err(error) => {
                            println!("> Proving <a problem> ended with an error"); // TODO: Get the name of the problem
                            println!("Error: {error}");
                            success = false;
                        }
                    }
                    println!();
                }

                if success {
                    println!("> Success! Anthem found a proof of equivalence.")
                } else {
                    println!("> Failure! Anthem was unable to find a proof of equivalence.")
                }
            }

            Ok(())
        }
    }
}
