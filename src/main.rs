pub mod command_line;
pub mod convenience;
pub mod formatting;
pub mod parsing;
pub mod problem_building;
pub mod simplifying;
pub mod syntax_tree;
pub mod translating;

use {
    crate::{
        command_line::{Arguments, Command, Translation},
        problem_building::Problem,
        syntax_tree::{
            asp,
            fol::{self, Theory},
        },
        translating::tau_star::tau_star,
    },
    anyhow::{Context, Result},
    clap::Parser as _,
    std::fs::read_to_string,
    translating::gamma::gamma,
};

fn main() -> Result<()> {
    match Arguments::parse().command {
        Command::Translate { with, input } => {
            let content = read_to_string(&input)
                .with_context(|| format!("could not read file `{}`", input.display()))?;

            match with {
                Translation::Gamma => {
                    let theory: fol::Theory = content
                        .parse()
                        .with_context(|| format!("could not parse file `{}`", input.display()))?;

                    let theory = gamma(theory);

                    print!("{theory}")
                }

                Translation::TauStar => {
                    let program: asp::Program = content
                        .parse()
                        .with_context(|| format!("could not parse file `{}`", input.display()))?;

                    let theory = tau_star(program);

                    print!("{theory}")
                }
            }

            Ok(())
        }

        Command::BuildProblem {
            axioms,
            conjectures,
        } => {
            let axioms_string = read_to_string(&axioms)
                .with_context(|| format!("could not read file `{}`", axioms.display()))?;

            let conjectures_string = read_to_string(&conjectures)
                .with_context(|| format!("could not read file `{}`", conjectures.display()))?;

            let axioms_program = axioms_string
                .parse()
                .with_context(|| format!("could not parse file `{}`", axioms.display()))?;

            let conjectures_program = conjectures_string
                .parse()
                .with_context(|| format!("could not parse file `{}`", conjectures.display()))?;

            let problem = Problem::from_parts(
                gamma(tau_star(axioms_program)),
                Theory::empty(),
                gamma(tau_star(conjectures_program)),
            );

            print!("{problem}");

            Ok(())
        }
    }
}
