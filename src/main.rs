pub mod command_line;
pub mod convenience;
pub mod formatting;
pub mod parsing;
pub mod simplifying;
pub mod syntax_tree;
pub mod translating;

use {
    crate::{
        command_line::{Arguments, Command, Translation},
        syntax_tree::{asp, fol},
        translating::tau_star::tau_star,
    },
    anyhow::{Context, Result},
    clap::Parser as _,
    std::fs::read_to_string,
    translating::gamma::gamma,
};

fn main() -> Result<()> {
    let p1: Result<asp::Program, _> = "p(X) :- q(X++1), not r(X). \nq(X) :- not r(X).".parse();
    match p1 {
        Err(e) => {
            let s = e.line();
            let r1: Result<asp::Rule, _> = s.parse();
            match r1 {
                Err(e1) => println!("{e1}"),
                _ => todo!(),
            }
        },
        _ => todo!(),
    }
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
    }
}
