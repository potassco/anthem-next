use {
    clap::{Parser, Subcommand, ValueEnum},
    std::path::PathBuf,
};

#[derive(Debug, Parser)]
#[command(author, version, about, long_about = None)]
pub struct Arguments {
    #[command(subcommand)]
    pub command: Command,
}

#[derive(Debug, Subcommand)]
pub enum Command {
    /// Translate a given answer set program or first-order theory
    Translate {
        /// The translation to use
        #[arg(long, value_enum)]
        with: Translation,

        /// The file to translate
        input: PathBuf,
    },

    /// Create and optionally verify a set of problem files from a claim about answer set programs or first-order theories
    Verify {
        /// The equivalence theory used to proof the claim
        #[arg(long, value_enum)]
        equivalence: Equivalence,

        /// The decomposition strategy to use
        #[arg(long, value_enum, default_value_t)]
        decomposition: Decomposition,

        /// The direction of the proof
        #[arg(long, value_enum, default_value_t)]
        direction: Direction,

        /// Omit simplifications
        #[arg(long, action)]
        no_simplify: bool,

        /// Omit breaking equivalences
        #[arg(long, action)]
        no_eq_break: bool,

        /// Omit proof search and just create problem files
        #[arg(long, action)]
        no_proof_search: bool,

        /// The destination directory for the problem files
        #[arg(long)]
        out_dir: Option<PathBuf>,

        /// A specification of intended behavior
        left: PathBuf,

        /// A file about which the claim is constructed
        right: PathBuf,

        /// Additional knowledge used to construct the claim (e.g., user guide, proof outline)
        aux: Vec<PathBuf>,
    },
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Translation {
    Completion,
    Gamma,
    TauStar,
}

#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Equivalence {
    Strong,
    External,
}

#[derive(Copy, Clone, Debug, Default, PartialEq, Eq, PartialOrd, Ord, ValueEnum)]
pub enum Decomposition {
    Independent,
    #[default]
    Sequential,
}

pub use crate::syntax_tree::fol::Direction;

#[cfg(test)]
mod tests {
    use super::Arguments;

    #[test]
    fn verify() {
        use clap::CommandFactory as _;
        Arguments::command().debug_assert()
    }
}
