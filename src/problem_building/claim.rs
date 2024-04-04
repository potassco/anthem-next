use {
    crate::{
        syntax_tree::{asp, fol},
    },
    super::problem_building::Problem,
};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Strategy {
    Default,
    Sequential,
}

/// Program to specification verification
/// Based on direction, prove p->s, s->p, or p<->s
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SpecificationEquivalenceClaim {
    user_guide: fol::UserGuide,
    program: asp::Program,
    specification: fol::Specification,
    proof_outline: fol::Specification,
    direction: fol::Direction,
    strategy: Strategy,
    break_equivalences: bool,
    simplify: bool,
}

/// Program to program (external behavior) verification
/// Based on direction, prove p->s, s->p, or p<->s
pub struct ExternalEquivalenceClaim {
    user_guide: fol::UserGuide,
    program: asp::Program,
    specification: asp::Program,
    proof_outline: fol::Specification,
    direction: fol::Direction,
    strategy: Strategy,
    break_equivalences: bool,
    simplify: bool,
}

/// Strong equivalence verification
pub struct StrongEquivalenceClaim {
    program: asp::Program,
    specification: asp::Program,
    proof_outline: fol::Specification,
    strategy: Strategy,
    break_equivalences: bool,
    simplify: bool,
}


pub trait Claim {
    fn summarize(&self) -> String;

    fn decompose(&self) -> Vec<Problem>;
}

impl Claim for ExternalEquivalenceClaim {
    fn summarize(&self) -> String {
        format!("tbd")
    }

    // "derive" here means to insert associated problems at beginning of sequence
    fn decompose(&self) -> Vec<Problem> {
        // Step 1:   Error handling 
        //           (checking that all function constants in our files have been declared as inputs,
        //           checking that the specified direction is consistent with formula annotations)
        // Step 2:   Placeholder replacement. If "n" occurs in formula COMP[tau*(Pi)] and
        //           the user guide contains a placeholder "n$<s>" replace "n" in formula with function constant "n$<s>"

        // Step 3:   Identify public/private predicates, resolve pivate predicate name conflicts
        // Step 3.1: Separate completed definitions of private predicates in P1 from other theory formulas 
        // Step 3.2: Separate completed definitions of private predicates in P2 from other theory formulas 

        // Step 4.1: Assemble stable premises 
        //           (includes Definitions from proof outline, assumptions from user guide, completed defs of private preds)
        // Step 4.2: Assemble forward premises 
        //           (remaining formulas from COMP[tau*(P1)])
        // Step 4.3: Assemble backward premises 
        //           (remaining formulas from COMP[tau*(P2)])

        // Step 5:   Derive universal lemmas and universal inductive lemmas from stable premises
        // Step 6a:  If direction is forward, derive forward direction lemmas, then backward premises
        //           (ignore backward direction lemmas with warning)
        // Step 6b:  If direction is backward, derive backward direction lemmas, then forward premises
        //           (ignore forward direction lemmas with warning)
        // Step 6c:  If direction is universal, do 6a then 6b (without issuing warnings about lemma annotations)

        // Keep in mind that if Strategy::Sequential then premises need to be extended every time
        vec![]
    }
}

// verify (p, s, u, o) --sequential --forward -b -s
//      becomes SpecificationEquivalenceClaim with strategy sequential, direction forward, breaking equivalences and simplify on
