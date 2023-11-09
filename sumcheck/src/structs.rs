use ff::PrimeField;
use multilinear_extensions::virtual_poly::VirtualPolynomial;
use serde::{Deserialize, Serialize};
use transcript::Challenge;

/// An IOP proof is a collections of
/// - messages from prover to verifier at each round through the interactive
///   protocol.
/// - a point that is generated by the transcript for evaluation
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct IOPProof<F> {
    pub point: Vec<F>,
    pub proofs: Vec<IOPProverMessage<F>>,
}
impl<F: PrimeField> IOPProof<F> {
    #[allow(dead_code)]
    pub(crate) fn extract_sum(&self) -> F {
        let res = self.proofs[0].evaluations[0] + self.proofs[0].evaluations[1];

        res
    }
}

/// A message from the prover to the verifier at a given round
/// is a list of evaluations.
#[derive(Clone, Debug, Default, PartialEq, Eq, Serialize, Deserialize)]
pub struct IOPProverMessage<F> {
    pub(crate) evaluations: Vec<F>,
}

/// Prover State of a PolyIOP.
pub struct IOPProverState<F> {
    /// sampled randomness given by the verifier
    pub challenges: Vec<Challenge<F>>,
    /// the current round number
    pub(crate) round: usize,
    /// pointer to the virtual polynomial
    pub(crate) poly: VirtualPolynomial<F>,
    /// points with precomputed barycentric weights for extrapolating smaller
    /// degree uni-polys to `max_degree + 1` evaluations.
    pub(crate) extrapolation_aux: Vec<(Vec<F>, Vec<F>)>,
}

/// Prover State of a PolyIOP
pub struct IOPVerifierState<F> {
    pub(crate) round: usize,
    pub(crate) num_vars: usize,
    pub(crate) max_degree: usize,
    pub(crate) finished: bool,
    /// a list storing the univariate polynomial in evaluation form sent by the
    /// prover at each round
    pub(crate) polynomials_received: Vec<Vec<F>>,
    /// a list storing the randomness sampled by the verifier at each round
    pub(crate) challenges: Vec<Challenge<F>>,
}

/// A SumCheckSubClaim is a claim generated by the verifier at the end of
/// verification when it is convinced.
#[derive(Clone, Debug, Default, PartialEq, Eq)]
pub struct SumCheckSubClaim<F> {
    /// the multi-dimensional point that this multilinear extension is evaluated
    /// to
    pub point: Vec<Challenge<F>>,
    /// the expected evaluation
    pub expected_evaluation: F,
}
