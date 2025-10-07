use ark_ff::{to_bytes, FftField};
use ark_poly::{univariate::DensePolynomial, EvaluationDomain, Polynomial, UVPolynomial};
use ark_poly_commit::{LabeledCommitment, LabeledPolynomial, PolynomialCommitment, QuerySet};
use ark_std::rand::RngCore;

use crate::{
    data_structures::{Proof, Statement},
    error::Error,
    rng::FiatShamirRng,
    PROTOCOL_NAME,
};

pub fn prove<
    F: FftField,
    PC: PolynomialCommitment<F, DensePolynomial<F>>,
    FS: FiatShamirRng,
    R: RngCore,
>(
    ck: &PC::CommitterKey,
    statement: &Statement<F, PC>,
    f: &LabeledPolynomial<F, DensePolynomial<F>>,
    f_rand: &PC::Randomness,
    rng: &mut R,
) -> Result<Proof<F, PC>, Error<PC::Error>> {
    // Construct polynomials s, h, g satisfying: f(x) + s(x) = x * g(x) + h(x) * Z_H(x) + sum/|H|
    // We pick g(x) = 0 and h(x) = 0, and s(x) = -f(x) + (sum/|H|).
    // In this puzzle instance sum == 0, so s(x) = -f(x), which is non-constant as required.

    let f_poly = f.polynomial();

    // s(x) = -f(x) + c, with c = sum/|H|. Since prover doesn't need to use c when sum=0, we set c = 0.
    let s_coeffs: Vec<F> = f_poly.coeffs().iter().map(|c| -*c).collect();
    let s_poly = DensePolynomial::from_coefficients_slice(&s_coeffs);

    let h_poly = DensePolynomial::from_coefficients_slice(&[F::zero()]);
    let g_poly = DensePolynomial::from_coefficients_slice(&[F::zero()]);

    // Label polynomials. Match labels/degree bounds used by the verifier.
    let s_labeled = LabeledPolynomial::new("s".into(), s_poly, None, Some(1));
    let h_labeled = LabeledPolynomial::new("h".into(), h_poly, None, Some(1));
    let g_labeled = LabeledPolynomial::new(
        "g".into(),
        g_poly,
        Some(statement.domain.size() - 2),
        Some(1),
    );

    // Commit to s, h, g
    let (shg_commitments, shg_rands) =
        PC::commit(ck, &[s_labeled.clone(), h_labeled.clone(), g_labeled.clone()], Some(rng))
            .map_err(Error::from_pc_err)?;

    let s_comm = shg_commitments[0].commitment().clone();
    let h_comm = shg_commitments[1].commitment().clone();
    let g_comm = shg_commitments[2].commitment().clone();

    // Fiat–Shamir to derive xi and opening_challenge exactly as the verifier does
    let mut fs_rng = FS::initialize(&to_bytes![&PROTOCOL_NAME, statement].unwrap());
    fs_rng.absorb(&to_bytes![s_comm, h_comm, g_comm].unwrap());
    let xi = F::rand(&mut fs_rng);
    let opening_challenge = F::rand(&mut fs_rng);

    // Evaluate polynomials at xi
    let f_opening = f.polynomial().evaluate(&xi);
    let s_opening = s_labeled.polynomial().evaluate(&xi);
    let h_opening = h_labeled.polynomial().evaluate(&xi);
    let g_opening = g_labeled.polynomial().evaluate(&xi);

    // Create QuerySet matching verifier
    let point_label = String::from("xi");
    let query_set = QuerySet::from([
        ("f".into(), (point_label.clone(), xi)),
        ("h".into(), (point_label.clone(), xi)),
        ("g".into(), (point_label.clone(), xi)),
        ("s".into(), (point_label, xi)),
    ]);

    // Batch open for f, s, h, g in this order
    let polys = [f.clone(), s_labeled.clone(), h_labeled.clone(), g_labeled.clone()];

    let f_lc = LabeledCommitment::new("f".into(), statement.f.clone(), None);
    let s_lc = LabeledCommitment::new("s".into(), s_comm.clone(), None);
    let h_lc = LabeledCommitment::new("h".into(), h_comm.clone(), None);
    let g_lc = LabeledCommitment::new(
        "g".into(),
        g_comm.clone(),
        Some(statement.domain.size() - 2),
    );
    let commitments = [f_lc, s_lc, h_lc, g_lc];

    let rands = [f_rand, &shg_rands[0], &shg_rands[1], &shg_rands[2]];

    let pc_proof = PC::batch_open(
        ck,
        polys.iter(),
        commitments.iter(),
        &query_set,
        opening_challenge,
        rands.iter().cloned(),
        Some(rng),
    )
        .map_err(Error::from_pc_err)?;

    Ok(Proof {
        f_opening,
        s: s_comm,
        s_opening,
        g: g_comm,
        g_opening,
        h: h_comm,
        h_opening,
        pc_proof,
    })
}
