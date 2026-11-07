# Citation And Provenance

This file records external mathematical and code sources used by the
submission-facing Lean formalization. It complements
`FORMALIZATION_COVERAGE.md`; it is not a license grant.

## Citation Rules

- The camera-ready manuscript defines the statements and proof structure.
- The authors' final appendix text provides the proofs formalized in
  `BordaIPO.lean` and `OfflineIPO.lean`. These follow the zero-loss and
  normalization argument and the constant-difference argument, respectively.
- Bibliographic metadata are given in the paper's references.
- Cite local PDFs by their bibliographic entries, not by file path. Local
  copies are working references, not redistribution permissions.
- Third-party Lean code is not vendored in the submission-facing formalization.

## NLHF Existence: Sion and Komiya

The paper-facing NLHF existence proof applies the Apache-2.0 Mathlib theorem
`Sion.exists_isSaddlePointOn` from `Mathlib.Topology.Sion` directly to the
finite lottery simplex. The project proves the required simplex convexity and
compactness, KL continuity and convexity (including the boundary), and affine
margin properties in `PaperFormalization/NLHFExistence.lean`. It does not
assume Brouwer's theorem. The Mathlib module is authored by Antoine
Chambert-Loir and Anatole Dedecker and states that its formal proof follows
Komiya's elementary proof of Sion's theorem.

Mathematical sources:

- Maurice Sion, “On general minimax theorems,” *Pacific Journal of
  Mathematics* 8(1) (1958), 171–176,
  <https://doi.org/10.2140/pjm.1958.8.171>.
- Hidetoshi Komiya, “Elementary proof for Sion's minimax theorem,” *Kodai
  Mathematical Journal* 11(1) (1988), 5–7,
  <https://doi.org/10.2996/kmj/1138038812>.

No third-party Brouwer formalization is imported, vendored, or used.

## Anderson Ranking

The project-specific proof follows L. B. Anderson, H. Dandurova, J. E. Falk,
and L. Yeganova, “Relationships between Borda voting and Zermelo ranking,”
*Social Choice and Welfare* 32 (2009), 355–365,
<https://doi.org/10.1007/s00355-008-0327-7>, especially pp. 360–361. The full
formal proof and the apparent `M(i,j)`/`M(i,k)` typo in printed Eq. (4) are
documented in `AndersonRanking.lean`.

## Noothigattu Citation Check (2026-10-28)

The citation in the `RTBTPM` proof is correct. Checked Noothigattu, Peters,
and Procaccia, “Axioms for Learning from Pairwise Comparisons” (NeurIPS 2020),
Definition 4.1 and Theorem 4.2 in the
[official paper](https://proceedings.neurips.cc/paper_files/paper/2020/file/cdaa9b682e10c291d3bbadca4c96f5de-Paper.pdf),
and the proof in Appendix D of its
[supplement](https://proceedings.neurips.cc/paper_files/paper/2020/file/cdaa9b682e10c291d3bbadca4c96f5de-Supplemental.pdf).
The theorem requires a strictly increasing, log-concave, differentiable
comparison link; Bradley–Terry's logistic link qualifies. Definition 4.1
requires unique fitted parameters (up to the common additive normalization)
at both endpoints and concerns their differences against every alternative.
It does not require equal pair totals.

In the manuscript, these differences are `log(u_x/u_z)`; exponentiation gives
the required ratio inequalities. Adding a weak `(x,y)` comparison either adds
a strict `x`-win or removes a strict `y`-win, depending on the reverse
comparison; removing weak `(y,x)` has the same two possibilities. Thus the
cited single-count monotonicity applies at every step. Both endpoint
connectivity assumptions ensure every intermediate graph remains connected,
as proved by `FordStronglyConnected_of_between`. Lean retains its direct
Ford-equation comparative-static proof.

## Source Map

The camera-ready partial-Borda formula gives half a point for either
indifference or incomparability. On partial orders this is half the score
`2 down(a) + incomp(a)` in Definition 1 of Cullinan, Hsiao, and Polett,
“A Borda count for partially ordered ballots,” *Social Choice and Welfare*
42 (2014), 913–926, <https://doi.org/10.1007/s00355-013-0751-1>.
The paper extends this formula to arbitrary reflexive relations. Its
equivalent raw-margin formulation is formalized in
`PaperFormalization.two_mul_partialBordaScoreP` in `WeakProfileBorda.lean`. The missing-comparison credit does not
change the paper's normalization of NLHF comparison frequencies.

| Formalized area | Lean files | Sources to cite | Notes |
| --- | --- | --- | --- |
| Lean and library foundations | all Lean files; `lakefile.lean`; `lake-manifest.json`; `lean-toolchain` | `lean4`, `mathlib4` | Pinned to Lean/mathlib `v4.30.0`; exact mathlib revision `c5ea00351c28e24afc9f0f84379aa41082b1188f`; Mathlib is Apache-2.0. |
| Paper-facing statement index and audit | `PaperFormalization/PaperStatements.lean`, `PaperFormalization/AssumptionAudit.lean`, `scripts/check_artifact.sh` | paper sources below; `lean4`, `mathlib4` | `PaperStatements.lean` collects thin aliases named after the paper labels; `AssumptionAudit.lean` prints the axioms of those aliases. |
| NLHF fixed point, uniqueness, and saddle formulation | `PaperFormalization/NLHFBasic.lean`, `PaperFormalization/NLHFExistence.lean`, selected NLHF files | `Munos2024`; Sion (1958), DOI 10.2140/pjm.1958.8.171; Komiya (1988), DOI 10.2996/kmj/1138038812; background `rosen1965` | Existence specializes Mathlib's Sion theorem; the project proves its finite-simplex KL and margin hypotheses and derives the fixed point, uniqueness, and saddle wrappers. |
| Ford/Zermelo/Bradley-Terry theorem and selectors | `PaperFormalization/FordZermelo.lean`, `PaperFormalization/ProfileFord.lean`, DPO/RTBT files | `zermelo1929`, `ford1957`, `bradley1952` | The formalization follows the finite closed-simplex/product-objective and displayed-equation structure audited in `FORMALIZATION_COVERAGE.md`. |
| DPO as RTBT | `PaperFormalization/DPO.lean`, `PaperFormalization/RTBT.lean`, `PaperFormalization/ProfileRTBT.lean` | `rafailov2023`, `ford1957`, `bradley1952`, `shirali2025` | The Lean bridge statements are project-specific formal versions of the paper's RTBT/DPO connection. |
| IPO and Borda-IPO minimizers | `PaperFormalization/BordaIPO.lean`, `PaperFormalization/OfflineIPO.lean` | Proofs in Appendix `IPOApp`; Azar et al. (2024), §5.2, Eq. (16), for the offline-IPO background | Project-specific proofs following the authors' final appendix text. They concern the two defined objectives and the reduction of the population IPO loss (Eq. (16), expectation as a finite average) to `IPO_τ`. |
| RTBT monotonicity comparative statics | `PaperFormalization/RTBTCountMonotonicity.lean`, `PaperFormalization/RTBTPairMonotonicity.lean`, `PaperFormalization/ProfileRTBT.lean` | `noothigattu2020` | The general heterogeneous-count comparative static is proved directly from Ford's displayed equations. The English citation is verified above; Lean gives a direct proof of the same comparative-static result. |
| Anderson result | `PaperFormalization/AndersonRanking.lean`, `PaperFormalization/RTBT.lean` | `anderson2009` | The paper-specific BT-vs-Borda equivalence is proved from Ford's displayed equations for finite linear-order profiles, following Anderson, Dandurova, Falk, and Yeganova (2009), pp. 360--361; `RTBT.lean` supplies the positive-power/uniform-reference transport to every `β > 0`.  The module comment also records the apparent `M(i,j)`/`M(i,k)` typo in printed Eq. (4). |
| Maximal lotteries and probabilistic social choice background | `PaperFormalization/MaximalLotteryLimit.lean`, `PaperFormalization/Core.lean` | `fishburn1984`, `brandl2016`, `brandl2022` | The Lean statements formalize the finite KL/coordinatewise convergence and maximal-lottery predicates used in the paper. |
| Proportional Borda and profile-level Borda material | `PaperFormalization/ProportionalBorda.lean`, `PaperFormalization/ProfileBorda.lean` | `heckelman2003`, `terzopoulou2021`, `cullinan2014b` | Cite the paper bibliography for the voting-rule background; the Lean proofs are the project-specific formal versions used by the paper. |
| NLHF and RTBT axiom violations | `PaperFormalization/NLHFSelectedMonotonicity.lean`, `PaperFormalization/NLHFSelectedInvolvement.lean`, `PaperFormalization/NLHFSelectedCommutativity.lean`, `PaperFormalization/RTBTInvolvement.lean` | paper proof appendix; background references above | Concrete witness algebra and selected-rule wrappers are formalized in Lean. |
