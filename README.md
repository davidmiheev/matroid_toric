# matroid_toric

Working repository for the thesis *«Инварианты матроидов, определяемых действиями тора»*
(D. A. Mikheev, Mech-Math MSU, 2022; advisor V. M. Buchstaber) and for the follow-up
program derived from its audit.

## Contents

| Path | What it is |
|---|---|
| `docs/thesis_matroid_invariants_torus_actions.pdf` | The thesis as submitted (20 pp., 18 refs). |
| `audit/matroid_torus_thesis_audit.md` | Checkpoint audit (CP0–CP4): reference pins, mathematical audit, priority fix table, development program. |
| `docs/thesis-v2/` | **Revised English edition** of the thesis (`thesis_en.pdf`, 22 pp.): all errata applied, counterexample proved in §4.5. `CHANGES.md` logs every change against the audit, including where the audit itself was wrong. |
| `experiments/cluster_permutohedra/` | Homology of cluster-permutohedra behind the corrected Examples 4.29–4.30, and the global-poset comparison for the witness pair. |
| `experiments/counterexample/` | The Track A sweep: scripts, verified witness pairs, and what is left to confirm in Macaulay2. |
| `engine/` | **mtengine**: one interface (Python API, `mte` CLI, MCP server) to Macaulay2, gfan, polymake, Singular, nauty and Lean, with a provenance-tracking result cache. Destined for its own repository. |
| `formal/` | Lean 4 / Mathlib project: G1 (vector matroid) and G2 (the unique-factorization step of the main theorem), both proved. |
| `experiments/question1/`, `experiments/tropical_flags/` | Track D (Question 1 for full and partial Hessenberg varieties) and Track C (frozen). |
| `PLAN.md` | Development plan built from the audit: tracks, milestones, atomic experiments, kill criteria, artifacts. |
| `docs/lean-formalization-feasibility.md` | Feasibility study for formally verifying the results in Lean 4 / Mathlib, with a tiered target list checked against the current Mathlib tree. |

## Status in one paragraph

The main theorem (local equivariant cohomology `H*_T(X, X∖pt)`, viewed as an ideal of
`H*_T(pt)`, determines the linear matroid of weights with multiplicities, and hence
`S(X)_{⩾pt}`) is sound. v2 gives it a correct general proof: the Thom isomorphism plus unique
factorization. The original's GKM-based proof of the key proposition needed pairwise
independent weights. The advertised corollary, that local weight matroids and hence their Chow
rings and Orlik–Solomon algebras do not determine `H*_T`, was unproved in the original and is
now **Theorem 4.35** of v2. The witness is two connected regular semisimple Hessenberg
varieties in `Fl(C⁵)`, confirmed by exhaustive matroid isomorphism and by two independent
Betti-number computations. All errata are applied in the English v2 (`docs/thesis-v2/`).
Verifying them against the primary sources also showed that the audit itself was wrong in a
few places (see `docs/thesis-v2/CHANGES.md`).
