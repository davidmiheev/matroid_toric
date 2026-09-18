# matroid_toric

Working repository for the thesis *«Инварианты матроидов, определяемых действиями тора»*
(D. A. Mikheev, Mech-Math MSU, 2022; advisor V. M. Buchstaber) and for the follow-up
program derived from its audit.

## Contents

| Path | What it is |
|---|---|
| `docs/thesis_matroid_invariants_torus_actions.pdf` | The thesis as submitted (20 pp., 18 refs). |
| `audit/matroid_torus_thesis_audit.md` | Checkpoint audit (CP0–CP4): reference pins, mathematical audit, priority fix table, development program. |
| `PLAN.md` | Development plan built from the audit: tracks, milestones, atomic experiments, kill criteria, artifacts. |
| `docs/lean-formalization-feasibility.md` | Feasibility study for formally verifying the results in Lean 4 / Mathlib, with a tiered target list checked against the current Mathlib tree. |

## Status in one paragraph

The main theorem (Теорема 1 = 5 = 8: local equivariant cohomology `H*_T(X, X∖pt)` determines
the linear matroid of weights `S(X)_{⩾pt}`) is sound; its proof is the slice theorem plus
excision plus a GKM computation for the compactified tangent representation, and it agrees
with Ayzenberg–Cherepanov (arXiv:2203.06282). The advertised *corollary* — that equivariant
cohomology is not determined by the Chow ring and the Orlik–Solomon algebra of the local
weight matroid — is asserted in the abstract but never proved in the body. Closing that gap
is item A in `PLAN.md`, and `PLAN.md` carries a concrete candidate witness pair to verify.
Several background statements (Определения 18, 19, Предложение 3, the Boolean expansion of
the characteristic polynomial, Теорема 2) are wrong as written and have explicit repairs.
