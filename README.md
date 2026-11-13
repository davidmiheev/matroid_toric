# matroid_toric

Working repository for the paper
**[*Face posets, local weight matroids and Betti numbers of torus actions*](docs/paper/)**
(D. A. Mikheev; draft in `docs/paper/`). The paper grew out of the thesis
*«Инварианты матроидов, определяемых действиями тора»* (Mech-Math MSU, 2022; advisor
V. M. Buchstaber), its audit, and the follow-up program in `PLAN.md`. Everything here — the revised
thesis, the computer experiments, the Lean formalization — exists to support the paper's three
results:

- **Theorem A.** Local equivariant cohomology at a fixed point, as an ideal of `H*_T(pt)`,
  determines the tangent weights with multiplicities, hence the local lattice `S(X)_{⩾pt}`.
- **Theorem B.** Local weight matroids do not determine `H*_T`: a connected pair of regular
  semisimple Hessenberg varieties in `Fl(C⁵)`.
- **Theorem C.** The face poset determines the Betti numbers for isospectral manifolds and all full
  and partial regular semisimple Hessenberg varieties of type A, because `Cl_Γ` determines `Γ`.

Computations run through [mtengine](https://github.com/davidmiheev/mtengine) (submodule at `engine/`).

## Contents

| Path | What it is |
|---|---|
| `docs/paper/` | **The paper** (`paper.tex`, `paper.pdf`, 10 pp.): Theorems A, B, C. Compile with XeLaTeX. `README.md` there lists what is left before submission. |
| `docs/thesis_matroid_invariants_torus_actions.pdf` | The thesis as submitted (20 pp., 18 refs). |
| `audit/matroid_torus_thesis_audit.md` | Checkpoint audit (CP0–CP4): reference pins, mathematical audit, priority fix table, development program. |
| `docs/thesis-v2/` | **Revised English edition** of the thesis (`thesis_en.pdf`, 26 pp.): all errata applied, counterexample proved in §4.5, Question 1 answered for type A in §4.4. `CHANGES.md` logs every change against the audit, including where the audit itself was wrong. |
| `experiments/cluster_permutohedra/` | Homology of cluster-permutohedra behind the corrected Examples 4.29–4.30, and the global-poset comparison for the witness pair. |
| `experiments/counterexample/` | The Track A sweep: scripts, verified witness pairs, and the independent Macaulay2 (GKM) recomputation of their Betti numbers. |
| `engine/` | **mtengine**, the computational engine for the experiments: one interface (Python API, `mte` CLI, MCP server) to Macaulay2, gfan, polymake, Singular, nauty, Lean and Regina, with a provenance-tracking result cache. A git submodule pointing at [davidmiheev/mtengine](https://github.com/davidmiheev/mtengine), a standalone engine for computational experiments in topology and geometry; clone with `--recurse-submodules` or run `git submodule update --init`. |
| `formal/` | Lean 4 / Mathlib project: G1–G7 (vector matroids, the unique-factorization step of Theorem A, the lattice of flats, characteristic polynomial, Philip Hall, fixed subspaces, GKM rings) and the rigidity `Cl_Γ ≅ Cl_Γ' ⇒ Γ ≅ Γ'` behind Theorem C. No `sorry`; see `formal/README.md`. |
| `experiments/question1/`, `experiments/tropical_flags/` | Track D: Question 1 for full and partial Hessenberg varieties, proved in `question1/PROOF.md` and checked by computer for n ≤ 7. Track C is frozen. |
| `PLAN.md` | Development plan built from the audit: a status table for every track, then tracks, milestones, atomic experiments, kill criteria, artifacts. |
| `docs/lean-formalization-feasibility.md` | Feasibility study for formally verifying the results in Lean 4 / Mathlib, with a tiered target list checked against the current Mathlib tree. |

## Setup

```sh
git submodule update --init engine                       # mtengine
(cd engine && python3 -m venv .venv && .venv/bin/pip install -e ".[test]")
(cd formal && lake exe cache get && lake build)          # prebuilt Mathlib, then the project
```

The `mtengine` MCP server in `.mcp.json` runs from `engine/.venv`. Its Lean backend
(`lean_check`) compiles in `formal/`, which it finds as the sibling of `engine/`; an mtengine
installed elsewhere needs `export MTENGINE_LEAN_PROJECT=$PWD/formal`. In Claude Code cloud
sessions, `.claude/hooks/session-start.sh` does all of this and sets that variable. The
toolchain is pinned in `formal/lean-toolchain` (Lean 4.36.0-rc1, Mathlib `625d8914`).

## Status in one paragraph

The main theorem (local equivariant cohomology `H*_T(X, X∖pt)`, viewed as an ideal of
`H*_T(pt)`, determines the linear matroid of weights with multiplicities, and hence
`S(X)_{⩾pt}`) is sound. v2 gives it a correct general proof: the Thom isomorphism plus unique
factorization. The original's GKM-based proof of the key proposition needed pairwise
independent weights. The advertised corollary, that local weight matroids and hence their Chow
rings and Orlik–Solomon algebras do not determine `H*_T`, was unproved in the original and is
now **Theorem 4.45** of v2. The witness is two connected regular semisimple Hessenberg
varieties in `Fl(C⁵)`, confirmed by exhaustive matroid isomorphism and by two independent
Betti-number computations. All errata are applied in the English v2 (`docs/thesis-v2/`).
Verifying them against the primary sources also showed that the audit itself was wrong in a
few places (see `docs/thesis-v2/CHANGES.md`).

The thesis's Question 1 asks whether the face poset determines the Betti numbers. It now has a
positive answer for isospectral manifolds and for all full and partial regular semisimple
Hessenberg varieties. The reason is rigidity: the cluster-permutohedron `Cl_Γ` determines the
graph `Γ`: the poset sees which edges meet and which form triangles, and that determines the
graph by an elementary star argument (v2 Theorems 4.35 and 4.38).
