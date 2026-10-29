# formal — Lean 4 / Mathlib formalization (PLAN.md Track G)

Lean `v4.36.0-rc1`, Mathlib pinned in `lake-manifest.json` (commit `625d8914`, 2026-10-16).

| File | Target | Status |
|---|---|---|
| `Formal/LocalCohomologyIdeal.lean` | **G2** — over a field, `span {∏α} = span {∏β} ↔ Multiset.Rel Associated α β` for linear forms: the local equivariant cohomology ideal determines the weights up to scalars, with multiplicities (thesis v2, Theorem 4.15(2)) | ✅ proved |
| `Formal/VectorMatroid.lean` | **G1** — `vectorMatroid v : Matroid ι`, the linear matroid of a finite family of vectors, with the exchange axiom `linearIndepOn_augment` | ✅ proved |
| `Formal/FlatLattice.lean` | **G3** — `Flats M`, the complete lattice of flats of any matroid: meet = `∩`, join = closure of `∪`, `sSup`/`sInf`, `⊥` = loops, `⊤` = ground set; submodular rank; `F ⋖ G ↔ G = cl(insert e F)`; covers raise rank by 1; `IsUpperModularLattice` and `IsAtomistic` instances | ✅ proved |
| `Formal/CharPoly.lean` | **G4** — `charPoly M = ∑_F μ(⊥,F) X^{r(E)−r(F)}` via Mathlib's `IncidenceAlgebra.mu` on `Flats M`; `sum_closure_eq_mu` (signed count of spanning sets of a flat = `μ(⊥,F)`, loopless) and **Whitney's Boolean expansion** `charPoly_eq_sum_subsets` (`χ_M = ∑_{A⊆E} (−1)^{|A|} X^{r(E)−r(A)}`, loopless, finite type) | ✅ proved |
| `Formal/PhilipHall.lean` | **G5** — Philip Hall's theorem, combinatorial form: for `a < b` in any locally finite partial order, `mu ℤ a b = redEulerChar a b`, the reduced Euler characteristic `∑_C (−1)^{|C|+1}` over the chains `C` of the open interval `(a, b)` (empty chain included); `Flats.mu_bot_top_eq_redEulerChar` for the lattice of flats (corrected thesis Предложение 3, sign included) | ✅ proved |
| `Formal/GKM.lean` | **G7** — GKM rings as a definition: `LabelledGraph` (multigraphs with edge labels), `gkmRing` (the subalgebra of graph functions), `sphere α` (the GKM graph of `S^{2n}`). `mem_iInf_iff_exists_gkm`: the relative part restricts to `⋂ⱼ (αⱼ)`; `iInf_span_eq_span_prod`: for pairwise non-associated linear forms, `⋂ⱼ (αⱼ) = (∏ⱼ αⱼ)` (thesis Prop. 4.12, GKM case); `gkm_relative_determines_weights` (with G2); `iInf_span_ne_span_prod_of_repeated`: for weights `(X₀, X₀)` the GKM model gives `(X₀) ≠ (X₀²)`. The GKM theorem itself (ring = `H*_T`) is **not** formalized | ✅ proved |

Both depend only on `propext`, `Classical.choice`, `Quot.sound` (no `sorry`); the engine test
`engine/tests/test_backends.py::test_lean_g2_is_sorry_free` re-checks this.

Setup: `lake exe cache get && lake build`. Check a theorem's axioms:
`echo 'import Formal\n#print axioms MatroidToric.span_prod_eq_iff' > /tmp/a.lean && lake env lean /tmp/a.lean`.
