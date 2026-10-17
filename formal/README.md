# formal — Lean 4 / Mathlib formalization (PLAN.md Track G)

Lean `v4.36.0-rc1`, Mathlib pinned in `lake-manifest.json` (commit `625d8914`, 2026-10-16).

| File | Target | Status |
|---|---|---|
| `Formal/LocalCohomologyIdeal.lean` | **G2** — over a field, `span {∏α} = span {∏β} ↔ Multiset.Rel Associated α β` for linear forms: the local equivariant cohomology ideal determines the weights up to scalars, with multiplicities (thesis v2, Theorem 4.15(2)) | ✅ proved |
| `Formal/VectorMatroid.lean` | **G1** — `vectorMatroid v : Matroid ι`, the linear matroid of a finite family of vectors, with the exchange axiom `linearIndepOn_augment` | ✅ proved |

Both depend only on `propext`, `Classical.choice`, `Quot.sound` (no `sorry`); the engine test
`engine/tests/test_backends.py::test_lean_g2_is_sorry_free` re-checks this.

Setup: `lake exe cache get && lake build`. Check a theorem's axioms:
`echo 'import Formal\n#print axioms MatroidToric.span_prod_eq_iff' > /tmp/a.lean && lake env lean /tmp/a.lean`.
