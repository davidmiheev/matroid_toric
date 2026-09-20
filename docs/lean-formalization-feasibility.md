# Feasibility: formal verification in Lean 4 / Mathlib

**Question.** Can the results of the thesis — and the repairs listed in `PLAN.md` Track B — be
formally verified in Lean 4 against Mathlib?

**Short answer.** The combinatorial and commutative-algebra layers: yes, and one of them is a
genuinely attractive target. The equivariant-topology layer: no, and not in the foreseeable
future — the prerequisites (equivariant cohomology, the Borel construction, excision for a
pair, equivariant Euler classes, the slice theorem) do not exist in Mathlib, and singular
homology itself landed only recently and in embryonic form.

Everything below was checked against the Mathlib tree on `master` (survey date 2026-09-18) by
reading `Mathlib.lean` and the relevant files, not from memory.

---

## 1. What Mathlib has today

| Needed for | Status | Where |
|---|---|---|
| Matroids (ground set, independence, bases, circuits, closure, flats, duality, minors, rank) | **Present and mature** | `Mathlib/Combinatorics/Matroid/{Basic,Circuit,Closure,Dual,IndepAxioms,Loop,Map,Sum,Constructions}.lean`, `Matroid/Minor/*`, `Matroid/Rank/{Cardinal,ENat,Finite}.lean` |
| Möbius function of a locally finite poset, Möbius inversion | **Present** | `Mathlib/Combinatorics/Enumerative/IncidenceAlgebra.lean` (`zeta`, `mu`, `mu_mul_zeta`, `zeta_mul_mu`) |
| Unique factorization in `k[t₁,…,t_k]` | **Present** | `MvPolynomial.uniqueFactorizationMonoid` in `Mathlib/RingTheory/Polynomial/UniqueFactorization.lean`; `Mathlib/RingTheory/UniqueFactorizationDomain/*` |
| Simplicial complexes (abstract and geometric) | Present, thin | `Mathlib/AlgebraicTopology/SimplicialComplex/Basic.lean`, `Mathlib/Analysis/Convex/SimplicialComplex/*` |
| Tropical semiring | Present, algebra only | `Mathlib/Algebra/Tropical/{Basic,BigOperators,Lattice}.lean` |
| Linear (vector) matroid — the matroid of a family of vectors | **Absent** | — |
| Lattice-of-flats as a lattice object; geometric lattices | **Absent** | `Matroid.IsFlat` exists as a predicate; no `Lattice` instance on flats, no `GeometricLattice` |
| Characteristic polynomial of a matroid; Whitney's expansion | **Absent** | — |
| Order complex of a poset; shellability; Philip Hall's theorem | **Absent** | — |
| Chow ring of a matroid; Orlik–Solomon algebra; Bergman fan; toric varieties | **Absent** | no `Chow`/`Toric`/`Orlik`/`Arrangement` modules exist |
| Singular **co**homology, cup product, cohomology of a pair, excision | **Absent** | singular *homology* exists only as `SingularHomology/{Basic,HomologyZero,HomotopyInvariance,HomotopyInvarianceTopCat}.lean`: the chain-complex functor, `H₀`, homotopy invariance. No LES of a pair, no excision, no cohomology, no ring structure |
| Classifying spaces `BG`, Borel construction `EG ×_G X`, equivariant cohomology | **Absent** | no `ClassifyingSpace`/`Equivariant` topology modules; `RepresentationTheory/Homological/GroupCohomology/*` is algebraic group cohomology, which is a different object |
| Euler class, equivariant Euler class, Serre spectral sequence of a fibration | **Absent** | — |
| Slice theorem for compact transformation groups | **Absent** | — |

## 2. Tiered target list

### Tier 1 — feasible now (weeks, by one person familiar with Mathlib)

**T1.1 — The unique-factorization step of Теорема 5.** This is the mathematical heart of the
main theorem once the topology has produced the ideal, and it is exactly the step the thesis
states loosely (`PLAN.md` Track B item 8). Statement: over a field `k`, for nonzero linear
forms `α_j`, the principal ideal `(∏_j α_j) ⊆ MvPolynomial (Fin k) k` determines the multiset
`{α_j}` up to units — hence determines the linear matroid of the `α_j` *including*
multiplicities.

```lean
-- sketch, not compiled
open MvPolynomial in
theorem span_prod_eq_iff_factors_eq {k : Type*} [Field k] {σ : Type*} [Fintype σ]
    (α β : Multiset (MvPolynomial σ k))
    (hα : ∀ p ∈ α, p.totalDegree = 1) (hβ : ∀ p ∈ β, p.totalDegree = 1) :
    Ideal.span {α.prod} = Ideal.span {β.prod} ↔
      ∃ u : Multiset.Rel (Associated) α β, True := by
  sorry
```

Ingredients, all present: `MvPolynomial.uniqueFactorizationMonoid`,
`UniqueFactorizationMonoid.factors_unique`, `Ideal.span_singleton_eq_span_singleton`
(`↔ Associated`). The one lemma to prove from scratch is that a nonzero form of total degree 1
is irreducible in `MvPolynomial σ k` — a short degree argument. Estimated 200–400 lines.
Deliverable value: it converts the vaguest sentence in the thesis («задаёт алгебраическое
многообразие… двойственным является набор весов») into a machine-checked statement, and it is
the step where the multiplicity information is actually won or lost.

**T1.2 — The linear matroid of a family of vectors.** Build `Matroid.ofVectors : (ι → V) →
Matroid ι` from `LinearIndepOn`, via `IndepMatroid.ofFinitary` / the augmentation axiom in
`Matroid/IndepAxioms.lean`. This is a known-absent, self-contained, Mathlib-worthy
contribution, and it is the object the thesis's Определение 19 (once repaired: rank-`r`
matroids realize in dimension `r`, with the biconditional quantified over all `S ⊆ E`) is
about. Estimated 300–600 lines. Upstreamable.

**T1.3 — Whitney's Boolean expansion of the characteristic polynomial** (`PLAN.md` Track B
item 5, the repair of the thesis's ill-formed expansion). Needs: a `Lattice`/`Fintype`
structure on flats so that `IncidenceAlgebra.mu` applies, the definition
`χ_M(t) = Σ_{F ∈ ℒ_M} µ(0̂,F) t^{r(E)−r(F)}`, and then the identity
`χ_M(t) = Σ_{A ⊆ E} (−1)^{|A|} t^{r(E)−r(A)}` for loopless `M` by Möbius inversion over the
closure map. The lattice-of-flats instance is the real work and is itself upstreamable.
Estimated 600–1200 lines including the flats lattice.

### Tier 2 — feasible but a project (months)

**T2.1 — Geometric lattices and `ℒ_M` is one.** Define `GeometricLattice` (graded, atomistic,
semimodular), instantiate it on the flats of a finite matroid. Prerequisite for anything about
Теорема 7. Mathlib has `Order/Atoms`, `IsModularLattice`, and grading machinery, so this is
assembly rather than invention.

**T2.2 — The combinatorial core of Теорема 7 (Ayzenberg–Cherepanov).** *Given* the slice
theorem as a hypothesis, the content is a poset isomorphism: for a family of weights
`α : ι → Qᵏ`, the poset of subspaces `{ V^H : H ⊆ T closed }` ordered by inclusion is
isomorphic to `ℒ_α` via orthogonal complement. Stated purely linear-algebraically — subgroups
replaced by subspaces of the character lattice — this is formalizable and is the honest way to
verify the thesis's Теорема 7 proof, whose geometric input is entirely in the slice theorem.

**T2.3 — Philip Hall / the corrected Предложение 3.** Two routes. (a) The *purely
combinatorial* Hall theorem — `µ(0̂,1̂) = Σ_i (−1)^i c_i`, where `c_i` counts chains of length
`i` in `ℒ∖{0̂,1̂}` — is a Möbius-algebra statement and is formalizable today; it gives the
corrected identity `χ̃ = µ(0̂,1̂)` **as a definition of `χ̃` by the chain count**, which is
exactly what the repaired Предложение 3 needs. (b) The *topological* reading (the order complex
is a wedge of `|µ|` spheres of dimension `r−2`) needs shellability and homology of simplicial
complexes and belongs to Tier 3. Route (a) is the right target and is a clean, self-contained
formalization.

### Tier 3 — blocked on missing foundations (not a matter of effort)

Теорема 1/5/8 as stated, Предложение 5, Лемма 1 (Chang–Skjelbred), the GKM theorem, Предложение
4 (equivariant formality), and the whole of Track A's witness are blocked. To formalize
Теорема 5 one needs, in order: singular cohomology with its ring structure; relative cohomology
and the long exact sequence of a pair; excision; the Borel construction and `H*_T` as a module
over `H*(BT)`; equivariant Euler classes of `T`-vector bundles; and Bredon's slice theorem.
Mathlib currently has the singular *chain complex* functor, `H₀`, and homotopy invariance.
Realistically that is a multi-year, multi-person foundational program, comparable in scale to
the Liquid Tensor Experiment, and it is not sensible to attach it to this thesis.

A partial escape exists and is worth stating explicitly: **the GKM presentation can be taken as
the definition.** If one *defines* `H*_T(X)` for a GKM manifold to be the ring of graph
functions `{ (f_p) ∈ ⊕_p Sym(t*) : f_p − f_q ∈ (α_pq) }` (Теорема 4), then everything
downstream — Предложение 5, Теорема 5's algebra, and the Track A Betti-number computation —
becomes finite commutative algebra over `MvPolynomial`, and is formalizable at Tier 1/2 cost.
What is *not* then verified is that this ring is the equivariant cohomology of a manifold; the
GKM theorem becomes an axiom. For a thesis whose content is the combinatorics downstream of
GKM, this is an honest and useful boundary — but it must be labelled as such.

## 3. Recommendation

1. Do **T1.1** first. It is small, it is the actual gap in the thesis's own exposition, and it
   formally verifies the statement that the local equivariant cohomology ideal remembers the
   weight multiset — the substance of Теорема 5 minus the topology.
2. Do **T1.2** next and upstream it. The linear matroid of a family of vectors is missing from
   Mathlib, is needed by every other item here, and is useful far beyond this thesis.
3. Treat **T1.3 / T2.1 / T2.3(a)** as the natural continuation: they formalize the repaired
   background section (Track B items 4, 5, 7) rather than the main theorem, which is the honest
   place for formal verification to add value here.
4. Do **not** attempt Tier 3. If the GKM-as-definition route is taken, say in the write-up that
   the GKM theorem is assumed, not verified.

**Practical setup.** Lean 4 + Mathlib pinned to a fixed commit in `lakefile.lean` (the `Matroid`
API is under active development and has moved recently); work in a `lean/` subdirectory of this
repository with `lake exe cache get` in CI; state each target as a `theorem … := by sorry`
skeleton first so that the statement can be reviewed independently of the proof.

---

## Mapping to `PLAN.md` Track G

`PLAN.md` carries the scheduled, actionable version of this list; this file is the Mathlib
survey it rests on. The identifiers correspond as follows.

| Here | `PLAN.md` | Item |
|---|---|---|
| T1.1 | **G2** (+ **G2a**) | Unique-factorization step of Теорема 5 |
| T1.2 | **G1** | Linear matroid of a family of vectors |
| T1.3 | **G4** | Characteristic polynomial, Whitney's expansion |
| T2.1 | **G3** | Lattice of flats, geometric lattices |
| T2.2 | **G6** | Combinatorial core of Теорема 7 |
| T2.3(a) | **G5** | Philip Hall, combinatorial form |
| GKM-as-definition escape (§2, Tier 3) | **G7** | `gkmRing`, Предложение 5 |
| — | **G8** | The Track A counterexample in Lean (stretch; expressible, not provable) |
| Tier 3 | out of scope | Теорема 1/5/8 as stated, Лемма 1, GKM theorem, Предложение 4 |

If one file is edited, edit the other: the survey moves when Mathlib moves, the plan moves when
priorities move.
