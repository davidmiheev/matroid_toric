# Track D results: Question 1 on regular semisimple Hessenberg varieties

**Question 1 (thesis v2, §4.4):** for torus manifolds with `H^odd = 0`, does `S(X₁) ≅ S(X₂)`
imply equal Betti numbers?

**Result: yes, within this family, for all n ≤ 7 (714 Hessenberg functions).** In this family
the face poset determines the graph `Γ_h` up to isomorphism, and the graph determines the
Betti numbers.

## Setup

Regular semisimple Hessenberg varieties all have `H^odd = 0`, and
`S(Hess(M,h)) ≅ Cl(Γ_h)` (v2 Example 4.26, via the twin argument of Ayzenberg–Buchstaber).
So Question 1 in this family asks whether `Cl(Γ_{h₁}) ≅ Cl(Γ_{h₂})` forces
`P_{h₁} = P_{h₂}`, where `P_h = Σ_w q^{2ℓ_h(w)}`.

## Method (`hessenberg_q1.py` → `hessenberg_q1.log`)

- **(a)** Group the `h` by the isomorphism class of `Γ_h` (canonical form by brute force
  over relabellings), and check that Betti numbers agree within each class.
- **(b)** Group the `h` by an invariant of `Cl(Γ_h)`, and look for classes that contain
  non-isomorphic graphs. The invariant is the multiset, per rank, of (lower-cover count,
  upper-cover count). It is computed on the lattice of flats: over a clustering `C` there are
  `n!/∏|Vᵢ|!` elements, each with `Σ_{C′⋖C} ∏|Vᵢ|!/∏|V′ⱼ|!` lower covers and
  `#{C″ ⋗ C}` upper covers, independently of the assignment. For n = 4, 5 this closed form
  was cross-checked against a direct computation on the full poset: identical classes.

| n | Hessenberg functions | graph classes | Cl-invariant classes | (a) violations | (b) candidates |
|---|---|---|---|---|---|
| 4 | 14 | 9 | 9 | 0 | 0 |
| 5 | 42 | 21 | 21 | 0 | 0 |
| 6 | 132 | 55 | 55 | 0 | 0 |
| 7 | 429 | 151 | 151 | 0 | 0 |

## Why this is a rigorous statement, not just an absence of evidence

Different invariants mean non-isomorphic posets. By (b), non-isomorphic graphs always give
different invariants. So in this family `Cl(Γ_{h₁}) ≅ Cl(Γ_{h₂})` implies
`Γ_{h₁} ≅ Γ_{h₂}`, and by (a) that implies equal Betti numbers. The one input taken from
the literature is `S(Hess) ≅ Cl(Γ_h)`.

## What this means for Question 1

The Hessenberg family is too rigid to produce a counterexample. The face poset remembers
the whole graph, and for indifference graphs the graph determines the Betti numbers: a
connected unit interval graph has a natural labelling that is unique up to reversal, and
reversal preserves `P_h`. Twins (Ayzenberg–Buchstaber) are no help either, since they have
equal face posets *and* equal Betti numbers.

A counterexample, if one exists, has to come from families where the face poset forgets
more than the graph:
1. **Partial Hessenberg varieties**, including `Gr(2,4)` (complexity one), with face posets
   `Flats(Γ_h(k̄)) ×_Λ ([n] choose k̄)` ([AB24] Thm 2). Here different pairs
   `(Γ, k̄)` could give isomorphic posets. This is the next experiment; it needs the
   symmetric identification poset implemented from [AB24, Constr. 5.1, 5.11].
2. **GKM manifolds beyond type A**, such as Hessenberg varieties in other Lie types.
