# Track D results: Question 1 on regular semisimple Hessenberg varieties

**Question 1 (thesis v2, §4.4):** for torus manifolds with `H^odd = 0`, does `S(X₁) ≅ S(X₂)`
imply equal Betti numbers?

> **Update: now proved for all n** (`PROOF.md`; thesis v2, Theorems 4.35 and 4.38). The
> computations below came first and motivated the proof. They remain as independent evidence.

**Result: yes, within this family, for all n ≤ 7 (714 Hessenberg functions).** Partial
Hessenberg varieties are treated in the second half of this file. In this family
the face poset determines the graph `Γ_h` up to isomorphism, and the graph determines the
Betti numbers.

## Setup

Regular semisimple Hessenberg varieties all have `H^odd = 0`, and
`S(Hess(M,h)) ≅ Cl(Γ_h)` (v2 Example 4.27, via the twin argument of Ayzenberg–Buchstaber).
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

## What the full family can and cannot tell us

The Hessenberg family is too rigid to produce a counterexample. The face poset remembers
the whole graph, and for indifference graphs the graph determines the Betti numbers: a
connected unit interval graph has a natural labelling that is unique up to reversal, and
reversal preserves `P_h`. Twins (Ayzenberg–Buchstaber) are no help either, since they have
equal face posets *and* equal Betti numbers.

## Partial Hessenberg varieties (`partial_hessenberg.py`, `partial_q1.py`)

**Result: yes again, for all n ≤ 7 (2,940 cases: every composition `k̄` with at least two parts
and every Hessenberg function `h` on its parts).** This family includes the Grassmannians
`Gr(2,4)` (complexity one), `Gr(2,5)`, `Gr(3,6)`, all partial flag varieties, and the full
Hessenberg varieties as the case `k̄ = (1,…,1)`.

| n | cases | invariant classes | classes with differing Betti numbers |
|---|---|---|---|
| 3 | 9 | 6 | 0 |
| 4 | 35 | 19 | 0 |
| 5 | 136 | 54 | 0 |
| 6 | 542 | 175 | 0 |
| 7 | 2,218 | 577 | 0 |

This family is genuinely less rigid than the full one: at n = 6, 542 cases share only 175
invariant classes, so many different `(k̄, h)` cannot be told apart by the invariant. Yet the
Betti numbers agree inside every class. Since isomorphic posets have equal invariants, the
statement "`S(X₁) ≅ S(X₂)` ⇒ equal Betti numbers" holds for all pairs in this family with n ≤ 7.

n ≤ 6 comes from `partial_q1.py` (`partial_q1.log`). n = 7 comes from `partial_q1_resumable.py`
(`partial_q1_n7.jsonl`, one line per case, and `partial_q1_n7_run.log`), which checkpoints every
case, runs in parallel and computes the invariant once per mirror pair
`(k̄, h) ↔ (k̄ reversed, h*)`. That symmetry is verified on all cases with n ≤ 5 at the start of
each run. The run survived a container restart by resuming from its checkpoint (1,764 of
2,218 cases were already done). It reproduces the n = 6 row exactly. `partial_q1_n7.log` is
the earlier, non-resumable attempt, which was lost to a container reset after n = 6.

### How the face poset is computed

Ayzenberg–Buchstaber (IMRN 2024, Thm 2) write the face poset as a symmetric identification
poset, `Flats(Γ_h(k̄)) ×_Λ ([n] choose k̄)`. Applying that formula literally is easy to get
wrong: two readings of how `Σ_C` acts gave 16 and 4 rank-1 faces for `Gr(2,4)`, which has 12.
The proof of their theorem shows that a face `X_(C,κ)` depends only on the set partition
`{σ(V_j)}` of the coordinates and on the part-counts `k_i(V_j)` of each block. So faces are
implemented as **(set partition of [n], admissible part-count vector per block)**. A block is
admissible when its induced subgraph in the inflated graph is connected.

### Validation (`validate_partial.py` → `validate_partial.log`, and `engine/tests`)

- `Gr(2,4)`: faces (6, 12, 11, 1), where 12 is the number of edges of its GKM graph, the
  octahedron; Betti numbers (1, 1, 2, 1, 1). `Gr(2,5)`: the Gaussian binomial.
- Full case `k̄ = (1,…,1)`, every `h` for n = 3, 4, 5: reproduces `Cl(Γ_h)` and the De Mari–
  Procesi–Shayman Betti numbers.
- Local posets: at every fixed point, in five partial cases, the faces above it form the
  lattice of flats of the inflated graph, as [AB24, Thm 2] requires.
- Cover counts from the split/merge formulas agree with brute force on the order relation.
- **The Betti formula itself** (the Białynicki-Birula count) agrees with an independent
  Macaulay2 computation of the GKM ring for `Gr(2,4)`, `k̄ = (1,2,2)`, the partial flag variety
  `Fl_(2,1,2)` and the permutohedral variety (`engine/tests/test_backends.py`).

## What this means for Question 1

Both natural families of type A, full and partial Hessenberg, answer "yes" for every case
computed. A counterexample, if one exists, has to come from elsewhere: GKM manifolds
outside type A, such as Hessenberg varieties in other Lie types, or non-algebraic torus
manifolds. Since the cover invariant never separated two cases with different Betti
numbers, it is also worth asking whether it is the Betti numbers that the face poset
determines, via an h-vector-like formula, which would be a theorem rather than a search.
