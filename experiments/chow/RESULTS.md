# Track F — Chow rings, augmented Chow rings and intersection cohomology: results

Script: `track_f.py` (log: `track_f.log`), using mtengine's `chow_ring`, `kazhdan_lusztig`,
`orlik_solomon`. Run: `../../engine/.venv/bin/python track_f.py`.

## 1. The local matroid of the Track A pair

`X₁ = Hess(2,3,5,5,5)` and `X₂ = Hess(2,4,4,5,5)` have the same local matroid
`U_{2,3} ⊕ U_{1,1} ⊕ U_{1,1}` (rank 4, flats by rank `1, 5, 8, 5, 1`) at every fixed point, so every
matroid invariant agrees. Computed for both, from the two different graphs:

| Invariant | Value | How |
|---|---|---|
| Chow ring `A(M)` | `1, 14, 14, 1` | Macaulay2, AHK presentation; equals the Feichtner–Yuzvinsky basis count |
| augmented Chow ring | `1, 19, 44, 19, 1` | Macaulay2, BHMPW presentation; equals the basis count |
| Kazhdan–Lusztig polynomial | `1` | recursion on the lattice of flats |
| `IH(M)` (Z-polynomial) | `1, 5, 8, 5, 1` | the same |
| Orlik–Solomon algebra | `1, 5, 9, 7, 2` | Macaulay2 |
| Betti numbers of `X₁`, `X₂` | `1,17,42,42,17,1` and `1,12,47,47,12,1` | — |

So Theorem B extends verbatim from `A(M)` and `OS(M)` to the augmented Chow ring, `IH(M)` and the
Kazhdan–Lusztig polynomial: none of them, taken at all fixed points, determines `H*_T(X)`. (This
is immediate from the matroids being isomorphic; the computation is the check.)

## 2. The gluing test: kill criterion met

The plan asks whether the face poset glues the local rings into something of the size of
`H*(X)`, with the kill criterion "the dimension count already fails for `CP²`". The count
tested: `Σ_σ (−1)^{rk σ} f(M_σ)` over the faces `σ`, for `f` the total dimension of each ring and
`M_σ` either the matroid of the weights tangent to `σ` (restriction) or normal to it
(contraction). The target is the number of fixed points.

| `f` | matroid | `CP²` | `CP³` | `Fl(C³)` | `X₁` | `X₂` |
|---|---|---|---|---|---|---|
| **target** | | **3** | **4** | **6** | **120** | **120** |
| 1 | either | 1 | 1 | −2 | −14 | −24 |
| `dim A` | restriction / contraction | 2 / 4 | 0 / 15 | −1 / 4 | 25 / 2046 | 10 / 2026 |
| `dim` augmented `A` | restriction / contraction | 2 / 10 | −4 / 41 | −6 / 19 | 4 / 5751 | −26 / 5711 |
| `dim IH` | restriction / contraction | 1 / 7 | 0 / 15 | −7 / 13 | 50 / 511 | 20 / 481 |
| `P_KL(1)` | either | 1 | 1 | −2 | −14 | −24 |
| `dim OS` | restriction / contraction | 1 / 7 | 0 / 15 | −6 / 19 | 44 / 771 | 24 / 751 |

No candidate gives 3 for `CP²`. **The kill criterion is met: the track is frozen in this form.**
(The row `f = 1` is the Euler characteristic of the orbit space, which is why it is 1 for `CPⁿ`.)

## 3. What does decompose over the face poset

There is exactly one way to write the Poincaré polynomial as a sum over faces with the toric
weight `(q − 1)^{rk}`: define `e_σ(q)` recursively by

    P_σ(q) = Σ_{τ ⩽ σ} (q − 1)^{rk τ} e_τ(q)      for every face σ,

where `P_σ` is the Poincaré polynomial of the face submanifold. Geometrically `e_σ` is the
E-polynomial of the quotient of the open stratum of `σ` by the complex torus. For a toric variety
`e ≡ 1` and the formula is the `h`-vector formula. Computed for Hessenberg varieties, where a face
is a product over the blocks of a clustering and `e` is multiplicative:

| Graph | `e` |
|---|---|
| tree (free matroid) | `1` |
| `K₃` (`Fl(C³)`) | `q + 4` |
| `K₄` | `q³ + 6q² + 20q + 33` |
| `K₅` | `q⁶ + 8q⁵ + 35q⁴ + 111q³ + 260q² + 453q + 456` |
| Track A: `X₁` and `X₂` (top face) | `q + 6` for **both** |

Two observations.

- **The top stratum does not distinguish the Track A pair.** `e_top = q + 6` for both; the whole
  difference between `(1,17,42,…)` and `(1,12,47,…)` comes from the numbers `ν` of fixed points on
  the lower faces, i.e. from how the same local lattices are glued. This is the precise sense in
  which the local matroid misses the cohomology.
- **`e` is nearly, but not, a matroid invariant.** Among the 64 connected Hessenberg functions with
  `n ⩽ 6` (37 Tutte classes) `e` is constant on 34 classes and differs on 3, each time only in the
  constant term: e.g. `h = (2,3,5,6,6,6)` gives `q² + 8q + 28` and `h = (2,4,5,5,6,6)` gives
  `q² + 8q + 33`, for 2-isomorphic graphs (two triangles sharing an edge plus two more edges).

## 4. A closed formula for `e_σ` (the answer to "compute `e_σ`")

Script: `stratum_formula.py` (log `stratum_formula.log`).

**Theorem.** Let a torus act with isolated fixed points on `X`, and let `ξ` be a generic
one-parameter subgroup such that `P_X(q) = Σ_p q^{ind(p)}`, `ind(p)` the number of weights at `p`
negative on `ξ` (Białynicki-Birula; Morse theory of a moment map), and the same for every face
submanifold. For a face `σ` and a fixed point `p ∈ σ` let `N_p(σ)` be the set of weights of `σ` at
`p` that are negative on `ξ`. Then

    P_X(q) = Σ_σ (q − 1)^{rk σ} e_σ(q),
    e_σ(q) = Σ_{p ∈ σ^T, N_p(σ) spans the weights of σ}  T_{M(N_p(σ))}(1, q),

where `T_M(x, y)` is the Tutte polynomial of the linear matroid of the vectors `N_p(σ)`. The
polynomials `e_σ` are the ones defined by the recursion of §3; in particular they do not depend on
`ξ`, although the individual summands do.

*Proof.* `q^{ind(p)} = Σ_{S ⊂ N_p} (q − 1)^{|S|}`, the sum over all subsets of the set `N_p` of
negative weights at `p`. Group the subsets `S` by the flat `F` they span in the matroid of weights
at `p`; the pair `(p, F)` is the same thing as a face `σ` together with a fixed point `p` of it, and
`S` runs over the subsets of `N_p(σ) = N_p ∩ F` that span `F`. So
`P_X = Σ_σ (q − 1)^{rk σ} Σ_{p ∈ σ^T} Σ_S (q − 1)^{|S| − rk σ}`, and
`Σ_{S ⊂ N spanning} (y − 1)^{|S| − r} = T_{M(N)}(1, y)` when `N` has rank `r`, and is empty
otherwise. Applying the same computation to a face `τ`, whose fixed points, weights and faces are
those of `X` inside `τ`, gives `P_τ = Σ_{σ ⩽ τ} (q − 1)^{rk σ} e_σ` with the same `e_σ`, which is
the recursion of §3. ∎

Consequences.

- **Toric case.** If the weights of `σ` at `p` are independent, `N_p(σ)` spans only when all of them
  are negative, which happens at exactly one fixed point of `σ` (its sink), and `T = 1`. So
  `e_σ = 1` and the formula is `h(q) = Σ_σ (q − 1)^{dim σ}`.
- **`Fl(C³)`.** The top face: the two permutations with two inversions contribute `T(1, q) = 1`
  each, the longest element contributes `T_{U_{2,3}}(1, q) = q + 2`; total `q + 4`.
- **Positivity.** `e_σ` has nonnegative coefficients, and `e_σ(1) = Σ_p #{bases of M(N_p(σ))}`.
- **Hessenberg varieties, graph form.** For a connected Hessenberg graph `G` on `[n]`,
  `e_G(q) = Σ_S (q − 1)^{|S| − n + 1} L(S)` over the connected spanning edge sets `S`, where `L(S)` is
  the number of `w ∈ S_n` with `w(i) > w(j)` for every edge `i < j` of `S` (linear extensions).
  With `L ≡ 1` this would be `T_G(1, q)`, a matroid invariant. That is why `e` is constant on most
  Tutte classes, and why it is not a matroid invariant in general.
- **What it uses.** The face poset (the faces and their fixed points), the local matroids (the
  Tutte polynomials) and the signs of the weights against one `ξ` (the sets `N_p`). The third
  ingredient is exactly the oriented datum singled out in Track E: the oriented matroid at each
  fixed point together with the tope of a common `ξ`. So the formula is not a function of `S(X)`
  alone; it says precisely which extra structure turns the face poset into Betti numbers.

Checked: against the recursion for all 22 connected Hessenberg functions with `n ⩽ 5`; the identity
for `P_X` on `Fl(C³)`, `Fl(C⁴)`, `Gr(2,4)`, both Track A varieties and `CP³` with a 2-torus;
independence of `ξ` on `X₁`.

## Status

- Atomic experiment: done. Kill criterion: met (§2). Frozen as "glue Chow-type rings".
- The surviving question, to compute `e_σ`, is answered by the theorem of §4: `e_σ` is a sum of Tutte
  polynomials `T(1, q)` of the negative parts of the local matroids. What remains open is whether
  `e_σ` can be computed from `S(X)` without the signs.
- Engine: `chow_ring` (plain and augmented, Macaulay2 against the FY basis) and `kazhdan_lusztig`
  (KL polynomial and Z-polynomial), tested against the published values for uniform and braid
  matroids.
