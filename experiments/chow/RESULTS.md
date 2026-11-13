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

## Status

- Atomic experiment: done. Kill criterion: met (§2). Frozen as "glue Chow-type rings".
- What survives is a question rather than a construction: **compute `e_σ` from the face poset.**
  That is open question (2) of the paper (a formula for the Betti numbers), in the form
  `P_X = Σ_σ (q − 1)^{rk σ} e_σ`; the data above (all coefficients of `e` except the constant term
  agree on Tutte classes for `n ⩽ 6`) suggest looking for `e_σ` as a matroid invariant of the
  face plus a correction counted by `ν`.
- Engine: `chow_ring` (plain and augmented, Macaulay2 against the FY basis) and `kazhdan_lusztig`
  (KL polynomial and Z-polynomial), tested against the published values for uniform and braid
  matroids.
