# Track A results

Run: `python3 sweep.py` (enumerate + bucket + compare) and `python3 verify_pairs.py`
(exhaustive matroid isomorphism + sanity checks). Pure Python, no dependencies, ~4 minutes.

## What is computed

* `G_h` — the indifference graph of the Hessenberg function `h`, edges `(j,i)` with `j < i ⩽ h(j)`.
* The local weight matroid at a fixed point `w ∈ Sₙ` is the cycle matroid `M(G_h)` relabelled by
  `w`, because the tangent weights are `e_{w(i)} − e_{w(j)}` over the edges. It is therefore the
  same matroid at every fixed point.
* `Poin(Hess(M,h), q) = Σ_{w ∈ Sₙ} q^{2·inv_{G_h}(w)}` (Shareshian–Wachs / Tymoczko).
* Matroids are bucketed by Tutte polynomial, then candidate pairs are confirmed by exhaustive
  search over bijections of the ground sets — Tutte equality is **not** matroid isomorphism.

## Sanity checks on the Poincaré formula (all pass)

| Check | Result |
|---|---|
| `h = (n,…,n)` must give `[n]_q!` | exact match for `n = 3,4,5` |
| total must be `n!` (Euler characteristic = number of fixed points) | holds throughout |
| palindromic (Poincaré duality, smooth compact) | holds throughout |
| `β₀` must equal the number of connected components, `C(n,m)` at a break `m` | matches at every break |

## Verified witnesses (`n ⩽ 6`)

| Pair | `h₁` / `h₂` | local matroid | Betti `β₂ₖ` | connected |
|---|---|---|---|---|
| **publish this one** — `Fl(C⁵)`, dim 5 | `(2,3,5,5,5)` / `(2,4,4,5,5)` | `U_{2,3} ⊕ U_{2,2}` | `(1,17,42,42,17,1)` vs `(1,12,47,47,12,1)` | **yes** |
| `Fl(C⁶)`, dim 6 | `(2,3,4,6,6,6)` / `(2,3,5,5,6,6)` | `U_{2,3} ⊕ U_{3,3}` | `(1,43,179,274,179,43,1)` vs `(1,29,175,310,175,29,1)` | yes |
| smallest of all — `Fl(C⁴)`, dim 2 | `(2,3,3,4)` / `(2,2,4,4)` | free, rank 2 | `(4,16,4)` vs `(6,12,6)` | no |
| W1 from the plan's first draft — `Fl(C⁶)`, dim 6 | `(3,3,3,6,6,6)` / `(3,3,5,5,5,6)` | `U_{2,3} ⊕ U_{2,3}` | `(20,80,160,200,160,80,20)` vs `(6,48,174,264,174,48,6)` | no |

In every row the two local weight matroids were confirmed isomorphic by exhaustive search, so
`A*(M)` and `OS(M)` — matroid invariants — agree at every fixed point while the Betti numbers,
hence `H*_T`, do not. The disconnected rows are valid but cheap: their `β₀` is the component
count, so the two spaces are separated by counting components. Prefer the connected rows.

## The independent GKM recomputation (Macaulay2) — ✅ **done, confirms the witness**

Everything above depends on one formula, so the check was redone from the GKM presentation of
Теорема 4, using no Shareshian–Wachs input at all. For `R = Q[t₁,…,t_n]`,

    H*_T(Hess(M,h))  =  ker ( ⊕_{w ∈ Sₙ} R  ⟶  ⊕_{edges (p,q)} R/(α_pq) ),

the map sending `(f_w)` to `(f_p − f_q mod α_pq)`, with an edge between `w` and `w·(j i)` for
`j < i ⩽ h(j)` of weight `α = t_{w(j)} − t_{w(i)}`. `gkm.m2` builds this kernel as a graded
module and reads the Betti numbers off `hilbertSeries`; the variables have degree 1, so the
series variable `T` is cohomological degree 2 and `Hilb = (Σ_k β_{2k} T^k)/(1−T)^n`.

Run: the three scripts listed under "Reproducing" below. Macaulay2 1.22; under a minute
through n = 5, a few minutes for the connected n = 6 pair (720 fixed points, 2160 GKM edges
over 6 variables).

| case | GKM kernel Hilbert numerator | agrees with `sweep.py` |
|---|---|---|
| `Fl(C³)` | `1 + 2T + 2T² + T³` `= [3]_q!` | ✅ |
| `Fl(C⁴)` | `1 + 3T + 5T² + 6T³ + 5T⁴ + 3T⁵ + T⁶` `= [4]_q!` | ✅ |
| `Fl(C⁵)` | `1 + 4T + 9T² + 15T³ + 20T⁴ + 22T⁵ + …` `= [5]_q!` | ✅ |
| `h = (2,3,3,4)` | `4 + 16T + 4T²` | ✅ |
| `h = (2,2,4,4)` | `6 + 12T + 6T²` | ✅ |
| **`h = (2,3,5,5,5)`** | **`1 + 17T + 42T² + 42T³ + 17T⁴ + T⁵`** | ✅ |
| **`h = (2,4,4,5,5)`** | **`1 + 12T + 47T² + 47T³ + 12T⁴ + T⁵`** | ✅ |
| `h = (2,3,4,6,6,6)` | `1 + 43T + 179T² + 274T³ + 179T⁴ + 43T⁵ + T⁶` | ✅ |
| `h = (2,3,5,5,6,6)` | `1 + 29T + 175T² + 310T³ + 175T⁴ + 29T⁵ + T⁶` | ✅ |

The two computations are independent — one counts `G_h`-inversions over `Sₙ`, the other takes
a module kernel over a polynomial ring — and they agree on every case, including the three
full flag varieties whose answers are known in advance. The witness stands:

> **`X₁ = Hess(M,(2,3,5,5,5))` and `X₂ = Hess(M,(2,4,4,5,5))` in `Fl(C⁵)` have isomorphic
> local weight matroids at every fixed point — hence equal `A*(M)` and `OS(M)` — and
> `H*_T(X₁) ≇ H*_T(X₂)`.**

## Files

| File | What it does |
|---|---|
| `sweep.py` | Enumerates Hessenberg functions for `n = 4,5,6`, buckets by Tutte polynomial of `M(G_h)`, compares Poincaré polynomials. Output: `sweep.log`. |
| `verify_pairs.py` | Exhaustive matroid-isomorphism confirmation for the candidate pairs + the sanity checks on the Poincaré formula. Output: `verify_pairs.log`. |
| `gkm.m2` | The GKM kernel construction and Hilbert-series reader; runs the `n = 3,4` cases. Output: `gkm_n34.log`. |
| `gkm_n5.m2` | Same construction, `Fl(C⁵)` validation + the witness pair. Output: `n5.log`. |
| `gkm_n6.m2` | Same construction, the connected `n = 6` pair. Output: `n6.log`. |

`gkm_n5.m2` and `gkm_n6.m2` reuse the first 58 lines of `gkm.m2` verbatim (the `gkmBetti`,
`coeffList` and `doCase` definitions) and differ only in the cases they run.

## The matrix `M`

**Choice of `M`.** `M` is any regular semisimple matrix (distinct eigenvalues); take
`M = diag(1,2,3,4,5)`. Nothing depends on the choice: `Hess(gDg⁻¹,h) = g·Hess(D,h)` reduces to the
diagonal case, and regular semisimple Hessenberg varieties with fixed `h` form a smooth proper
family over the connected set of regular diagonal matrices, so their topology is independent of
the eigenvalues. The computations never choose `M` at all — they use only the GKM data (fixed
points = coordinate flags `w ∈ S₅`, weights `t_{w(i)} − t_{w(j)}`), and the only property of `M`
behind that data is that a diagonal `M` preserves every coordinate subspace. Explicitly, with
flags `V₁ ⊂ ⋯ ⊂ V₄ ⊂ C⁵`: `X₁ = {MV₁ ⊂ V₂, MV₂ ⊂ V₃}` and `X₂ = {MV₁ ⊂ V₂, MV₂ ⊂ V₄, MV₃ ⊂ V₄}`.
The diagonal torus `T⁵` acts with the scalars acting trivially, so the effective torus has rank 4
(the weights lie in the sum-zero hyperplane) and both actions have **complexity `5 − 4 = 1`** —
the positive-complexity setting of the thesis, not the toric case.

## Reproducing

```
python3 sweep.py          # the n = 4,5,6 search             (~4 min, no dependencies)
python3 verify_pairs.py   # exhaustive matroid isomorphism   (~1 min)
M2 --script gkm.m2        # GKM recomputation, n = 3,4       (Macaulay2 1.22)
M2 --script gkm_n5.m2     # GKM recomputation, n = 5
M2 --script gkm_n6.m2     # GKM recomputation, connected n = 6 pair
```
