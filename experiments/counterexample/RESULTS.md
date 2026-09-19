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

## Still owed: the independent GKM recomputation (Macaulay2)

Everything above depends on one formula. The independent check does not use it at all: build
the GKM ring of Теорема 4 directly and read off its Hilbert series.

For `h` on `[n]`, let `R = Q[t₁,…,t_n]` with `deg tᵢ = 2`. The GKM presentation is the kernel

    H*_T(Hess(M,h))  =  ker ( ⊕_{w ∈ Sₙ} R  ⟶  ⊕_{edges (p,q)} R/(α_pq) )

where the map sends `(f_w)` to `(f_p − f_q mod α_pq)`, the sum is over pairs `p, q ∈ Sₙ`
differing by a transposition `(j i)` with `j < i ⩽ h(j)`, and `α_pq = t_{p(j)} − t_{p(i)}`. In
Macaulay2 this is a graded module kernel, and `hilbertSeries` gives `P(q)/(1−q²)ⁿ`; the
numerator must equal the Poincaré polynomial computed here. For `n = 5` the source has rank
120 over a 5-variable ring — large but well within range; if it is slow, restrict to one
connected component or use the module of sections over the GKM graph's edge set directly.

Agreement confirms the witness. Disagreement means the Shareshian–Wachs convention is being
misapplied in `sweep.py`, and every Betti number in this file must be re-derived from the GKM
side — the matroid isomorphisms are unaffected either way, since they are computed exhaustively
and independently.
