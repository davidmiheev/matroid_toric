# Track E — oriented local weight matroids: results

Script: `oriented.py` (log: `oriented.log`), using mtengine's `oriented_matroid`.
Run: `../../engine/.venv/bin/python oriented.py`.

When `X` has a `T`-invariant (stably) complex structure the tangent weights at a fixed point `p`
have signs, so the local weight matroid is an oriented matroid `OM_p`. Three things are compared
at each fixed point: the underlying matroid, the oriented matroid up to relabelling, and its
reorientation class. *Acyclic* means the weights lie in an open half-space, i.e. `p` is an
isolated extremum of some component of the moment map.

## Answer to the plan's question

**On the examples the plan names, and on every homogeneous space and every regular semisimple
Hessenberg variety with its full torus, the oriented refinement is constant across fixed points.**
That is the kill criterion as written. But it holds for a structural reason that does not extend
to other actions, and **for subtorus actions the refinement does separate fixed points that the
matroid identifies**, already for `T² ⊂ T⁴` acting on `CP³`. So the track is not vacuous; its
target has to be restated (last section).

## Results

| Space, torus | Fixed points | Underlying classes | Oriented classes | Reorientation classes |
|---|---|---|---|---|
| `CPⁿ`, `n = 1..5`, full torus | `n+1` | 1 (free matroid) | 1 | 1 |
| `Fl(C³)`, `Fl(C⁴)` | 6, 24 | 1 | 1 | 1 |
| `Gr(2,4)`, `Gr(2,5)` | 6, 10 | 1 | 1 | 1 |
| Track A pair `Hess(2,3,5,5,5)`, `Hess(2,4,4,5,5)` | 120 each | 1 | 1 | 1 |
| `Sp(4)/B` (type B₂), `G₂/B` | 8, 12 | 1 | 1 | 1 |
| `Fl(C³)`, generic circle | 6 | 1 (`U_{1,3}`) | 2 | 1 |
| Track A pair, generic circle | 120 each | 1 (`U_{1,5}`) | 3 | 1 |
| `CP³`, generic `T²`, characters in convex position | 4 | 1 (`U_{2,3}`) | 1 | 1 |
| `CP³`, generic `T²`, one character inside the triangle of the others | 4 | 1 (`U_{2,3}`) | **2** | 1 |
| `CP⁶`, generic `T³` (characters in the log) | 7 | 1 (`U_{3,6}`) | **3** | **3** |

## Why

1. **Free matroids (`CPⁿ`, all toric and quasitoric manifolds).** The weights at a fixed point
   form a basis, and any two bases differ by a linear map, so there is one oriented matroid.
2. **Weyl translates.** For `G/P` and for regular semisimple Hessenberg varieties of any type, the
   signed weights at the fixed point `w` are `w` applied to the signed weights at the identity
   (`t_{w(i)} − t_{w(j)} = w(t_i − t_j)`). A linear isomorphism multiplies the chirotope by the
   sign of its determinant, so `OM_w ≅ OM_e` for every `w`. No computation is needed; the table
   confirms it.
3. **Type A carries nothing even between varieties.** The local matroids are graphic, hence
   regular, and a regular matroid has a single reorientation class (Bland–Las Vergnas, 1978). So
   in type A the reorientation class is a function of the underlying matroid. In particular the
   two varieties of Theorem B have the same oriented matroid at every fixed point, not only the
   same matroid.
4. **Circles.** For a generic circle `S¹ ⊂ T` the weights at `p` are `n` nonzero integers, the
   matroid is `U_{1,n}` at every fixed point, and the oriented matroid is the unordered pair
   `{ind(p), n − ind(p)}`, where `ind(p)` is the number of negative weights. With Poincaré duality
   these classes give the Betti numbers: for `Fl(C³)` the classes `{0,3}, {1,2}` occur 2 and 4
   times, i.e. `(1,2,2,1)`; for the Track A pair they occur `2, 34, 84` and `2, 24, 94` times,
   i.e. `(1,17,42,…)` and `(1,12,47,…)`. So the oriented matroids of a generic circle separate
   the two varieties of Theorem B, which no matroid invariant at the fixed points does.
5. **Subtori of the torus of `CPⁿ`.** If `T^k` acts on `CPⁿ` through characters
   `a_0, …, a_n ∈ Z^k`, the weights at `p_i` are `a_j − a_i`. `OM_{p_i}` is acyclic exactly when
   `a_i` is a vertex of the convex hull of the characters (the moment polytope), and totally
   cyclic when `a_i` is in its interior. For four characters in the plane the matroid is `U_{2,3}`
   at all four fixed points, and the oriented matroid tells the interior point from the three
   vertices. For seven characters in `Z³` the reorientation classes themselves differ: three
   classes of `U_{3,6}` among seven fixed points with the same matroid.

## What the experiment shows about the right object

Items 2 and 4 together say where the information is. For the full torus on a homogeneous space
each `OM_p` is the same abstract oriented matroid; the Betti numbers are the distribution of
the number of minus signs of the tope of **one** generic `ξ` in all the `OM_p` at once. An
abstract oriented matroid at each point forgets how the weight lattices at different fixed points
are identified, and that identification is what carries the cohomology. Restricting to a subtorus
moves part of this global information into the local oriented matroids, the whole of it in the
case of a circle.

## Status and restated target

- Atomic experiment: done. Kill criterion: met on the named examples and on all homogeneous
  spaces and Hessenberg varieties with the full torus (item 2 is a proof); not met for subtorus
  actions.
- Restated target: for an action with an invariant almost complex structure, study the oriented
  matroids `OM_p` **together with the tope of a common generic `ξ`** (equivalently, the oriented
  matroids of the subtori). Natural first questions: (i) which part of `H*(X)` do the `OM_p` of a
  rank-2 subtorus see, between the two extremes above; (ii) is the number of acyclic fixed points
  always the number of vertices of the moment polytope for Hamiltonian actions (it is in every
  example here).
- Engine: `oriented_matroid` (chirotope, signed circuits, acyclic / totally cyclic, topes and
  index set, canonical forms up to relabelling and up to reorientation for at most 7 elements).
