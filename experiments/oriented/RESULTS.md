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

## Second round: subtori of rank 2 (`subtori.py`, log `subtori.log`)

### Acyclic fixed points are the vertices of the moment polytope

**Proposition.** Let a torus `H` act on a compact symplectic manifold `X` in a Hamiltonian way with
isolated fixed points, with moment map `μ` and moment polytope `Δ = μ(X)`, and let the weights
`α_{p,j} ∈ 𝔥*` be taken with respect to a compatible almost complex structure, with the sign
convention for which `μ(z) = μ(p) + ½ Σ_j |z_j|² α_{p,j}` in the local normal form at `p`. Let `C_p`
be the cone spanned by the weights at `p`. Then the tangent cone of `Δ` at `μ(p)` is `C_p`, and so

- `OM_p` is acyclic iff `μ(p)` is a vertex of `Δ`, and `p ↦ μ(p)` is a bijection from the acyclic
  fixed points to the vertices of `Δ`;
- `OM_p` is totally cyclic iff `μ(p)` is an interior point of `Δ`;
- in general `μ(p)` lies in the relative interior of a face of dimension `dim (C_p ∩ −C_p)`.

*Proof.* By the local normal form the image of a neighbourhood of `p` is a neighbourhood of the
apex in `μ(p) + C_p`. The fibres of `μ` are connected (Atiyah; Guillemin–Sternberg), and by the
local convexity theorem the polytope near a value `μ(x)` is the local cone at any point `x` of the
fibre (Sjamaar, 1998). Hence `Δ` coincides with `μ(p) + C_p` near `μ(p)`. The weights are nonzero
because `p` is isolated, so they lie in an open half-space iff `C_p` is pointed, i.e. iff `μ(p)` is
a vertex; they are totally cyclic iff `C_p` is a linear subspace, which is all of `𝔥*` since the
action is effective; and the face of `Δ` through `μ(p)` is cut out by the lineality space
`C_p ∩ −C_p`. Finally the fibre over a vertex is connected and consists of fixed points, so it is
one point. ∎

So the count of acyclic fixed points is not a new invariant: it is the number of vertices of the
moment polytope. Checked on 68 actions of 2-dimensional subtori on Hessenberg varieties (`n ⩽ 5`)
and Grassmannians, generic and not, where the weights at `p` are only some of the differences
`μ(p′) − μ(p)`: 682 acyclic fixed points are all vertices of the hull of the images, 1,668 totally
cyclic ones are all interior, 12 mixed ones are all on the boundary and not vertices; no exceptions.
For a generic `T²` on a connected Hessenberg variety in `Fl(Cⁿ)` the polygon is the projected
permutohedron, with `n(n−1)` vertices whatever `h` is, so this count carries no information there.

### What the oriented matroids of a generic `T²` see

For a generic 2-torus the oriented matroid at `p` is a cyclic word: the weights and their negatives
in angular order, up to rotation and reflection. Equivalently it is the function `θ ↦ ind_p(θ)` on
the circle of directions, without its base point. The Betti numbers are `Σ_p q^{ind_p(θ)}` at one
common `θ`, which the unbased words do not obviously give.

| | `n = 4` | `n = 5` | `n = 6` |
|---|---|---|---|
| connected Hessenberg functions | 5 | 14 | 42 |
| Poincaré polynomials | 4 | 9 | 22 |
| classes by the multiset of words | 4 | 10 | 26 |
| … of which contain two Poincaré polynomials | 0 | 0 | 0 |
| classes by the multiset of index sets `{ind_p(θ)}_θ` | 4 | 10 | 26 |
| … ambiguous | 0 | 0 | 0 |
| classes by (dimension, number of vertices) | 4 | 7 | 11 |
| … ambiguous | 0 | 2 | 7 |

(three choices of generic characters for `n = 4, 5`, two for `n = 6`; same counts each time.)

- **In every case computed, the oriented matroids of a generic `T²` determine the Betti numbers.**
  They do more: 4, 10, 26 are the numbers of connected Hessenberg functions up to reversal, so the
  multiset of words determines the variety. Even the much coarser multiset of index sets does.
- The Track A pair is separated: e.g. for one choice of characters the index sets
  `{0..5}, {1..4}, {2,3}` occur `20, 97, 3` times on `X₁` and `20, 88, 12` times on `X₂`. These
  numbers depend on the subtorus; the 20 is the number of vertices.
- There is no formula here, and no proof that the words determine the Betti numbers. The picture
  across ranks is: rank 1, the oriented matroids give the Betti numbers by an identity; rank 2,
  they determine them in all examples, for no known reason; full rank on a homogeneous space, they
  are constant and determine nothing.

The formula that does produce Betti numbers from oriented data is the one of Track F
(`experiments/chow/RESULTS.md`, §4): it uses the signs of the weights against one common `ξ`, and
the local Tutte polynomials of the negative parts.

## Status and restated target

- Atomic experiment: done. Kill criterion: met on the named examples and on all homogeneous
  spaces and Hessenberg varieties with the full torus (item 2 is a proof); not met for subtorus
  actions.
- Restated target, after the second round: (i) prove or refute that the oriented matroids of a
  generic 2-torus determine the Betti numbers (true for `n ⩽ 6`); (ii) the object to use for
  cohomology is the oriented matroid at each fixed point **with the tope of a common generic `ξ`**,
  which enters the stratum formula of Track F. The question about acyclic fixed points is settled
  by the proposition above.
- Engine: `oriented_matroid` (chirotope, signed circuits, acyclic / totally cyclic, topes and
  index set, canonical forms up to relabelling and up to reorientation for at most 7 elements).
