# Question 1 for isospectral manifolds and (partial) Hessenberg varieties: a proof

**Question 1 (thesis v2, §4.4).** For torus actions with `H^odd = 0`, does `S(X₁) ≅ S(X₂)` imply
equal Betti numbers?

The sweeps in `RESULTS.md` answered "yes" for full and partial regular semisimple Hessenberg
varieties with n ≤ 7. This note proves it for **all n**. The key step is purely combinatorial:
the cluster-permutohedron `Cl_Γ` determines the graph `Γ` up to isomorphism (Theorem A). The
graph then determines the manifold (Proposition B). For partial Hessenberg varieties, the face
poset determines the inflated graph with its parts (Theorem D, step 3), and a fibration reduces
the Betti numbers to the full case.

Cited inputs, all already used in thesis v2: the face-poset theorems of Ayzenberg–Buchstaber
([AB24, Thm. 1, Cor. 2.43, Thm. 2], thesis Thm. 4.25, Examples 4.27–4.28), the twin theorem
[AB21, Thm. 3.11], and Whitney's line-graph theorem.

## 1. Setup

Let `Γ` be a simple graph on `[n]`, `n ≥ 1`. An element of `Cl_Γ` is a pair `(C, A)`: a partition
`C = {V_1, …, V_m}` of `[n]` into blocks that induce connected subgraphs, and an assignment `A`,
i.e. label sets `L_1, …, L_m` partitioning `[n]` with `|L_i| = |V_i|`. The order is refinement of
blocks with label sets uniting accordingly, and `rk(C, A) = n − m` (thesis Construction 4.24).
The definition makes sense for disconnected `Γ` as well. The following facts are immediate.

- **(F1)** The minimal elements are the `n!` pairs (singletons, bijection `[n] → [n]`).
- **(F2)** For a minimal `x = (singletons, p)`, the map `(C, A) ↦ C` is an isomorphism from the
  upper interval `(Cl_Γ)_{≥x}` onto the lattice of connected partitions of `Γ`, i.e. onto
  `Flats(M(Γ))`. The assignment above `x` is forced: `L_i = p(V_i)`.
- **(F3)** The number of minimal elements below `y = (C, A)` is `ν(y) = ∏_i |V_i|!`: one for each
  choice of bijections `V_i → L_i`.

**Lemma 1.** Fix a minimal `x`. The atoms of `(Cl_Γ)_{≥x}` correspond to the edges of `Γ`. For a
set `S` of edges, the join of the corresponding atoms has rank `n − #components(V, S)`, which is the
rank of `S` in the graphic matroid. For two distinct edges `e`, `f`, the join `a_e ∨ a_f` has
`ν = 3! = 6` if `e` and `f` share a vertex, and `ν = 2!·2! = 4` otherwise.

*Proof.* By (F2), the join of a set of atoms is the partition into the components of `(V, S)`.
The rest is (F3). ∎

## 2. The cluster-permutohedron determines the graph

**Theorem A.** If `Cl_Γ ≅ Cl_{Γ'}` as posets, then `Γ ≅ Γ'`.

*Proof.* Let `Φ` be an isomorphism. By (F1), `n! = n'!`, so `n = n'`. Fix a minimal `x`. Then `Φ`
restricts to an isomorphism of lattices `(Cl_Γ)_{≥x} → (Cl_{Γ'})_{≥Φ(x)}`. It sends atoms to
atoms, giving a bijection `φ : E(Γ) → E(Γ')`. The map `Φ` commutes with joins in these intervals
and preserves rank and `ν`, since `ν(y)` is the number of minimal elements below `y` and so is
defined by the order. By Lemma 1, `φ` preserves adjacency of edges, so it is an isomorphism of line
graphs `L(Γ) → L(Γ')`. It also preserves the graphic rank of every edge set.

The connected components of `L(Γ)` are the line graphs of the components `Γ_1, …, Γ_r` of `Γ` that
have at least one edge. So `φ` matches them with the components `Γ'_1, …, Γ'_r` of `Γ'`, and
`L(Γ_i) ≅ L(Γ'_i)`. By Whitney's theorem [Whi32; Harary, *Graph Theory*, Thm. 8.3],
`Γ_i ≅ Γ'_i` unless one of them is `K_3` and the other is `K_{1,3}`. That case cannot occur. The
three edges of `K_3` span a rank-2 element (one block of size 3), while the three edges of
`K_{1,3}` span a rank-3 element, and `φ` preserves rank. Finally, both graphs have
`n − Σ|V(Γ_i)|` isolated vertices. ∎

`φ` also preserves the rank of every edge set, so it is an isomorphism of graphic matroids. This is
not needed for the proof.

**Computational cross-check** (`reconstruction_check.py`, `reconstruction_check.log`). All graphs
with at most 6 vertices are enumerated, one per isomorphism class, with nauty `geng`. For each one,
`Cl_Γ` is built from the definition and its exact isomorphism class is computed as the canonical
form of the rank-coloured Hasse diagram, using nauty's Traces. Graphs with different `n` are
compared too. Result: 208 graphs, 208 pairwise non-isomorphic posets (the largest, for n = 6, has
about 10⁴ elements). Before the sweep, a self-check confirms that randomly relabelled copies of
every graph with at most 4 vertices, with the poset elements shuffled, give identical forms.

## 3. The graph determines the manifold

**Proposition B.** Let `π` be a permutation of `[n]` with `π(Γ) = Γ'`, and let `P_π` be its
permutation matrix. Then `A ↦ P_π A P_π⁻¹` is a diffeomorphism `M_{Γ,λ} → M_{Γ',λ}`. It is
equivariant with respect to the automorphism `t ↦ P_π t P_π⁻¹` of the diagonal torus `T^n`.

*Proof.* Conjugation by `P_π` preserves Hermitian matrices and their spectrum, and
`(P_π A P_π⁻¹)_{π(i)π(j)} = A_{ij}`. So the zero pattern prescribed by `Γ` goes to the one
prescribed by `Γ'`. For diagonal `t`, `P_π t P_π⁻¹` is diagonal and
`P_π (t A t⁻¹) P_π⁻¹ = (P_π t P_π⁻¹)(P_π A P_π⁻¹)(P_π t P_π⁻¹)⁻¹`. ∎

**Corollary C (Question 1, full flags).** Let each of `X`, `X'` be either an isospectral manifold
`M_{Γ,λ}` (`Γ` connected, `λ` generic) or a regular semisimple Hessenberg variety `Hess(M, h)`
with `Γ_h` connected. If `S(X) ≅ S(X')`, then `β_j(X) = β_j(X')` for all `j`. Moreover, `X` and
`X'` have isomorphic equivariant cohomology rings, after reindexing the torus.

*Proof.* `S(M_{Γ,λ}) ≅ Cl_Γ` [AB24, Thm. 1], and `S(Hess(M,h)) ≅ Cl_{Γ_h}` through the twin
`M_{Γ_h,λ}` [AB24, Cor. 2.43]. By Theorem A the two graphs are isomorphic, and by Proposition B
the corresponding isospectral manifolds are equivariantly diffeomorphic up to an automorphism of
`T^n`. A Hessenberg variety and its twin have isomorphic equivariant cohomology and equal Betti
numbers [AB21, Thm. 3.11]. ∎

Two remarks:

- Corollary C does not need `H^odd = 0`. Within these families the face poset determines the
  manifold up to weakly equivariant diffeomorphism, or up to passing to the twin. This covers
  `M_{K_{1,3},λ}` and `M_{C_n,λ}`, which are not equivariantly formal (thesis Examples 4.29–4.30).
- The answer does not come from a formula for the Betti numbers in terms of the poset. It comes
  from rigidity: the poset remembers the whole graph. So in this family the face poset determines
  the Betti numbers for a structural reason, and the family cannot produce a counterexample.

## 4. Partial Hessenberg varieties

Let `k̄ = (k_1, …, k_s)` be a composition of `n`, `h` a Hessenberg function on `[s]`, and
`X = Hess_{k̄}(M, h) ⊂ Fl_{k̄}`. Its face poset is the poset of [AB24, Thm. 2] (thesis
Example 4.28), implemented in `partial_hessenberg.py`. Its elements are sets `{(W_j, c_j)}`, where
the `W_j` partition `[n]`, `c_j` is a vector of part counts with `|c_j| = |W_j|`, and `Σ_j c_j = k̄`.
Each block must be admissible, i.e. connected in the inflated graph. The facts used are these:

- **(P1)** The minimal elements are the fixed points `J = (J_1, …, J_s)`, `|J_a| = k_a`. There are
  `n!/∏ k_a!` of them.
- **(P2)** For a fixed point `J`, `S(X)_{≥J} ≅ Flats(G_J)`. Here `G_J ≅ Γ_h(k̄)` is the inflated
  graph on the coordinates `[n]`: `x ∈ J_a` and `y ∈ J_b` are adjacent iff `ab ∈ Γ_h`. Parts are
  independent sets. ([AB24, Thm. 2]; validated in `validate_partial.py`.)
- **(P3)** The number of fixed points below `{(W_j, c_j)}` is `ν = ∏_j |W_j|! / ∏_a c_j(a)!`.

For two edges `uv` and `vw` of `G_J` sharing the vertex `v`, the join has one block `{u, v, w}`.
So `ν = 3` if `u` and `w` lie in the same part and `ν = 6` otherwise. Two disjoint edges give
`ν = 4`.

**Fibration identity** (`fibration_check.py`, `fibration_check.log`). Let `h̃(i) = K_{h(a)}` for
`i` in part `a`, where `K_b = k_1 + ⋯ + k_b`. Then `Hess(M, h̃)` is the preimage of `X` under
`Fl_n → Fl_{k̄}`, a bundle with fibre `∏_a Fl(k_a)`. Hence

    P(Hess(M, h̃)) = P(X) · ∏_a [k_a]_q!        (q = t²).

Combinatorially, the inversions of `w ∈ S_n` along the edges of `Γ_{h̃}` split into those between
parts, which give `ind(J)`, and those inside parts. The graph `Γ_{h̃}` is the inflated graph with
every part made a clique. The identity and this description of `Γ_{h̃}` were checked for all
2,949 cases `(k̄, h)` with `n ≤ 7`.

**Theorem D (Question 1, partial flags).** If `X = Hess_{k̄}(M, h)` and `X' = Hess_{k̄'}(M', h')`
are partial regular semisimple Hessenberg varieties with `S(X) ≅ S(X')`, then
`β_j(X) = β_j(X')` for all `j`.

*Proof.* **Step 1 (splitting).** Let `Q_1, …, Q_r` be the connected components of `Γ_h`. They are
intervals of parts. The Białynicki-Birula index `ind(J)` is the sum of the indices of the
restrictions of `J` to each component, and each of these depends only on the relative order of
that component's coordinates. Hence
`P_X = #Fix(X) · ∏_j P_{Q_j}(q) / P_{Q_j}(1)`. Here `P_{Q_j}` is the Poincaré polynomial of the
partial Hessenberg variety of the component, and an isolated part contributes the factor 1.

**Step 2 (one component).** Let `Q` be a component with at least two parts. By the fibration
identity, `P_Q · ∏_{a∈Q} [k_a]_q! = P(Hess(M_Q, h̃_Q))`, and `Γ_{h̃_Q}` is connected. By
Corollary C, the right-hand side depends only on the isomorphism class of `Γ_{h̃_Q}`. That class
is determined by the inflated component `G_Q` together with its partition into parts. So `P_Q` is
determined by `(G_Q, parts)` up to isomorphism.

**Step 3 (reconstruction).** Let `Φ : S(X) → S(X')` be an isomorphism. By (P1),
`#Fix(X) = #Fix(X')`. As in Theorem A, fix a fixed point `J`. Then `Φ` gives a bijection
`φ : E(G_J) → E(G'_{Φ(J)})` that preserves rank and `ν` of the join of every edge set. By the
values of `ν` above, `φ` is an isomorphism of line graphs. The components of `G_J` with an edge are
exactly the inflations `G_Q` of the components `Q` with at least two parts. Copies of isolated
parts are isolated vertices. So `φ` matches these components. Take a matched pair `G_Q`, `G'_{Q'}`.

- If `G_Q` has at least 5 vertices, then by Whitney's theorem in the form of Jung
  [Jun66; Hemminger–Beineke 1978] `φ` is induced by a graph isomorphism `ψ`. Two distinct vertices
  `u`, `w` of `G_Q` lie in the same part iff they have a common neighbour `v` with
  `ν(a_{uv} ∨ a_{vw}) = 3`. Copies of a part `a` always have a common neighbour, because `Q` is
  connected with at least two parts. So `ψ` preserves parts.
- If `G_Q` has at most 4 vertices, then so does `G'_{Q'}`, since by Whitney the two are isomorphic
  or are `K_3` and `K_{1,3}`. The finite check `partial_small_components.py`
  (`partial_small_components.log`) covers this case. It takes all connected inflated components
  with at most 4 vertices: 19 of them, 13 up to isomorphism of graphs with parts. It shows that
  whenever an edge bijection preserves `(rank, ν)` on all edge sets, the two components are
  isomorphic as graphs with parts.

So the multiset of isomorphism classes of `(G_Q, parts)` over the components is the same for `X`
and `X'`. By Steps 1 and 2, `P_X = P_{X'}`. ∎

Theorem D contains Corollary C's Hessenberg case as `k̄ = (1, …, 1)`. It also covers Grassmannians
and partial flag varieties: in those cases `Γ_h = K_s` and the statement is classical.

## 5. What remains open

Question 1 is now settled for every family in type A that this project considered. A
counterexample would have to come from GKM manifolds outside type A, for example Hessenberg
varieties of other Lie types, where the analogue of Theorem A is not known, or from non-algebraic
torus manifolds. Natural next questions:

1. **Other Lie types.** Is there a rigidity statement like Theorem A for the face posets of
   regular semisimple Hessenberg varieties in types B, C and D?
2. **Formalisation.** Theorem A is elementary apart from Whitney's theorem, and it is a good Lean
   target once G3 (lattice of flats, `formal/Formal/FlatLattice.lean`) is in place. Mathlib has
   line graphs (`SimpleGraph.lineGraph`), but not Whitney's theorem.

## References

- [AB21] A. Ayzenberg, V. Buchstaber, *Manifolds of isospectral matrices and Hessenberg varieties*,
  IMRN 2021.
- [AB24] A. Ayzenberg, V. Buchstaber, *Cluster-permutohedra and submanifolds of flag varieties with
  torus actions*, IMRN 2024.
- [Whi32] H. Whitney, *Congruent graphs and the connectivity of graphs*, Amer. J. Math. 54 (1932).
- [Jun66] H. A. Jung, *Zu einem Isomorphiesatz von H. Whitney für Graphen*, Math. Ann. 164 (1966).
- R. L. Hemminger, L. W. Beineke, *Line graphs and line digraphs*, in *Selected Topics in Graph
  Theory*, 1978.
- F. Harary, *Graph Theory*, 1969, Thm. 8.3.
