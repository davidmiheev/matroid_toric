# Paper draft

*Face posets, local weight matroids and Betti numbers of torus actions* (`paper.tex`, `paper.pdf`, 15 pp.).
Compile with XeLaTeX (same fonts as the thesis: TeX Gyre Pagella + Euler).

Five results:

1. **Theorem A (§3).** Local equivariant cohomology at a fixed point, as an ideal of `H*_T(pt)`, is generated
   by the product of the tangent weights. It determines the weights with multiplicities, and hence the local
   lattice `S(X)_{⩾pt}`. Thesis v2, Theorem 4.15.
2. **Theorem B (§4).** Local weight matroids do not determine `H*_T`: the pair
   `Hess(M,(2,3,5,5,5))`, `Hess(M,(2,4,4,5,5))` in `Fl(C⁵)`. Thesis v2, Theorem 4.45 (with Lemmas 4.42–4.43
   and Proposition 4.44).
3. **Theorem C (§5).** The face poset determines the Betti numbers for isospectral manifolds and all full and
   partial regular semisimple Hessenberg varieties of type A, because `Cl_Γ` determines `Γ`. Thesis v2,
   Theorems 4.35 and 4.38; `experiments/question1/PROOF.md`.
4. **Theorem D (§6).** The same for regular semisimple Hessenberg varieties of all simply-laced Lie types: the
   face poset `{(F, wW_F)}` determines `W` and the lines of the Hessenberg ideal up to isometry.
   `experiments/question1_lie_types/PROOF.md`. Types B, C, F₄, G₂: by computation in rank ≤ 5 only.
5. **Theorem E (§7).** `P_X(q) = Σ_σ (q−1)^{rk σ} e_σ(q)` with `e_σ` a sum of Tutte polynomials `T(1, q)` of the
   matroids of negative weights; plus the moment-polytope description of acyclic fixed points.
   `experiments/chow/RESULTS.md` §4, `experiments/oriented/RESULTS.md`.

Still to do before submission:

- Affiliation, e-mail and acknowledgements (marked `TODO(author)` in the source).
- Choose a venue. The draft is written as a short research article.
- ~~An independent read of §5.2.~~ Done: `REVIEW-5.2.md` (one overstated claim in Corollary 5.6 corrected, Lemma 5.7 added). A read by a specialist is still worth having.
