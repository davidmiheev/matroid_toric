# Paper

*Face posets, local weight matroids and Betti numbers of torus actions* (`paper.tex`, `paper.pdf`, 27 pp.
including a table of contents and a 6-page background appendix). Intended for deposit on
[Hexagon](https://hexagonmath.org).

The source compiles with XeLaTeX (TeX Gyre Pagella text, as in the thesis) and with pdfLaTeX
(newpxtext), with no warnings about undefined references. Run the engine three times for the table of contents.

Five results, each proved in full in the paper:

1. **Theorem A (§3).** Local equivariant cohomology at a fixed point, as an ideal of `H*_T(pt)`, is generated
   by the product of the tangent weights. It determines the weights with multiplicities, and hence the local
   lattice `S(X)_{⩾pt}`. Thesis v2, Theorem 4.15.
2. **Theorem B (§4).** Local weight matroids do not determine `H*_T`: the pair
   `Hess(M,(2,3,5,5,5))`, `Hess(M,(2,4,4,5,5))` in `Fl(C⁵)`. The Chow ring, augmented Chow ring,
   intersection cohomology, Kazhdan–Lusztig polynomial and Orlik–Solomon algebra of the local matroid are listed.
3. **Theorem C (§5).** The face poset determines the Betti numbers for isospectral manifolds and all full and
   partial regular semisimple Hessenberg varieties of type A, because `Cl_Γ` determines `Γ`.
4. **Theorem D (§6).** The same for regular semisimple Hessenberg varieties of all simply-laced Lie types: the
   face poset `{(F, wW_F)}` determines `W` and the lines of the Hessenberg ideal up to isometry. Types B, C,
   F₄, G₂: by computation in rank ≤ 5 only. `experiments/question1_lie_types/`.
5. **Theorem E (§7).** `P_X(q) = Σ_σ (q−1)^{rk σ} e_σ(q)` with `e_σ` a sum of Tutte polynomials `T(1, q)` of the
   matroids of negative weights. For simply-laced Hessenberg varieties `e_σ` depends only on `S(X)_{⩽σ}`
   (Proposition 7.3). Also the moment-polytope description of acyclic fixed points (Proposition 7.5).
   `experiments/chow/`, `experiments/oriented/`.

Appendix A introduces posets, matroids and their invariants, oriented matroids and signed graphs, torus
actions, equivariant cohomology, GKM theory, moment maps and the Białynicki-Birula decomposition, root
systems, and flag and Hessenberg varieties.

Reviews and checks:

- `REVIEW-5.2.md`: independent read of §5.2.
- All references were checked against Crossref, the publishers' pages and the arXiv sources (2026-11-24);
  theorem numbers of AB21, AB24 and AC22 refer to their arXiv versions, as the paper says.

Still to do before deposit:

- Affiliation and e-mail, further acknowledgements, and the statement on the use of AI (all marked
  `TODO(author)` in the source).
- Hexagon does not allow AI systems as contributors; the AI contribution is stated in a title footnote and in
  the statement at the end. Hexagon's listings carry tags for how the text was produced and how much of it the
  contributors understand; if the deposit form asks about these, answer them yourself.
- §§6–7 and the appendix have not yet had an independent read.
