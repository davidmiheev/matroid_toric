# Thesis v2: changes from the 2022 original

`thesis_en.tex` / `thesis_en.pdf` is a revised **English** edition of
`docs/thesis_matroid_invariants_torus_actions.pdf` (Russian, 2022). The LaTeX
source of the original was not available, so this is a fresh source. It is a
faithful translation with corrections, not a new paper: the section structure,
examples and scope are kept.

Build: `xelatex thesis_en.tex` twice (needs `fontspec`, `eulervm`, `newpx`, `bbold`,
`tikz`, `microtype`, `xurl`, `enumitem`, `booktabs`; on Debian/Ubuntu:
`texlive-xetex texlive-fonts-extra`). The figure is generated into `fig_u45.tex`.

Typography reproduces the original, which was built with XeLaTeX: TeX Gyre Pagella text,
Euler math letters (Latin and Greek), newpx symbol and extension fonts, Latin Modern math
operators and digits, `bbold` blackboard bold, Euler fraktur. The configuration was derived
by comparing the fonts embedded in the two PDFs (`pdffonts`). It has to work around
`eulervm`, which under XeLaTeX's `TU` encoding leaves the math accents undefined and routes
`:` and `\infty` to fonts that are no longer loaded; the preamble comments say where. The
page size is A4; the original was US letter.

Every claim that was changed was checked against its primary source (arXiv full
text or Crossref metadata), not taken from the audit on trust. Audit item IDs refer
to `audit/matroid_torus_thesis_audit.md`.

## Where the audit itself was wrong

These were found while verifying the audit against the sources. The audit file
is left unchanged as the user's document; `PLAN.md` has been corrected.

| Audit item | Audit said | Actually | Source |
|---|---|---|---|
| **B4** (Теорема 2) | AHK do not prove the "iff"; misattribution | AHK **do** prove it: Thm 5.12, *a Chow equivalence from a smooth projective variety to X(Σ_M) exists iff M is realizable over k*. The original's attribution was right; only its paraphrase was loose (it dropped "induced by a morphism") | arXiv:1511.02888, Def. 5.11, Thm 5.12 |
| **B5** (cocircuit matrix) | 0/1 convention "may be inverted" | The original's convention is **correct** (0 iff the element lies in the cocircuit). Only "над полем F₂" was wrong | Develin–Santos–Sturmfels, Def. 7.1 |
| **B5 / CP3** | cite "Develin–Sturmfels, *On the rank of a tropical matrix*" | the authors are **Develin, Santos, Sturmfels** (MSRI Publ. 52, 2005) | Crossref |
| **B3** | J_M generated over "pairs of atoms" | AHK Def. 1.3 uses pairs of **elements** of E (equivalent for simple matroids) | arXiv:1511.02888 |
| **A3** (Предложение 5) | `ESTABLISHED` | the proof's GKM computation silently needs **pairwise independent** weights (otherwise ∩(αⱼ) ≠ (∏αⱼ)) and contains an algebra slip; the statement is true in general by the Thom isomorphism | — |
| **CP4 paperability** | Пример 18 (partial Hessenberg) "appears to be new relative to [1]" | **not new**: [1] §5, Construction 5.13 and Theorem 2, covers it, and [1] Cor. 3.2 covers full Hessenberg varieties | arXiv:2203.14133 |
| CP1 [3] | "to appear in Sbornik" | Sb. Math. **214** (2023), no. 6, 793–815 | Crossref |

## Errors found that the audit missed

- **Пример 9: the defining condition of isospectral manifolds is reversed.** The original has
  «aᵢⱼ ≠ 0, если [i,j] — ребро»; it should be *aᵢⱼ = 0 whenever {i,j} is not an edge*
  (Γ-shaped matrices). Source: [1] §2.3.
- **Hessenberg varieties are not isospectral manifolds.** The original (before Конструкция 8)
  says Hess(M,h) «попадают» into the class X_{G,λ} with matrix graph the indifference graph.
  They are the *twins* of the staircase manifolds: they have homeomorphic orbit spaces and
  isomorphic H*_T, but they are different manifolds (Ayzenberg–Buchstaber, IMRN 2021,
  Thm 1.1, 3.11). The conclusion S(Hess) ≅ Cl(Γ_h) survives, via [1] Prop. 2.42 / Cor. 3.2.
- **Пример 20 is wrong as stated.** Cl(Cₙ)∖{1̂} has rank n−2, so it cannot be the cell poset
  of a subdivision of T^{n−1}. It is the face poset of the **(n−2)-skeleton** of one
  ([1] Prop. 1.1 + Thm 1(4), girth argument). Its top Betti number is **2n−2**, so the claim
  «сильно больше, чем n(n−1)/2» is false for n ≥ 4 (equal at n = 4, smaller at n = 5).
  Verified by computation for n = 3, 4, 5 (`experiments/cluster_permutohedra/`).
- **The Orlik–Solomon algebra is used in the abstract and the main corollary but never
  defined.** A definition has been added.
- **The GKM theorem is used without citing Goresky–Kottwitz–MacPherson.** Now cited (Invent.
  Math. 131 (1998)).
- **Вопрос 1 was stated as "⟺".** The "⟸" direction fails already for quasitoric manifolds:
  the pentagonal prism and the cube with a vertex cut off have the same f-vector but
  different face lattices. Restated as "⟹", and the complexity-zero case, where the answer
  is yes, is recorded.
- **Plücker ideal:** "|J| = r + 1" with r undefined → |J| = m + 1; the convention x_{I∪j} = 0
  for j ∈ I is added.
- **Theorem 5 (main theorem), precision.** The original identifies H*_T(X, X∖pt) *with* the
  ideal (∏αⱼ). As an abstract module it is just Q[t] shifted, with no information about the
  weights; the statement must be about the *image under restriction to pt*. It is now stated
  that way, with injectivity proved.

## Change list by section

### Front matter and §1
| Change | Audit |
|---|---|
| Abstract restates both results precisely; the corollary is now proved | A1 |
| «Мы проверили гипотезу… оказалась неверной» replaced by Theorem B with a pointer to the proof | A1 |
| Theorem 1 = 5 = 8 deduplicated: Theorem A (intro summary) → Theorem 4.15 (precise) → Corollary 4.23 (was Теорема 8) | A2.4 |
| Conventions paragraph (Q coefficients, closed manifolds, isolated fixed points, H*(BT)) | A2.1 |
| Buchstaber–Terzić claims now cited (Mosc. Math. J. 2019; Mat. Sb. 2019) | — |
| Previously uncited [4], [8], [9], [12], [14] cited where their topics occur | — |

### §2 Matroids and posets
| Original | Change | Audit |
|---|---|---|
| Опр. 3 «лист/флэт/флет» | one term, "flat"; closure and loops defined | C6 |
| Опр. 8 rank function | minimal elements have rank 0 (normalization made explicit) | — |
| Пример 4 «булева решетка F₂^{n−1}» | Boolean lattice B_{n−1} | C7 |
| Boolean expansion Σ_{A⊆M} µ(0̂,A)… | Whitney: χ_M(t) = Σ_{A⊆E} (−1)^{|A|} t^{r(E)−r(A)}, loopless, **with a proof** | B2 |
| Предложение 3: χ = \|µ\| + 1 | χ̃ = µ(0̂,1̂) = (−1)^r \|µ(0̂,1̂)\|; proof via Hall + Rota; B₃ example of the sign | B1 |
| Опр. 17 Bergman fan (v_F undefined) | v_F = e_F, chains of nonempty proper flats, sign convention; cite Ardila–Klivans, Feichtner–Yuzvinsky | CP1 |
| Опр. 18 Chow ring | AHK Def. 1.3 exactly: nonempty proper flats, difference relations | B3 |
| — | Orlik–Solomon algebra defined | new |
| Опр. 19 «(r+1)-мерном» | k^r; biconditional quantified over all S ⊆ E; parallel elements | B6 |
| Рис. 2 Vámos | explicit list of the five dependent 4-sets | — |
| Конструкция 4 | independence of forests proved (only cycles were argued) | — |
| Теорема 2 | exact AHK Thm 5.12 via Chow equivalence; FY for the realizable direction | B4 (corrected) |
| Конструкция 5 «над полем F₂» | real 0/1 matrix; cocircuit defined | B5 |
| Опр. 20 Kapranov rank (min over fields) | Kapranov rank *over k* via Puiseux series (DSS Def. 3.9) | B5 |
| Теорема 3 | DSS Prop. 7.2 + Thm 7.3 (one direction in general, converse for infinite k) | B5 |
| Рис. 1 | redrawn (TikZ, generated) with 0̂ and 1̂; caption says U_{4,5} | — |

### §3 Equivariant cohomology
| Original | Change | Audit |
|---|---|---|
| Опр. 22 complexity «n − m» | n − k | C1 |
| "eq. formal ⟺ H^odd = 0" asserted | justified (localization + Euler characteristic), closed X | — |
| Предложение 4 | also H*_T ≅ H* ⊗ H*(BT) free (needed in §4.5) | — |
| Пример 7 | dimension count cleaned; the "space of symmetries of the n-torus" sentence dropped | — |
| Пример 8 Hessenberg | M·Vᵢ ⊂ V_{h(i)}; M regular semisimple, WLOG diagonal; smooth/dim/H^odd = 0 cited (De Mari–Procesi–Shayman) | C3 |
| Замечание 2 partial Hessenberg | identified with the spaces ᵏM′_{Γ_h,λ} of [1] §5.2 | — |
| Пример 9 isospectral | **condition reversed** (see above); effective T^{n−1}; complexity = b₁(Γ) | new |
| T_x (stabilizer) | St(x) | C8 |

### §4 GKM theory
| Original | Change | Audit |
|---|---|---|
| Опр. 24 GKM | pairwise-independence formulation; edge labels defined | — |
| Пример 10/15 CPⁿ | T^{n+1}, n+1 fixed points, indexed by [n+1], K_{n+1} | C2 |
| Пример 11 | fixed-point description repaired | — |
| Лемма 1 | one-skeleton formulation; Chang–Skjelbred cited | C5 |
| Теорема 4 | GKM98 cited | new |
| Предложение 5 | new proof via Thom isomorphism; GKM computation kept as a remark with its hypothesis | A3 (corrected) |
| Теорема 5 | image-under-restriction formulation; UFD lemma (Lemma 4.14); multiplicities; sign remark | A2.2, A2.3 |
| Теорема 7 | exact hypotheses of AC22 Thm 1; proof sketch fixed (F ↦ V_F instead of "orthogonal complement") | A4 |
| Конструкция 8 | aligned with [1] Def. 2.14 (clusterings, left cosets) | — |
| Hessenberg ∈ isospectral class | replaced by the twin argument | new |
| Пример 18 | attributed to [1] §5, Thm 2 (inflation graph Γ_h(k̄)) | CP4 (corrected) |
| Пример 19 claw | kept; sourced ([1] Prop. 1.1) and verified by computation | — |
| Пример 20 cycles | corrected (see above) | C4 |
| Предложение 7 | exact AMS23 Thm 1 (Q; Z with connected stabilizers); non-formality consequence added | — |
| Вопрос 1 | "⟺" → "⟹"; complexity-zero case and the counterexample to "⟸" recorded | new |
| — | **§4.5 new: the counterexample** (Theorem 4.35), plus remarks on the minimal disconnected pair, the n = 6 pair, and why it does not bear on Вопрос 1 (Cl posets differ: 200 vs 190 rank-2 elements) | A1 |

### §5–6 and appendix
| Original | Change | Audit |
|---|---|---|
| Опр. 28 Plücker ideal | \|J\| = m + 1; x_{I∪j} = 0 convention | new |
| Теорема 9 | Speyer–Sturmfels cited; sign and edge-length conventions stated | CP1 |
| Вопрос 2 | kept as asked, then reformulated against Brandt–Eur–Zhang (flag Dressian) and Boretsky | CP4 item 3 |
| Заключение | results summary updated; tools cited | — |
| — | Appendix A: computations, with tables | — |

### Bibliography
[1] → IMRN 2024(3):1931–1967; [3] → Sb. Math. 214(6):793–815; [9] → Springer PROMS 2020,
*Schubert Calculus and Its Applications in Combinatorics and Representation Theory*,
251–279; [13] → Ann. of Math. 188(2):381–452; [14] University of Michigan; [18] placeholder
deleted. Added: Ayzenberg–Buchstaber IMRN 2021, Buchstaber–Terzić (×2), Chang–Skjelbred,
De Mari–Procesi–Shayman, Develin–Santos–Sturmfels, Feichtner–Yuzvinsky, GGMS, GKM,
Ardila–Klivans, Speyer–Sturmfels, Brandt–Eur–Zhang, Boretsky, Orlik–Terao,
Milnor–Stasheff, Tymoczko, Macaulay2. Every pin was checked against Crossref.

### Typos (audit C9, C10)
Moot: the text is newly written in English, and theorem numbering is automatic.
