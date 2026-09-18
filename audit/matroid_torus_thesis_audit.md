# Audit Report: «Инварианты матроидов, определяемых действиями тора» (Mikheev, MSU 2022)

**Framework:** checkpoint audit (CP0–CP4), per project convention.
**Status tags:** `ESTABLISHED` (standard, verified), `CITED-PUBLIC` (verified against public source), `DERIVED` (correct modulo exposition), `SUSPECT` (likely error, needs repair), `REFUTED-AS-STATED` (formally wrong as written; repair proposed), `MAJOR GAP` (claimed result absent from body), `CITATION GAP` (source pin missing/outdated), `TYPO`.
**Date of audit:** 2026-07-18. All arXiv/journal pins re-checked against current public records.

---

## CP0 — Ingest

Document: специалист diploma, Mech-Math MSU, Chair of Higher Geometry and Topology, advisor V. M. Buchstaber. 20 pp., 6 sections, 17 references + one placeholder `[18] To be continued`.

**Declared main results:**

- **Theorem 1 (= Theorem 5 = Theorem 8).** For a manifold `X` with a torus action of arbitrary complexity and a fixed point `pt`, the local equivariant cohomology `H*_T(X, X\pt)` determines the linear matroid of weights `S(X)⩾pt` inside the face poset `S(X)`.
- **Claimed corollary (abstract + intro).** Equivariant cohomology is *not* determined by the Chow ring `A*(M)` and the Orlik–Solomon algebra of the weight matroid `S(X)⩾pt`.
- Worked descriptions of `S(X)` for flag varieties, Hessenberg varieties, partial Hessenberg varieties (cluster-permutohedra), plus two open questions (Q1: does `S(X)` determine Betti numbers under equivariant formality; Q2: tropicalization of flag varieties).

**Overall verdict:** the core theorem is `DERIVED` — correct in substance, standard in method (slice theorem + excision + GKM computation for the compactified tangent representation), and consistent with Ayzenberg–Cherepanov `arXiv:2203.06282` (`CITED-PUBLIC`). The thesis's genuine contribution is the assembly + the local-cohomology reformulation; its weakest point is that the advertised negative corollary is **never proved in the body** (`MAJOR GAP`, item A1 below). Several background statements contain formal errors (items B1–B6).

---

## CP1 — Reference audit and updates

### 1.1 Verified / updated pins

| Ref | Thesis citation | Current status | Action |
|---|---|---|---|
| [1] | Ayzenberg–Buchstaber, cluster-permutohedra, arXiv:2203.14133 (2022) | Published: **IMRN 2024, no. 3, 1931–1967, doi:10.1093/imrn/rnad076** | `CITED-PUBLIC`; update pin. Published abstract confirms: face poset of the torus action on isospectral Γ-shaped Hermitian matrices ≅ cluster-permutohedron — matches Предложение 6. |
| [2] | Ayzenberg–Cherepanov, arXiv:2203.06282 | v1 confirmed; "locally geometric poset" and Theorem 7 of the thesis match the paper's main theorem verbatim in substance | `CITED-PUBLIC`. Check for a published version before resubmission. |
| [3] | Ayzenberg–Masuda–Solomadin, arXiv:2203.10641 | Listed elsewhere as "to appear in Sbornik: Mathematics" | `CITATION GAP` (minor): pin the Sbornik volume/pages. |
| [7] | Maclagan–Sturmfels, *Introduction to Tropical Geometry*, GSM 161 | Correct | — |
| [9] | Abe–Horiguchi Hessenberg survey, arXiv:1904.11155 | Published in a Springer proceedings volume (2020) | `CITATION GAP` (minor): pin. |
| [13] | Adiprasito–Huh–Katz, arXiv:1511.02888 "2018" | Published: **Annals of Math. 188 (2018), no. 2, 381–452** | Update pin. **But see B4: the theorem attributed to [13] is not their statement.** |
| [14] | Huh thesis, "Michigan University" | **University of Michigan** | `TYPO`. |
| [18] | "To be continued" | Placeholder | Delete. |

### 1.2 Missing references that materially affect the thesis

- **Speyer–Sturmfels, "The tropical Grassmannian" (Adv. Geom. 4 (2004))** — Theorem 9 (`trop(Gr(2,n)) = space of phylogenetic trees`) is *their* theorem; citing only the textbook [7] undersells provenance. `CITATION GAP`.
- **Ardila–Klivans, "The Bergman complex of a matroid and phylogenetic trees" (JCTB 2006)** — the fine (flat-chain) structure of the Bergman fan used in Определение 17 is theirs; also directly ties the two halves of Section 5 together.
- **Brandt–Eur–Zhang, "Tropical flag varieties", Adv. Math. 384 (2021) 107695 (arXiv:2005.13727).** This paper **predates the thesis** and substantially answers Вопрос 2: it introduces the flag Dressian, proves the correspondence (flag Dressian points ↔ valuated flag matroids ↔ flags of tropical linear spaces ↔ coherent flag-matroidal subdivisions), and settles realizability up to ground sets of size 5 with a size-6 counterexample. Question 2 must be reframed (see CP4). Follow-ups: Haque (2012, initiating), Boretsky (arXiv:2111.12587 / 2208.09128, TNN tropical flags), Joswig–Loho–Luber–Olarte (IMRN 2023), Boretsky–Eur–Williams (flag positroids).
- **Feichtner–Yuzvinsky (Invent. Math. 155 (2004))** — `A*(M)` ≅ Chow ring of the wonderful compactification for realizable `M`; this is the actual source needed to state the realizable case of the Chow-ring comparison correctly (see B4).
- **Gelfand–Goresky–MacPherson–Serganova (Adv. Math. 63 (1987))** — companion to [6], standard alongside it.
- **Chang–Skjelbred (Ann. Math. 100 (1974))** — Лемма 1 is used with no citation. `CITATION GAP`.
- **Björner–Wachs–Welker / Barmak** if poset-fiber arguments survive into a journal version (they appear in [1]).

---

## CP2 — Mathematical audit

### A. Main results

**A1. `MAJOR GAP` — the advertised corollary is unproved.**
The abstract and introduction claim: «эквивариантные когомологии не определяются кольцом Чжоу и алгеброй Орлика-Соломона линейного матроида весов S(X)⩾pt», and «Мы проверили гипотезу… Эта гипотеза оказалась неверной». **No section of the body contains this verification.** There is no exhibited pair of actions with isomorphic weight matroids (hence isomorphic `A*(M)` and OS algebras at each fixed point) but non-isomorphic `H*_T`. As written, the second declared result of the thesis is an assertion without proof.
*Repair path (concrete, computable):* take two GKM manifolds with the same local weight matroids at all fixed points but different GKM graphs — e.g., two Hessenberg varieties `Hess(M,h₁)`, `Hess(M,h₂)` in `Fl(C^4)` whose local weight arrangements coincide (both are sub-arrangements of type A root systems of equal local rank) but whose Betti numbers differ (computable via Shareshian–Wachs / chromatic quasisymmetric functions, or directly in Macaulay2 using the GKM presentation of Пример 17). Since `A*(M)` and `OS(M)` are invariants of the matroid alone, any such pair proves the claim. This is a one-afternoon computation with the tooling already cited in Заключение (Macaulay2 + Ayzenberg's GKM-homology code). **This is the single highest-priority fix.**

**A2. Theorem 1/5/8 — `DERIVED`, with three exposition obligations.**
The chain `H*_T(X, X\pt) ≅ H*_T(D, D\pt) ≅ H*_T(S^{2n}, pt) = (e^T(T_{pt}X)) = (∏ⱼ α_{j,pt})` is correct given: slice theorem [11], excision, and Предложение 5. Obligations:
1. State coefficient conventions (Q throughout) and that fixed points are isolated — used silently.
2. The step "the ideal `(∏ⱼ αⱼ)` determines the matroid" deserves one honest sentence: by unique factorization in `Q[t₁,…,t_k]`, the principal ideal determines the **multiset** of linear forms `{αⱼ}` up to nonzero scalars; this is exactly the data of the linear matroid of weights *including parallel elements/multiplicities*. The current wording («задаёт алгебраическое многообразие… двойственным является набор весов») detours through a hyperplane arrangement, which loses multiplicities — the ideal itself does not. Rewrite via unique factorization.
3. Weights are defined only up to sign (real tangent representation, no invariant complex structure assumed) — the thesis says this in §3.2 but the theorem statement should recall it: the matroid is well-defined precisely because matroid data is sign-blind. (Ayzenberg's own slides make exactly this remark.)
4. **Deduplicate:** Theorem 1 (intro) = Theorem 5 = Theorem 8. State once, cross-reference twice.

**A3. Предложение 5 (relative `H*_T` of `S^{2n}`) — `ESTABLISHED`,** standard GKM computation; matches the two-vertices-n-edges graph. Typos in the proof: `H*(S^{2n})` should read `H*_T(S^{2n})` in the displayed chain; «эвивариантно», «последоательность», «му получаем». The injectivity of `H*_T(S^{2n},pt) → H*_T(S^{2n})` follows from surjectivity of restriction to the fixed point (equivariant formality) splitting the LES — say so in one clause instead of the current homotopy-equivalence sentence, which is garbled («Tpt → S^{2n} → S^{2n} → pt»).

**A4. Теорема 7 (S(X)⩾x is a geometric lattice) — `CITED-PUBLIC`** against arXiv:2203.06282. The thesis proof sketch is a faithful compression. Fine.

### B. Background section errors (each formally wrong as written)

**B1. Предложение 3 (Euler characteristic via Möbius) — `REFUTED-AS-STATED`.**
Stated: `χ(ord(ℒ\{0̂,1̂})) = |µ(0̂,1̂)| + 1`. The order complex is a wedge of `|µ(0̂,1̂)|` spheres of dimension `r−2` (r = rank of ℒ), so
`χ = 1 + (−1)^{r−2}·|µ(0̂,1̂)| = 1 + µ(0̂,1̂)` (Philip Hall's theorem: `χ̃ = µ(0̂,1̂)`).
The stated formula holds only for even `r`; for odd rank the sign flips (e.g. ℒ = Boolean lattice of rank 3: `µ = −1`, complex is `S¹`? no — take `U²₃`: `µ(0̂,1̂) = 2`, `ord` = 3 points, `χ = 3 = 1+2` ✓; but `U³₄`... rank 3, `µ = −3·?` — in general the sign matters). **Fix:** state `χ̃(ord(ℒ\{0̂,1̂})) = µ(0̂,1̂) = (−1)^r |µ(0̂,1̂)|` and drop the absolute value from the unreduced formula, or restrict to the reduced Euler characteristic. Also the "Mayer–Vietoris" invocation in the proof is unnecessary: wedge of spheres ⇒ Betti numbers immediately.

**B2. Boolean expansion of the characteristic polynomial (after Определение 12) — `REFUTED-AS-STATED`.**
Written: `χ_M(t) = Σ_{A⊆M} µ(0̂,A) t^{r(E)−r(A)}`. Two problems: `µ(0̂,A)` is defined on the lattice of flats, not on arbitrary subsets; and the correct Boolean expansion (Whitney's theorem) is
`χ_M(t) = Σ_{A⊆E} (−1)^{|A|} t^{r(E)−r(A)}` (for loopless `M`).
Replace, cite Oxley [17] or Stanley EC1.

**B3. Определение 18 (Chow ring of a matroid) — `REFUTED-AS-STATED`.**
Two deviations from AHK: (i) variables must range over **nonempty proper flats** of `M` (the thesis allows all flats incl. `0̂`, `E`); (ii) the linear ideal `J_M` is generated by **differences** `Σ_{F∋a} x_F − Σ_{F∋b} x_F` over pairs of atoms `a,b` — not by the sums `Σ_{F⊇a} x_F` themselves. Quotienting by the sums kills the fundamental class in degree `r−1` and does not give AHK's ring (their ring has `A^{r−1} ≅ Z` — quotienting by all sums would force additional relations). Restate per AHK Def. 1.1 / §5.

**B4. Теорема 2 (realizability ⇔ Chow ring of a projective variety) — `SUSPECT` + `CITATION GAP`.**
Attributed to [13] (AHK). AHK do **not** prove this equivalence; their point is the opposite emphasis — `A*(M)` satisfies the Kähler package (PD, HL, HR) *regardless* of realizability. What is true and sourced: for `M` realizable over `k`, `A*(M)` ≅ Chow ring of the de Concini–Procesi wonderful compactification (**Feichtner–Yuzvinsky 2004**), a smooth projective `k`-variety. The converse ("iso to the Chow ring of *some* projective variety ⇒ realizable") is, to my knowledge, open/false-adjacent and certainly not in [13] — the Chow ring `A*(X(Σ_M))` of the (non-complete) Bergman-fan toric variety already equals `A*(M)` for every `M`, realizable or not. **Fix:** either restate as the Feichtner–Yuzvinsky forward direction with correct citation, or supply a genuine source for the equivalence; delete the "iff" otherwise.

**B5. Конструкция 5 + Теорема 3 (cocircuit matrix, Kapranov rank) — `SUSPECT`.**
The matrix is declared «над полем F₂». Kapranov rank (Определение 20, from Develin–Sturmfels via [7]) is defined for matrices over `R̄ = R ∪ {∞}` (tropical semiring), not over `F₂`. The Develin–Sturmfels cocircuit matrix is a real 0/1 matrix. Also double-check the 0/1 convention (`c_{ij} = 0` iff element `i` lies in cocircuit `j` — verify against [7] Ch. 5 before print; the thesis's convention may be inverted). The theorem itself (Kapranov rank of `C(M)` equals `r(M)` iff `M` realizable over some field) is genuine Develin–Sturmfels material — cite them (`On the rank of a tropical matrix`) alongside [7]. `CITATION GAP`.

**B6. Определение 19 (realization) — `TYPO`/`SUSPECT`.**
«набор векторов в (r+1)-мерном векторном пространстве» — should be an `r`-dimensional space (rank-`r` matroid realizes in dimension `r`; the `+1` looks like a projective/affine confusion). Also the biconditional should quantify: *for every* `S ⊆ E`, `S ∈ ℐ ⟺ {vᵢ : i ∈ S}` linearly independent.

### C. Local errors and typos (fix-list)

1. **Определение 22 (complexity):** «сложность действия равна n − m» — `m` is undefined; must be `n − k` where `k = dim T`. `TYPO` (but in a definition that the whole thesis rests on — fix first).
2. **Пример 15 (`CP^n` GKM):** `CP^n` has `n+1` fixed points; the displayed tuple `(f_{σ1},…,f_{σn}) ∈ ⊕ⁿ` should have `n+1` components indexed by `[n+1]`, GKM graph `K_{n+1}` (as correctly said in Пример 10).
3. **Пример 8 (Hessenberg):** condition should read `M·Vᵢ ⊂ V_{h(i)}`; state that `Hess(M,h)^T = S_n` requires `M` **regular semisimple** (currently implicit via «фиксированный спектр» only in Пример 12).
4. **Пример 20:** the final sentence about `H^{n−1}(ord(Cl(C_n)))` («сильно больше, чем n(n−1)/2, поскольку мы не факторизуем по симплициальным цепям старшей размерности») is not a wellformed mathematical statement. Either compute the top Betti number of `ord(Cl(C_n)\{1̂})` (feasible in polymake for n = 3,4,5) or replace with a precise inequality with proof.
5. **Лемма 1:** notation `H*_T(X^H, X^T)` needs the union/sum over all corank-1 subtori `H` (the standard form uses the one-skeleton `X₁`); cite Chang–Skjelbred 1974.
6. **Terminology:** «лист»/«флэт»/«флет» used interchangeably («Решётка листов» def. header vs «Решётка флэтов» in its body); pick one («флэт» is the loanword used in the modern Russian literature) and note «лист» once.
7. **Пример 4:** «булева решетка F₂^{n−1}» — write the Boolean lattice `B_{n−1}` (subsets of an (n−1)-set); `F₂^{n−1}` reads as a vector space.
8. **Notation clash:** `T_x` = stabilizer (Конструкция 7) vs `T_x X` = tangent space (§3.2). Rename stabilizer `St(x)` or `T_x^{st}`.
9. Spelling: «Реализиция» (TOC + §2.2), «упомяналось», «Симлициальный», «комлекса», «тоесть», «естть», «му получаем», «неподвивжных», «многобразие», «делели», «оказалось неверной» → «оказалась неверной», latin «c» in «cимплексов», "Bruhat" transliteration inconsistency.
10. Дублирование нумерации: Вопрос 1/2 fine, but Theorem numbering restarts logic (Теорема 1 in intro vs Теоремы 2–9 in body) — renumber on merge.

---

## CP3 — Corrections summary (priority-ordered)

| # | Item | Severity | Fix |
|---|---|---|---|
| 1 | A1: advertised corollary unproved | **MAJOR GAP** | Add a computed counterexample section (Hessenberg pair; Macaulay2 script as artifact) |
| 2 | B3: Chow ring relations wrong | REFUTED | Restate per AHK (proper nonempty flats; difference relations) |
| 3 | B4: Теорема 2 misattributed/false "iff" | SUSPECT | Restate via Feichtner–Yuzvinsky; drop converse or source it |
| 4 | B1: Euler characteristic sign | REFUTED | `χ̃ = µ(0̂,1̂)`; sign `(−1)^r` |
| 5 | B2: Boolean expansion | REFUTED | Whitney's theorem `Σ (−1)^{|A|} t^{r(E)−r(A)}` |
| 6 | B5: `F₂` vs tropical semiring; convention check | SUSPECT | Real 0/1 matrix; cite Develin–Sturmfels; verify convention |
| 7 | C1: complexity `n − m` → `n − k` | TYPO (load-bearing) | one character |
| 8 | B6, C2, C3: realization dim, `CP^n` indices, reg. semisimple | TYPO | as listed |
| 9 | A2: main theorem exposition (UFD argument, sign-of-weights remark, dedup) | DERIVED | rewrite ~½ page |
| 10 | CP1 pins: [1]→IMRN 2024, [13]→Annals 188, [3]/[9] pins, delete [18], add Speyer–Sturmfels, Ardila–Klivans, BEZ, Feichtner–Yuzvinsky, Chang–Skjelbred | CITATION GAP | bib pass |

---

## CP4 — Future development program

Template per item: target; prerequisite; atomic experiment; kill criterion; payoff; artifact.

### Next 30 days

1. **Counterexample computation (closes A1).** Target: explicit pair `(X₁, X₂)` with isomorphic local weight matroids at all fixed points, hence isomorphic `A*(M)` and `OS(M)`, but `H*_T(X₁) ≇ H*_T(X₂)`. Prerequisite: none — GKM presentations of Примеры 16–17 suffice. Atomic experiment: enumerate Hessenberg functions on `n = 4`, compute local weight matroids at each `σ ∈ S₄` and Poincaré polynomials (GKM-homology repo / Shareshian–Wachs tables); find matroid-matched, Betti-mismatched pair. Kill criterion: no such pair for `n ≤ 5` ⇒ the corollary needs a different witness class (try `Gr(2,n)` vs a partial Hessenberg, or drop equivariant formality). Payoff: converts the thesis's second claim from assertion to theorem. Artifact: `counterexample.m2` + one-page section.
2. **Errata pass.** Items 2–8 of CP3. Artifact: v2 of the thesis text.
3. **Reframe Вопрос 2.** The literal question (does a "reasonable" description of `trop Fl(Cⁿ)` exist) is answered: flag Dressian ⊋ tropical flag variety in general, with the four-way correspondence of Brandt–Eur–Zhang (Adv. Math. 2021) and TNN coincidence (Boretsky). New, open reformulation compatible with this thesis's viewpoint: **compare the face poset `S(Fl(Cⁿ))` (cluster-permutohedron of `K_n`) with the fan structure / poset of the flag Dressian `FlDr(n)`** — does the cluster-permutohedron embed as (or map to) the face poset of a subfan? Artifact: revised Question 2 + literature paragraph.

### Days 31–90

4. **Question 1 (Betti-determinacy of `S(X)`).** Target: theorem or counterexample for `S(X₁) ≅ S(X₂) ⇒ β_j(X₁) = β_j(X₂)` under `H^{odd} = 0`. Prerequisite: item 1 (its data answers the *local* version; Q1 is the *global* poset). Atomic experiment: for complexity-0 (quasitoric) case the answer is yes (face poset = poset of the orbit polytope determines `h`-vector) — write this warm-up; then test complexity 1 on `Gr(2,4)` (Buchstaber–Terzić data) vs a candidate with matching poset. Kill criterion: a matching-poset pair among isospectral manifolds `X_{G,λ}` with distinct Betti numbers — then Q1 is settled negatively and becomes a classification question. Payoff: the thesis's stated open problem, resolved either way. Artifact: standalone note.
5. **Oriented matroids from (stably) almost complex structures.** The Заключение notes signs were discarded. Target: when `X` carries a `T`-invariant stably complex structure, weights have well-defined signs ⇒ `S(X)⩾pt` refines to an **oriented** linear matroid. Atomic experiment: write the oriented matroid of weights for `CP^n` and `Fl(C³)` at each fixed point; check whether reorientation classes distinguish fixed points that the underlying matroid cannot. Kill criterion: orientation data is constant across fixed points for all tested `X` (then the refinement is vacuous for this class). Payoff: genuinely new invariant; connects to Celaya–Loho–Yuen-style oriented tropical geometry. Artifact: definitions + examples section, seed of a paper.
6. **Chow-ring direction, correctly aimed.** Given B4, the productive question is not "does `A*(M)` see `H*_T`" (item 1 shows no) but: **which quotient of the equivariant data is matroid-invariant?** Candidates from the post-2018 literature: augmented Chow ring, intersection cohomology of matroids and Kazhdan–Lusztig polynomials (Braden–Huh–Matherne–Proudfoot–Wang), stellahedral `K`-theory (Eur–Huh–Larson). Atomic experiment: compute `IH(M)` and augmented `A*(M)` for the local matroids of the item-1 pair; test whether the *global* poset `S(X)` glues the local augmented Chow rings into something with the size of `H*_T(X)` (sheaf on `S(X)`, à la GKM sheaves of Braden–MacPherson). Kill criterion: dimension count fails already for `CP²`. Payoff: this is the natural "next theorem" after Theorem 1 — local-to-global matroid invariants on the face poset.

### Long horizon / frozen unless a gate opens

- **Face posets of flag Dressians / valuated version of Theorem 1** (gate: item 3 finds a poset map). Valuated matroids of weights would require a filtration on `H*_T(X, X\pt)` — none is visible yet.
- **Non-realizable local models** (gate: an example of a torus action whose weight matroid is non-realizable — impossible as stated, since weight matroids are linear by construction; the interesting variant is: which *abstract* locally geometric posets arise as `S(X)`? Realizability obstruction question, flagged in [2] — coordinate with Ayzenberg–Cherepanov before investing).
- **`g`-theorem circle (Adiprasito [15]):** thesis mentions it only as motivation; no concrete dependency. Keep frozen.

### Paperability

The publishable core after the 30-day items: Theorem 1 + the computed counterexample (A1) + the cluster-permutohedron examples for partial Hessenbergs (Пример 18, which appears to be new relative to [1] and worth stating as a proposition with proof, currently only sketched). That is a coherent short paper: *"Local equivariant cohomology and matroids of weights of torus actions"*. Items 5–6 are the sequel.

---

## Checkpoint recap

- **CP0** — full read; structure and claims inventoried.
- **CP1** — [1] pinned to IMRN 2024(3):1931–1967; [13] to Annals 188(2018); BEZ (Adv. Math. 384 (2021)) identified as a pre-thesis source resolving Вопрос 2; 6 missing references listed.
- **CP2** — main theorem `DERIVED` (sound; 4 exposition obligations); **one `MAJOR GAP`** (unproved advertised corollary); **three `REFUTED-AS-STATED`** background statements (Euler characteristic sign, Boolean expansion, Chow-ring relations); **two `SUSPECT`** (AHK misattribution "iff", `F₂`-vs-tropical cocircuit matrix); load-bearing typo in the complexity definition.
- **CP3** — 10-item priority fix table.
- **CP4** — 6-item program with atomic experiments and kill criteria; paperability assessment.

**Owed to the next run:** the `n = 4,5` Hessenberg counterexample computation (item 1, closes the MAJOR GAP); Develin–Sturmfels convention check (B5); Sbornik pin for [3].
