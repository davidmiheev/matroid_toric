# Development plan

Derived from `audit/matroid_torus_thesis_audit.md` (CP3 fix table + CP4 program) and from a
re-reading of the thesis text. Each track states: **target**, **prerequisite**, **atomic
experiment**, **kill criterion**, **payoff**, **artifact** — the audit's own template.

Ordering principle: Track A closes the one `MAJOR GAP`, Track B makes the text defensible,
and both are prerequisites for everything downstream. Tracks C–F are research; Track G
(formalization) runs in parallel and is scoped in `docs/lean-formalization-feasibility.md`.

---

## Track A — Close the MAJOR GAP: the unproved corollary  ✅ **witnesses found and verified**

**Target.** An explicit pair `X₁, X₂` of torus manifolds whose local weight matroids
`S(X_i)_{⩾p}` are isomorphic at every fixed point — hence with equal `A*(M)` and `OS(M)`,
which are matroid invariants — but with `H*_T(X₁) ≇ H*_T(X₂)`. This converts the abstract's
second claim from assertion to theorem.

**Why Hessenberg varieties are the right test class.** For a regular semisimple `M` and a
Hessenberg function `h : [n] → [n]`, the tangent weights of `Hess(M,h)` at the fixed point
`w ∈ Sₙ` are `{ t_{w(i)} − t_{w(j)} : j < i ⩽ h(j) }`, i.e. `{ e_{w(i)} − e_{w(j)} }` over
the edges of the indifference graph `G_h` on `[n]`. So the local weight matroid **is the
graphic matroid `M(G_h)`**, relabelled by `w` — in particular it is the *same* matroid at
every fixed point, and two Hessenberg varieties have matching local matroids exactly when
`M(G_{h₁}) ≅ M(G_{h₂})`, i.e. (Whitney) when `G_{h₁}` and `G_{h₂}` are 2-isomorphic. This
reduces the search to a finite graph-theoretic condition.

**Status: done for `n ⩽ 6`.** `experiments/counterexample/sweep.py` enumerates all Hessenberg
functions for `n = 4,5,6`, buckets them by the Tutte polynomial of `M(G_h)`, and compares
Poincaré polynomials `Σ_{w ∈ Sₙ} q^{2·inv_{G_h}(w)}` (Shareshian–Wachs / Tymoczko). Summing
over all of `Sₙ` makes the `w`-vs-`w^{-1}` convention irrelevant — `w ↦ w^{-1}` is a bijection
of the index set, so the generating function is unchanged. `verify_pairs.py` then confirms
each candidate by an **exhaustive ground-set bijection** between the two cycle matroids, since
Tutte equality alone is not matroid isomorphism. Both scripts are in the repository and their
output is in `RESULTS.md`.

### The witness to publish

`X₁ = Hess(M, h₁)` and `X₂ = Hess(M, h₂)` in `Fl(C⁵)`, `M` regular semisimple, same `T⁵`,
120 fixed points each, both **connected**, both of complex dimension 5:

| | `X₁` | `X₂` |
|---|---|---|
| `h` | `(2,3,5,5,5)` | `(2,4,4,5,5)` |
| `G_h` | triangle `{3,4,5}` + path `1–2–3` | triangle `{2,3,4}` + edges `12`, `45` |
| local weight matroid | `U_{2,3} ⊕ U_{2,2}` | `U_{2,3} ⊕ U_{2,2}` (verified isomorphic, exhaustively) |
| Betti `(β₀,β₂,…,β₁₀)` | `(1, 17, 42, 42, 17, 1)` | `(1, 12, 47, 47, 12, 1)` |

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

The matroids are isomorphic at every fixed point, so `A*(M)` and `OS(M)` agree; the Betti
numbers differ, and equivariant formality (`H*_T ≅ H* ⊗ Sym(t*)` as modules) upgrades that to
`H*_T(X₁) ≇ H*_T(X₂)`. The local matroid has a circuit, so this is not an artifact of a free
(locally generic) matroid, and both varieties are connected, so they cannot be separated by
counting components.

### Correction to the first draft of this plan

The originally proposed witness **W1** — `h₁ = (3,3,3,6,6,6)` vs `h₂ = (3,3,5,5,5,6)` in
`Fl(C⁶)` — is valid (matroids exhaustively isomorphic, Betti `(20,80,160,200,160,80,20)` vs
`(6,48,174,264,174,48,6)`), and the hand-computed `20` and `6` are correct. But both varieties
are **disconnected**: `h₁` breaks at `3` and `h₂` at `5`, giving `C(6,3) = 20` and `C(6,5) = 6`
components — which is exactly what those coefficients count. A witness separated by its number
of connected components is cheap, so W1 is demoted to a remark. The same defect afflicts the
smallest pair of all, `h = (2,3,3,4)` vs `(2,2,4,4)` in `Fl(C⁴)` (dimension 2, local matroid
free of rank 2, Betti `(4,16,4)` vs `(6,12,6)`): valid, minimal, and disconnected.

Connected witnesses also exist at `n = 6` — e.g. `(2,3,4,6,6,6)` vs `(2,3,5,5,6,6)`, local
matroid `U_{2,3} ⊕ U_{3,3}`, Betti `(1,43,179,274,179,43,1)` vs `(1,29,175,310,175,29,1)` —
so the phenomenon is not special to `n = 5`.

### What remains to be done on this track

1. ~~**An independent recomputation of the Betti numbers.**~~ **Done.** `H*_T` was rebuilt in
   Macaulay2 directly from the GKM presentation of Пример 17 — the kernel of
   `⊕_{w} R → ⊕_{edges} R/(α_pq)` as a graded `Q[t₁,…,t_n]`-module — and its Hilbert series
   numerator agrees with the Shareshian–Wachs count on every case, including the three full
   flag varieties, which reproduce `[n]_q!` exactly for `n = 3,4,5`. The two routes share no
   input. See `experiments/counterexample/{gkm.m2,gkm_n5.m2}` and `RESULTS.md`.
2. ~~**Write the section.**~~ **Done** — §4.5 of `docs/thesis-v2/thesis_en.pdf` (Theorem 4.42,
   with Lemmas 4.39–4.40 and Proposition 4.41). Originally planned as: statement, the `Fl(C⁵)` pair, the two indifference graphs, the
   matroid isomorphism, the Betti table, and the deduction. One page.
3. **Optional.** Push the sweep to `n = 7` to see whether a witness exists with a
   3-connected local matroid (there, 2-isomorphism forces graph isomorphism, so any witness
   must come from a genuinely different mechanism).

**Kill criterion.** Superseded — the search succeeded and the independent GKM recomputation
confirms it. What remains is exposition, not risk.

**Payoff.** The thesis's second declared result becomes a proved statement with a witness small
enough to print in full.

**Artifact.** `experiments/counterexample/{sweep.py,verify_pairs.py}` + `RESULTS.md`, and a
one-page section for the thesis text.

---

## Track B — Errata pass (thesis v2)  ✅ **done — applied in the English v2**

**Status.** All twelve items are applied in `docs/thesis-v2/thesis_en.tex` (English rewrite,
22 pp.), and every change is logged against its audit item in `docs/thesis-v2/CHANGES.md`.
Verifying the items against their primary sources turned up **two items below that were
wrong in the audit** (3 and 6, corrected in place) and **seven further errors the audit
missed**. The biggest of those: the isospectral-manifold condition is reversed in Пример 9;
Hessenberg varieties are not isospectral manifolds (they are *twins* of them); and Пример 20 is
false as stated. See `CHANGES.md`, "Where the audit itself was wrong" and "Errors found that
the audit missed".

Each item below is a specific replacement, in priority order (audit CP3 items 2–8, 10 plus
the local fix-list). None of them requires new mathematics.

1. **Определение 22 (complexity).** «сложность действия равна `n − m`» — `m` is undefined.
   Read `n − k`, `k = dim T`. Load-bearing: the whole thesis is about positive complexity.
2. **Определение 18 (Chow ring).** Two deviations from Adiprasito–Huh–Katz: variables must
   range over **nonempty proper** flats, and `J_M` is generated by the **differences**
   `Σ_{F ∋ a} x_F − Σ_{F ∋ b} x_F` over pairs of atoms, not by the sums `Σ_{F ⊇ a} x_F`.
   Quotienting by the sums destroys `A^{r−1} ≅ Z`. Restate per AHK Def. 1.1.
3. **Теорема 2 (realizability ⇔ Chow ring of a projective variety).** *Corrected — the audit
   was wrong here.* AHK **do** prove an equivalence (arXiv:1511.02888, Thm 5.12): *there is a
   Chow equivalence from a smooth projective variety over k to X(Σ_M) iff M is realizable over
   k*, where a Chow equivalence is a morphism inducing an isomorphism of Chow rings (Def. 5.11).
   The original's attribution to [13] was right. Its paraphrase dropped "induced by a
   morphism", and that is the only thing to fix. Applied: v2 Theorem 2.31 states Thm 5.12
   exactly, with Feichtner–Yuzvinsky for the realizable direction.
4. **Предложение 3 (Euler characteristic).** `χ(ord(ℒ∖{0̂,1̂})) = |µ(0̂,1̂)| + 1` holds only in
   even rank. The order complex is a wedge of `|µ(0̂,1̂)|` spheres of dimension `r − 2`, so
   `χ̃ = (−1)^r |µ(0̂,1̂)| = µ(0̂,1̂)` (Philip Hall). State it reduced. The Mayer–Vietoris step
   in the proof is unnecessary — the wedge-of-spheres conclusion gives the Betti numbers.
5. **Boolean expansion after Определение 12.** `Σ_{A ⊆ M} µ(0̂,A) t^{r(E)−r(A)}` is ill-formed
   (`µ` lives on flats). Whitney: `χ_M(t) = Σ_{A ⊆ E} (−1)^{|A|} t^{r(E)−r(A)}` for loopless `M`.
6. **Конструкция 5 / Теорема 3 (cocircuit matrix, Kapranov rank).** The matrix is declared over
   `F₂`, but it is a real 0/1 matrix. *Corrected against the source*: the original's 0/1
   convention is **right** (Develin–**Santos**–Sturmfels, *On the rank of a tropical matrix*,
   Def. 7.1; the audit had the wrong author list and wrongly suspected the convention). The
   theorem is DSS Prop. 7.2 + Thm 7.3: Kapranov rank of `C(M)` over `k` equals `r(M)` ⇒ `M`
   realizable over `k`, with the converse for infinite `k`. Kapranov rank is defined *over a
   field* via Puiseux series (DSS Def. 3.9).
7. **Определение 19 (realization).** `(r+1)`-dimensional → `r`-dimensional, and quantify the
   biconditional: *for every* `S ⊆ E`, `S ∈ ℐ ⟺ {v_i : i ∈ S}` independent.
8. **Теорема 5 proof (main theorem, exposition).** Replace the hyperplane-arrangement detour
   by the unique-factorization argument: in `Q[t₁,…,t_k]` the principal ideal `(∏_j α_j)`
   determines the **multiset** `{α_j}` up to units, which is exactly the linear matroid of
   weights *with* multiplicities — the arrangement loses parallel elements. Also state the
   standing conventions (Q coefficients, isolated fixed points) and recall that weights are
   defined up to sign, the matroid being sign-blind. Deduplicate Теорема 1 = 5 = 8: state once,
   cross-reference twice.
9. **Пример 15 (`CP^n`):** `n+1` fixed points, tuple indexed by `[n+1]`, GKM graph `K_{n+1}`.
   **Пример 8:** `M·V_i ⊂ V_{h(i)}`, and `Hess(M,h)^T = Sₙ` needs `M` regular semisimple
   (currently implicit). **Лемма 1:** the target is the one-skeleton / a sum over corank-1
   subtori; cite Chang–Skjelbred (Ann. Math. 100 (1974)).
10. **Пример 20.** «сильно больше, чем n(n−1)/2, поскольку мы не факторизуем по симплициальным
    цепям старшей размерности» is not a well-formed statement. Either compute the top Betti
    number of `ord(Cl(Cₙ)∖{1̂})` (polymake, `n = 3,4,5`) or replace by a proved inequality.
11. **Terminology and typos.** Fix «лист»/«флэт»/«флет» to one word; `T_x` (stabilizer) vs
    `T_x X` (tangent space) notation clash — rename the stabilizer `St(x)`; Пример 4 «булева
    решетка `F₂^{n−1}`» → `B_{n−1}`; the spelling list in the audit (§C.9); renumber theorems on
    merge.
12. **Bibliography.** `[1]` → IMRN 2024 no. 3, 1931–1967, doi:10.1093/imrn/rnad076; `[13]` →
    Ann. of Math. 188 (2018), no. 2, 381–452; pin `[3]` (Sbornik) and `[9]` (Springer, 2020);
    `[14]` University of Michigan; delete the `[18] To be continued` placeholder. Add:
    Speyer–Sturmfels (Adv. Geom. 4 (2004)) for Теорема 9; Ardila–Klivans (JCTB 2006) for the
    Bergman fan's flat-chain structure used in Определение 17; Brandt–Eur–Zhang (Adv. Math. 384
    (2021)); Feichtner–Yuzvinsky (2004); Gelfand–Goresky–MacPherson–Serganova (1987);
    Chang–Skjelbred (1974).

**Artifact (delivered).** `docs/thesis-v2/thesis_en.{tex,pdf}` (the original LaTeX source was
not available, so v2 is a newly written English source), plus `docs/thesis-v2/CHANGES.md`
mapping every change to its audit item.

---

## Track C — Reframe Вопрос 2 (tropical flags)  ⏸ **frozen: kill criterion met**

*Status:* the reframed question is in v2 §5 (Question 3). The experiment was run, with gfan
instead of polymake (`experiments/tropical_flags/`), and hit the kill criterion. Modulo
lineality, `trop Flₙ` has dimension `(n−1)(n−2)/2`, the complexity of the action, while
`Cl(Kₙ)` has rank `n−1`, the torus rank, so no rank-preserving map exists for n ≠ 4. At
n = 4 (f-vector (1,20,79,78) against (24,72,34,1)) the counts rule out injections and
surjections in both orientations. A meaningful version needs a geometric correspondence;
see `RESULTS.md` there.

**Target.** Replace the literal question («is there a reasonable description of
`trop Fl(Cⁿ)`?»), which was already answered before the thesis was written, by a question this
thesis's viewpoint is the natural one to ask.

**What is known.** Brandt–Eur–Zhang, *Tropical flag varieties* (Adv. Math. 384 (2021) 107695,
arXiv:2005.13727) introduce the flag Dressian and prove the four-way correspondence (flag
Dressian points ↔ valuated flag matroids ↔ flags of tropical linear spaces ↔ coherent
flag-matroidal subdivisions), with realizability settled up to `|E| = 5` and a counterexample
at `6`; `FlDr(n) ⊋ trop Fl(n)` in general. Follow-ups: Haque (2012), Boretsky
(arXiv:2111.12587, arXiv:2208.09128) on the totally nonnegative part, Joswig–Loho–Luber–Olarte
(IMRN 2023), Boretsky–Eur–Williams (flag positroids).

**New formulation.** Compare the face poset `S(Fl(Cⁿ)) = Cl(Kₙ)` (the cluster-permutohedron of
the complete graph, Предложение 6) with the fan/poset structure of `FlDr(n)`: does the
cluster-permutohedron embed as, or map onto, the face poset of a subfan of the flag Dressian?
The local pieces `S(X)_{⩾pt}` are Bergman fans of the local matroids, so a positive answer
would be a local-to-global statement rather than a coincidence.

**Atomic experiment.** For `n = 3, 4`: compute `Cl(Kₙ)` and the face poset of `FlDr(n)` in
polymake (`a-tint`/`Polymake::tropical`), and test for a rank-preserving poset map.
**Kill criterion.** No such map at `n = 4` with any natural labelling ⇒ record the obstruction
and freeze the track. **Artifact.** Revised Вопрос 2 plus a literature paragraph.

---

## Track D — Вопрос 1: does `S(X)` determine the Betti numbers?  ✅ **proved for type A: all full and partial regular semisimple Hessenberg varieties, all n**

*Status (proof):* `experiments/question1/PROOF.md`, written into thesis v2 as Theorems 4.33 and 4.35 (full proof of 4.35 in Lemmas 4.36–4.38)
and Corollary 4.34. **Theorem A:** `Cl_Γ ≅ Cl_Γ'` ⇒ `Γ ≅ Γ'` for all simple graphs. The number of
minimal elements below the join of two atoms is 6 for adjacent edges and 4 for disjoint ones, so
the poset recovers the line graph, and Whitney's theorem recovers `Γ`. Rank separates `K_3` from
`K_{1,3}`. Conjugation by a permutation matrix then gives `M_{Γ,λ} ≅ M_{Γ',λ}`, so Вопрос 1 is
answered **yes** for isospectral manifolds and for all regular semisimple Hessenberg varieties,
even without `H^odd = 0`. **Partial flags:** the same count gives 3 vs 6, which recovers the
inflated graph together with its parts (Whitney–Jung for components with ≥ 5 vertices, a finite
check for the rest). The fibration `Hess(h̃) → Hess_k̄(h)` with fibre `∏ Fl(k_a)` reduces the
Betti numbers to the full case. Machine checks: exact poset isomorphism classes (nauty Traces) for all 208
graphs with n ≤ 6, the fibration identity for 2,949 cases with n ≤ 7, and the small components.
Open: other Lie types, and a Lean proof of Theorem A (needs Whitney's line-graph theorem).

*Status (computations, before the proof):* for regular semisimple Hessenberg varieties with n ≤ 7 (714 functions) the answer is
**yes**, rigorously: the face poset `Cl(Γ_h)` determines `Γ_h` up to isomorphism (its cover
invariants separate all 151 graph classes at n = 7), and isomorphic graphs give equal Betti
numbers (`experiments/question1/`). Partial Hessenberg varieties (2,940 cases with n ≤ 7,
including `Gr(2,4)`, `Gr(2,5)`, `Gr(3,6)` and all partial flag varieties) also answer yes.
That family is far less rigid (2,218 cases at n = 7 share only 577 invariant classes), but
the Betti numbers still agree in every class. A counterexample would have to come from
outside type A; alternatively, the evidence suggests trying to *prove* that the face poset
determines the Betti numbers.

**Target.** Theorem or counterexample for: `H^odd(X_i) = 0` and `S(X₁) ≅ S(X₂)` ⇒
`β_j(X₁) = β_j(X₂)`. **Prerequisite:** Track A, whose data answers the *local* version; Вопрос 1
is the global-poset version and is not settled by it. (Checked: the Track A witness pair has
non-isomorphic global posets — `Cl(Γ_h)` has 200 vs 190 rank-2 elements — so it gives no
information here; `experiments/cluster_permutohedra/compare_witness_posets.py`.) The
complexity-zero warm-up is now written up in v2 after Question 1, together with the observation
that the *converse* of the thesis's original "⟺" fails already in complexity zero.

**Atomic experiment.** (i) Write the complexity-0 warm-up: for a quasitoric manifold the face
poset is the face poset of the orbit polytope, which determines the `h`-vector, so the answer
is yes — this belongs in the text regardless. (ii) Test complexity 1 on `Gr(2,4)`
(Buchstaber–Terzić data) against a candidate with the same poset. (iii) Sweep the isospectral
family `X_{G,λ}` via `Cl(G)`: a pair of graphs with isomorphic cluster-permutohedra and
different Betti numbers settles it negatively.

**Kill criterion.** Such a pair found ⇒ the question becomes a classification question («which
extra data does `S(X)` need?») and the track reformulates rather than continues. **Payoff.** The
thesis's own open problem, resolved either way. **Artifact.** Standalone note.

---

## Track E — Oriented matroids from invariant stably complex structures

**Target.** When `X` carries a `T`-invariant stably complex structure the weights have
well-defined signs, so `S(X)_{⩾pt}` refines to an **oriented** linear matroid; the thesis
explicitly discards signs (§3.2, Заключение). Determine whether the refinement carries
information the underlying matroid does not.

**Atomic experiment.** Write the oriented weight matroid of `CP^n` and `Fl(C³)` at every fixed
point; test whether reorientation classes separate fixed points that the underlying matroid
identifies. **Kill criterion.** Reorientation class constant across fixed points for every
tested `X` ⇒ the refinement is vacuous on this class and the track freezes. **Payoff.** A
genuinely new invariant, connecting to oriented tropical geometry (Celaya–Loho–Yuen).
**Artifact.** Definitions + examples section, seed of a paper.

---

## Track F — The Chow-ring direction, correctly aimed

Track A shows `A*(M)` does *not* see `H*_T`. The productive question is therefore: **which
quotient of the equivariant data is matroid-invariant?** Candidates from the post-2018
literature: the augmented Chow ring; intersection cohomology of matroids and Kazhdan–Lusztig
polynomials (Braden–Huh–Matherne–Proudfoot–Wang); stellahedral K-theory (Eur–Huh–Larson).

**Atomic experiment.** Compute `IH(M)` and the augmented `A*(M)` for the local matroids of the
Track A pair, then test whether the global poset `S(X)` glues the local augmented Chow rings
into an object of the size of `H*_T(X)` — a sheaf on `S(X)` in the Braden–MacPherson sense.
**Kill criterion.** The dimension count already fails for `CP²`. **Payoff.** This is the natural
next theorem after Теорема 1: local-to-global matroid invariants on the face poset.

---

## Track G — Formal verification (Lean 4 / Mathlib)  ◐ **G1–G4 proved (`formal/`)**

*Status:* Lean 4.36.0-rc1 with Mathlib `625d8914` (2026-10-16). **G1** (`vectorMatroid`, the
linear matroid of a finite family of vectors) and **G2** (`span_prod_eq_iff`) are proved, with
no `sorry` and only the standard axioms. The re-survey found that Mathlib now has
`MvPolynomial.irreducible_of_totalDegree_eq_one`, which is exactly G2a, so G2 took about 40
lines. **G3** (`formal/Formal/FlatLattice.lean`, about 260 lines) is done for matroids on any
type, with no finiteness assumption. `Flats M` is a `CompleteLattice`, in which meet is
intersection, join is the closure of the union, `⊥` is the set of loops and `⊤` is the ground
set. Rank is submodular. `F ⋖ G` iff `G = cl(F ∪ {e})` for some `e ∉ F`, and covers raise the
rank by exactly 1. The lattice has `IsUpperModularLattice` and `IsAtomistic` instances, which
makes it geometric in finite rank. **G4** (`formal/Formal/CharPoly.lean`) is done too. It defines
`charPoly M = ∑_F μ(⊥,F) X^{r(E)−r(F)}` with Mathlib's `IncidenceAlgebra.mu` on `Flats M`, and
proves Whitney's Boolean expansion for loopless matroids on a finite type by grouping subsets by
their closure and applying Möbius inversion. This repairs Track B item 5 in machine-checked form.
`Flats M` is now a `def` rather than an `abbrev`, so the subtype order no longer competes with the
lattice order. Next: G5 (Philip Hall) and G7. G3 and G4 are candidates for upstreaming to
Mathlib.

The Mathlib survey behind this track is in `docs/lean-formalization-feasibility.md`; that file
records what exists today, file by file. This section is the actionable list: what can be
formalized, in what order, and what each item buys.

**The verdict in one line.** The main theorem *as stated* is out of reach — equivariant
cohomology, the Borel construction, excision, the LES of a pair, equivariant Euler classes and
the slice theorem are all absent from Mathlib, and singular cohomology does not exist at all
(singular *homology* arrived recently and consists of the chain-complex functor, `H₀`, and
homotopy invariance). But the thesis's main theorem factors into a topological half and an
algebraic half, and **the algebraic half — the part the thesis itself states loosely — is
fully formalizable today.** That is the arc worth pursuing: G1 → G2 → G7 gives a
machine-checked proof of everything in Теорема 5 downstream of the GKM theorem.

### The core arc

**G1 — The linear matroid of a family of vectors.** *(prerequisite for most of the rest)*
Build `Matroid.ofVectors : (ι → V) → Matroid ι` from `LinearIndepOn`, via the augmentation
axiom in `Matroid/IndepAxioms.lean`. Mathlib has a mature `Matroid` API but **no vector
matroid**, which is the one object this whole thesis is about (Определение 19, once repaired
per Track B item 7). Self-contained, upstreamable, useful far beyond this project.
*Estimate 300–600 lines. Kill criterion: none — if it turns out to be in flight upstream,
adopt that version instead (check the Mathlib PR queue first).*

**G2 — The unique-factorization step of Теорема 5.** *(the mathematical heart)* Over a field
`k`, the principal ideal `(∏ⱼ αⱼ) ⊆ k[t₁,…,t_k]` determines the multiset `{αⱼ}` up to units —
hence determines the linear matroid of weights **including multiplicities**. This is exactly
Track B item 8: the thesis detours through a hyperplane arrangement, which loses parallel
elements, where the ideal itself does not.

```lean
-- sketch; the statement is the deliverable, the proof follows
theorem span_prod_eq_iff (α β : Multiset (MvPolynomial σ k))
    (hα : ∀ p ∈ α, p.totalDegree = 1) (hβ : ∀ p ∈ β, p.totalDegree = 1) :
    Ideal.span {α.prod} = Ideal.span {β.prod} ↔ Multiset.Rel Associated α β
```

Ingredients present: `MvPolynomial.uniqueFactorizationMonoid`,
`UniqueFactorizationMonoid.factors_unique`, `Ideal.span_singleton_eq_span_singleton`. The one
lemma to prove from scratch is **G2a**: a nonzero form of total degree 1 is irreducible in
`MvPolynomial σ k` — a short degree argument. With G1, state the corollary in matroid terms:
the ideal determines `Matroid.ofVectors α` up to isomorphism.
*Estimate 200–400 lines. Payoff: the vaguest sentence in the thesis becomes machine-checked.*

**G7 — GKM-as-definition, and Предложение 5.** Define, for a finite weighted graph `(G, α)`
over `R = k[t₁,…,t_k]`, the module of graph functions

```lean
def gkmRing (G : SimpleGraph V) (α : G.edgeSet → R) : Submodule R (V → R) :=
  { f | ∀ e ∈ G.edgeSet, f e.1 - f e.2 ∈ Ideal.span {α e} }
```

and prove Предложение 5 in that setting: for the two-vertex, `n`-edge graph (the compactified
tangent representation `S^{2n}`), the relative object is the principal ideal `(∏ⱼ αⱼ)`. This is
pure module theory over a polynomial ring — precisely what the Macaulay2 computation in
`experiments/counterexample/` did numerically. Composed with G2 it yields: **the local
equivariant cohomology of a GKM manifold at a fixed point determines the weight matroid with
multiplicities**, formally, with the GKM theorem (Теорема 4) as an explicit axiom rather than a
verified result. *Estimate 400–800 lines. The boundary must be labelled in the write-up: what
is verified is the algebra, not that this ring is the equivariant cohomology of a manifold.*

### Formalizing the repaired background section

These three correspond one-to-one with Track B repairs, which is the honest place for formal
verification to add value here — the background section is where the thesis's actual errors are.

**G3 — Lattice of flats; geometric lattices.** Put a `Lattice` (ideally `CompleteLattice`)
instance on `{F // M.IsFlat F}`; define `GeometricLattice` (graded, atomistic, semimodular) and
instantiate it on the flats of a finite matroid. Mathlib has `Matroid.IsFlat` as a *predicate*
only — no lattice instance — plus `Order/Atoms` and `IsModularLattice` to build on. This is the
prerequisite for G4, G5 and G6, and is upstreamable on its own. *Estimate 400–800 lines.*

**G4 — Characteristic polynomial and Whitney's Boolean expansion.** *(repairs Track B item 5)*
Define `χ_M(t) = Σ_{F ∈ ℒ_M} µ(0̂,F) t^{r(E)−r(F)}` using `IncidenceAlgebra.mu` on the flat
lattice from G3, then prove `χ_M(t) = Σ_{A ⊆ E} (−1)^{|A|} t^{r(E)−r(A)}` for loopless `M` by
Möbius inversion along the closure map. The thesis's version sums `µ(0̂,A)` over arbitrary
subsets, which is ill-formed — `µ` lives on flats. *Estimate 300–600 lines on top of G3.*

**G5 — Philip Hall, combinatorial form.** *(repairs Track B item 4)* Prove
`µ(0̂,1̂) = Σ_i (−1)^i cᵢ`, where `cᵢ` counts `i`-chains in `ℒ∖{0̂,1̂}`. This is a Möbius-algebra
identity, formalizable today, and it delivers the corrected Предложение 3 — `χ̃ = µ(0̂,1̂)` with
the sign `(−1)^r` — **without** needing the topological reading. The wedge-of-spheres route
needs shellability and simplicial homology and stays out of scope. *Estimate 300–500 lines on
top of G3. Kill criterion: none; the combinatorial route is known to work.*

### Reach

**G6 — The combinatorial core of Теорема 7.** Stated linear-algebraically, with the slice
theorem as a hypothesis rather than a goal: for weights `α : ι → Qᵏ`, the poset of subspaces
`{V^H}` ordered by inclusion is isomorphic to the lattice of flats `ℒ_α` via orthogonal
complement. Replacing closed subgroups of `T` by subspaces of the character lattice makes this
formalizable, and it is the honest way to verify Теорема 7, whose geometric input is entirely
in the slice theorem. *Depends on G1 and G3. Estimate 600–1000 lines.*

**G8 — The Track A counterexample in Lean.** *(stretch; do not schedule)* With G7 the Betti
numbers of the witness pair are *definable* as the Hilbert function of the GKM module, so the
counterexample becomes a statement Lean can express: two explicit weighted graphs with
isomorphic local matroids and different Hilbert functions. Expressing it is not proving it —
Mathlib has no Gröbner bases and no Hilbert-series machinery, and a 120-vertex kernel dimension
count is not going to fall to `decide`. The matroid half (an explicit bijection between two
6-element ground sets, checked finitely) is reachable; the Hilbert-function half is not.
*Kill criterion: if the `n = 4` pair (24 vertices, 24 edges) cannot be evaluated, abandon —
do not build Gröbner bases for this.*

### Explicitly out of scope

Теорема 1/5/8 as stated, Предложение 4 (equivariant formality), Лемма 1 (Chang–Skjelbred), the
GKM theorem itself, and the topological reading of Предложение 3. Each needs foundations that
do not exist: singular cohomology with cup products, relative cohomology and the LES of a pair,
excision, the Borel construction, equivariant Euler classes, Bredon's slice theorem. That is a
multi-year, multi-person foundational program on the scale of the Liquid Tensor Experiment, and
attaching it to this thesis would be a category error.

### Ordering and setup

`G1 → G2` first (small, self-contained, closes the thesis's own exposition gap), then `G3 → G4,
G5` (the repaired background section), then `G7` (which needs only G2), then `G6`. Pin Mathlib
to a fixed commit in `lakefile.lean` — the `Matroid` API is under active development — and work
in a `lean/` subdirectory. State every target as `theorem … := by sorry` first, so the
*statements* can be reviewed independently of the proofs; a wrong statement proved correctly is
the standard failure mode of a formalization project. G1 and G3 should be offered upstream
rather than kept local.

---

## Schedule

| Window | Items | Gate to the next window |
|---|---|---|
| Days 1–30 | ✅ Track A section; ✅ Track B (all 12 items, in the English v2); ◐ Track C (text done, experiment open) | done |
| Days 31–60 | Track B items 9–12 (v2 of the text); Track G items G1, G2 | v2 compiles; `span_prod_eq_iff` proved, `Matroid.ofVectors` offered upstream |
| Days 61–90 | Track D warm-up + complexity-1 test; Track E examples | Q1 resolved or reformulated |
| Beyond | Track F; Track G items G3–G5 (then G7, G6); flag-Dressian poset map | Gated on the kill criteria above |

## Paperability

After the 30-day items the publishable core is: Теорема 1, now with a correct proof that
covers weight multiplicities (Thom isomorphism plus unique factorization), and the
counterexample (Track A).

*Correction to the first draft of this section:* Пример 18 (partial Hessenberg
cluster-permutohedra) is **not** new. Ayzenberg–Buchstaber already cover it in
arXiv:2203.14133 / IMRN 2024, §5 (Construction 5.13, Theorem 2), and their Cor. 3.2 covers full
Hessenberg varieties. The audit's "appears to be new" was wrong, and v2 attributes it.

The core is therefore thinner than first estimated: one theorem, whose substance is a careful
version of a standard argument, and one computer-verified example. It reads as a short note
rather than a paper. Working title: *Local equivariant cohomology and matroids of weights of
torus actions*. Tracks E and F are what would make it a paper.

## Risk register

| Risk | Where it bites | Mitigation |
|---|---|---|
| ~~The Shareshian–Wachs count is misapplied~~ | Track A | **Retired.** The Macaulay2 GKM recomputation is independent of that formula and agrees on every case |
| A referee dismisses a disconnected witness | Track A write-up | The published pair is connected (`Fl(C⁵)`, `h = (2,3,5,5,5)` vs `(2,4,4,5,5)`); the disconnected pairs appear only as remarks |
| ~~Feichtner–Yuzvinsky restatement changes what Теорема 2 is used for downstream~~ | Track B item 3 | **Retired**: no restatement was needed (the audit was wrong; AHK Thm 5.12 is the iff) |
| Ayzenberg–Cherepanov `[2]` still unpublished at resubmission | Track B item 12 | Re-check for a journal version before the bibliography freeze |
| Mathlib refactors the `Matroid` API mid-effort | Track G | Pin a Mathlib commit in `lakefile`; the Tier 1 targets touch few files |
