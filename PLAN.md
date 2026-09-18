# Development plan

Derived from `audit/matroid_torus_thesis_audit.md` (CP3 fix table + CP4 program) and from a
re-reading of the thesis text. Each track states: **target**, **prerequisite**, **atomic
experiment**, **kill criterion**, **payoff**, **artifact** — the audit's own template.

Ordering principle: Track A closes the one `MAJOR GAP`, Track B makes the text defensible,
and both are prerequisites for everything downstream. Tracks C–F are research; Track G
(formalization) runs in parallel and is scoped in `docs/lean-formalization-feasibility.md`.

---

## Track A — Close the MAJOR GAP: the unproved corollary

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
reduces the search to a finite graph-theoretic condition and is what makes the experiment
a one-afternoon computation rather than a search.

**Candidate witness W1 (to verify, not yet proved).** Both inside `Fl(C⁶)` with the same
`T⁶`-action and the same 720 fixed points:

| | `X₁` | `X₂` |
|---|---|---|
| Hessenberg function | `h₁ = (3,3,3,6,6,6)` | `h₂ = (3,3,5,5,5,6)` |
| `G_h` | two disjoint triangles `{1,2,3}`, `{4,5,6}` | triangles `{1,2,3}`, `{3,4,5}` glued at `3`; vertex `6` isolated |
| edges / complex dimension | 6 | 6 |
| graphic matroid | `U_{2,3} ⊕ U_{2,3}` | `U_{2,3} ⊕ U_{2,3}` |

Vertex identification does not change the cycle matroid, so the two local matroids agree
(rank 4 on 6 elements, both `U_{2,3} ⊕ U_{2,3}`), hence `A*(M₁) ≅ A*(M₂)` and
`OS(M₁) ≅ OS(M₂)` at every fixed point. Both actions are GKM (regular semisimple Hessenberg
varieties are smooth with `H^odd = 0`), so equivariant formality gives
`H*_T(X) ≅ H*(X) ⊗ Sym(t*)` as a module and it suffices to separate the ordinary Betti
numbers.

*Hand estimate of the separating invariant.* By Shareshian–Wachs, the Poincaré polynomial of
a regular semisimple Hessenberg variety is `Σ_{w ∈ Sₙ} q^{2·inv_{G_h}(w)}`, so the top Betti
number is the number of `w` inverting **every** edge of `G_h`. For `X₁` that means choosing a
linear order inside each triangle independently: `6!/(3!·3!) = 20`. For `X₂` the two triangles
share a vertex, so the constraints concatenate into a single chain on 5 vertices with one free
vertex: `6`. **20 ≠ 6** ⇒ `β_top(X₁) ≠ β_top(X₂)` ⇒ `H*_T(X₁) ≇ H*_T(X₂)`.

This is a pencil computation and must be confirmed by machine before it is written down as a
theorem; the inversion-counting convention (which of `<`/`>` counts, and the `q` vs `q²`
grading) is exactly the kind of thing that flips a factor.

**Atomic experiment.**
1. Enumerate Hessenberg functions for `n = 4,5,6`; build `G_h`; compute `M(G_h)` and bucket by
   matroid isomorphism class (`polymake`/`sage`, or a 40-line Python matroid-isomorphism check
   on such small ground sets).
2. Within each bucket compute Poincaré polynomials two independent ways: the GKM presentation
   of Пример 17 (Macaulay2 + `AntonAyzenberg/GKM-homology`) and the chromatic quasisymmetric
   function / `inv_{G_h}` count. They must agree; disagreement means the convention is wrong,
   not the mathematics.
3. Confirm W1 specifically, and report the full matroid-matched / Betti-mismatched table.

**Kill criterion.** No matroid-matched, Betti-mismatched pair for `n ⩽ 6` (i.e. W1 fails on
inspection and nothing replaces it) ⇒ fall back to `Gr(2,n)` versus a partial Hessenberg
variety, or drop equivariant formality; if that also fails, the corollary must be retracted
from the abstract rather than restated.

**Payoff.** The thesis's second declared result becomes a proved statement, with a witness
that is small enough to print in full.

**Artifact.** `experiments/counterexample/` — enumeration script, `counterexample.m2`, the
matroid-class table, and a one-page section for the thesis text.

**Note for the write-up.** If only a cross-dimensional witness survives (e.g. `h = (3,3,5,5,5)`
in `Fl(C⁵)` against `h₁` above in `Fl(C⁶)`), it still proves the claim but invites the objection
that the acting torus differs; prefer the equal-`n` pair W1 and mention the other as a remark.

---

## Track B — Errata pass (thesis v2)

Each item below is a specific replacement, in priority order (audit CP3 items 2–8, 10 plus
the local fix-list). None of them requires new mathematics.

1. **Определение 22 (complexity).** «сложность действия равна `n − m`» — `m` is undefined.
   Read `n − k`, `k = dim T`. Load-bearing: the whole thesis is about positive complexity.
2. **Определение 18 (Chow ring).** Two deviations from Adiprasito–Huh–Katz: variables must
   range over **nonempty proper** flats, and `J_M` is generated by the **differences**
   `Σ_{F ∋ a} x_F − Σ_{F ∋ b} x_F` over pairs of atoms, not by the sums `Σ_{F ⊇ a} x_F`.
   Quotienting by the sums destroys `A^{r−1} ≅ Z`. Restate per AHK Def. 1.1.
3. **Теорема 2 (realizability ⇔ Chow ring of a projective variety).** Not an AHK statement;
   AHK's point is that `A*(M)` satisfies the Kähler package *regardless* of realizability, and
   `A*(X(Σ_M)) = A*(M)` holds for every `M`. Restate as the Feichtner–Yuzvinsky (Invent. Math.
   155 (2004)) forward direction — for realizable `M`, `A*(M)` is the Chow ring of the
   de Concini–Procesi wonderful compactification — and delete the converse unless sourced.
4. **Предложение 3 (Euler characteristic).** `χ(ord(ℒ∖{0̂,1̂})) = |µ(0̂,1̂)| + 1` holds only in
   even rank. The order complex is a wedge of `|µ(0̂,1̂)|` spheres of dimension `r − 2`, so
   `χ̃ = (−1)^r |µ(0̂,1̂)| = µ(0̂,1̂)` (Philip Hall). State it reduced. The Mayer–Vietoris step
   in the proof is unnecessary — the wedge-of-spheres conclusion gives the Betti numbers.
5. **Boolean expansion after Определение 12.** `Σ_{A ⊆ M} µ(0̂,A) t^{r(E)−r(A)}` is ill-formed
   (`µ` lives on flats). Whitney: `χ_M(t) = Σ_{A ⊆ E} (−1)^{|A|} t^{r(E)−r(A)}` for loopless `M`.
6. **Конструкция 5 / Теорема 3 (cocircuit matrix, Kapranov rank).** The matrix is declared over
   `F₂`, but Kapranov rank is defined for matrices over the tropical semiring `R ∪ {∞}`; the
   Develin–Sturmfels cocircuit matrix is a real 0/1 matrix. Fix the field, verify the 0/1
   convention against Maclagan–Sturmfels Ch. 5, cite Develin–Sturmfels *On the rank of a
   tropical matrix*.
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

**Artifact.** `docs/thesis-v2/` with the corrected source, plus `docs/errata.md` mapping every
change to its audit item.

---

## Track C — Reframe Вопрос 2 (tropical flags)

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

## Track D — Вопрос 1: does `S(X)` determine the Betti numbers?

**Target.** Theorem or counterexample for: `H^odd(X_i) = 0` and `S(X₁) ≅ S(X₂)` ⇒
`β_j(X₁) = β_j(X₂)`. **Prerequisite:** Track A, whose data answers the *local* version; Вопрос 1
is the global-poset version and is not settled by it.

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

## Track G — Formal verification (Lean 4 / Mathlib)

Scoped in `docs/lean-formalization-feasibility.md`. Summary of the verdict: the matroid and
commutative-algebra layers are formalizable today; the equivariant-topology layer is not, and
will not be for years. The valuable near-term target is **Track B item 8** — the
unique-factorization step of the main theorem — which is the mathematical heart of Теорема 5
and is fully within reach of current Mathlib.

---

## Schedule

| Window | Items | Gate to the next window |
|---|---|---|
| Days 1–30 | Track A (verify W1 + full table); Track B items 1–8; Track C reframing | A closed or explicitly killed |
| Days 31–60 | Track B items 9–12 (v2 of the text); Track G Tier 1 | v2 compiles; Lean Tier 1 target stated and proved |
| Days 61–90 | Track D warm-up + complexity-1 test; Track E examples | Q1 resolved or reformulated |
| Beyond | Track F; Track G Tier 2; flag-Dressian poset map | Gated on the kill criteria above |

## Paperability

After the 30-day items the publishable core is: Теорема 1 + the computed counterexample
(Track A) + the cluster-permutohedron description of partial Hessenberg varieties (Пример 18,
which appears to be new relative to Ayzenberg–Buchstaber and is currently only sketched —
it should be stated as a proposition with proof). Working title: *Local equivariant cohomology
and matroids of weights of torus actions*. Tracks E and F are the sequel.

## Risk register

| Risk | Where it bites | Mitigation |
|---|---|---|
| W1 fails on the convention check | Track A, the whole 30-day window | Two independent computations (GKM presentation vs. `inv_{G_h}`) are mandated in the protocol; full `n ⩽ 6` sweep runs regardless of W1 |
| Cross-dimensional witness only | Track A write-up | Stated as a remark, not the theorem; equal-`n` pair preferred |
| Feichtner–Yuzvinsky restatement changes what Теорема 2 is used for downstream | Track B item 3 | Теорема 2 is cited nowhere else in the thesis; the edit is local |
| Ayzenberg–Cherepanov `[2]` still unpublished at resubmission | Track B item 12 | Re-check for a journal version before the bibliography freeze |
| Mathlib refactors the `Matroid` API mid-effort | Track G | Pin a Mathlib commit in `lakefile`; the Tier 1 targets touch few files |
