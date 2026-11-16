# Independent read of §5.2 (partial Hessenberg varieties)

Scope: §5.2 of `paper.tex` (Theorem 5.8 and Lemmas 5.7, 5.9–5.11), the parts of §2.2 and §5.1 it
uses, and the two citations it rests on. Lemma and theorem numbers are those of the PDF built
from this commit.

How it was done: every step of the proofs was rederived by hand; the two cited statements were
read in the arXiv sources (Ayzenberg–Buchstaber, arXiv:2203.14133v2 and arXiv:1803.01132v2); and
`experiments/question1/independent_check.py`, written for this read without using the earlier
scripts, recomputes the statements (`independent_check.log`).

**Verdict.** Theorem 5.8 and its proof are correct. One claim next to it, in Corollary 5.6, was
stronger than what the cited theorem gives, and has been corrected. Four places were unclear or
leaned on the source more than a referee would accept; they are rewritten. Nothing in Theorem C
changes except the wording of part (2).

## Findings

| # | Where | Finding | Severity | Action |
|---|---|---|---|---|
| 1 | Cor. 5.6, Thm C(2), Thm 2.3 | "`H*_T(X) ≅ H*_T(X')` up to an automorphism of `T`" is not justified when one of `X`, `X'` is a Hessenberg variety and the other an isospectral manifold. The twin theorem (AB21, Thm 3.11) gives an isomorphism of graded rings only; its proof twists `H*(BT)` by a different permutation at each fixed point. The weights already show that no algebra isomorphism can exist in general: at `w`, the isospectral manifold has weights `t_i − t_j` and the Hessenberg variety `t_{w(i)} − t_{w(j)}`. | wrong as stated | Statement corrected to "as graded rings"; added that for two Hessenberg varieties it is an isomorphism of `H*(BT)`-algebras (short GKM argument, now in the proof), and for two isospectral manifolds one up to an automorphism of `T`. The same sentence is corrected in thesis v2 (Corollary 4.37). |
| 2 | §5.2, first paragraph | The face poset was quoted as "[AB24, Thm 2]", but that theorem states the poset as an identification space `Flats(Γ(k̄)) ×_Λ [n choose k̄]`, with a bicoset notation that does not literally produce the right poset (read literally it gives 4 one-dimensional faces for `CP²`). The correct description, by blocks with part counts, is the one in the *proof* of AB24, and that proof leaves injectivity "as an exercise". The paper's description was right, but "each block induces a connected subgraph of the inflation" was ambiguous, since blocks are sets of labels and the inflation is a graph on positions. | gap in exposition | New Lemma 5.7 states the description precisely and proves it in full (fixed sets of subtori split as products of smaller partial Hessenberg varieties; a component is a face exactly when its weights span). Check A below confirms it against faces computed from the GKM graph alone. |
| 3 | §2.2 | The paper defines the partial Hessenberg variety by `M V_{K_a} ⊂ V_{K_{h(a)}}`, AB24 by `M L_a ⊂ ⊕_{b ∈ star(a)} L_b` on orthogonal pieces. The two agree because `M` is Hermitian, but this was not said, and it is needed to apply AB24 at all. Smoothness was not stated either. | missing sentence | Both added (§2.2; smoothness in the proof of Lemma 5.10). |
| 4 | §2.2 | Sign conventions differed: full case `t_{w(i)} − t_{w(j)}` for `j < i`, partial case `t_x − t_y` for `x` in the earlier part. Harmless (formula (2.2) is invariant under the global sign by `x ↦ n+1−x`), but (2.2) "reduces to (2.1)" only with matching signs. | cosmetic | Partial weights now `t_y − t_x`. |
| 5 | Proof of Thm 5.8 | "by Corollary 5.6 and Theorem 2.3 its Poincaré polynomial depends only on `G_Q`" — the corollary is stated for isomorphic face posets, while what is used is that isomorphic connected graphs `Γ_h̃` give equal Betti numbers. True (it is the proof of the corollary), but not what the corollary says. Note the formula (2.1) alone does not give it: `Σ_w q^{inv_Γ(w)}` is not invariant under relabelling a graph (path `1–2–3`: `1+4q+q²`; path `1–3–2`: `2+2q+2q²`). The twin argument is really needed. | imprecise reference | Reworded to say exactly this. |

## Steps checked and found correct

- **Lemma 5.9 (splitting).** Components of `Γ_h` are intervals of parts; the pairs counted by
  `ind(J)` lie inside components; the multinomial count and the specialization `q = 1` are right.
- **Lemma 5.10 (fibration).** `h̃` is a Hessenberg function; `π⁻¹(X) = Hess(M, h̃)` because for `i`
  in part `a`, `M F_i ⊂ M F_{K_a} ⊂ F_{K_{h(a)}} = F_{h̃(i)}`; Leray–Hirsch applies (the Chern
  classes of the tautological quotients restrict to generators of the fibre); the description of
  `Γ_h̃` is right.
- **Lemma 5.11 (reconstruction).** The values `ν = 3, 6, 4` follow from the formula for `ν`;
  rank separates triangles from stars; Proposition 5.3 applies; "same part ⇔ common neighbour with
  `ν = 3`" is correct in both directions, and uses that a non-isolated vertex lies in a component
  with at least two parts.
- **Proof of Theorem 5.8.** The reduction to components with at least two parts, and the fact that
  `n` need not be equal for `X` and `X'`, are handled (isolated vertices carry no information and
  contribute the factor 1).
- **Citations.** AB24 "Thm 2" is `thmMegaDescription` (second theorem of the paper); "§5" is the
  section on identification constructions; AB21 "Thm 3.11" is the twin theorem
  (`thmXYconnection`). Numbers checked against the arXiv sources, not the journal versions.

## Computer checks (`independent_check.py`, all pass)

| | Check | Range |
|---|---|---|
| A | faces computed from the GKM graph (components of the subgraphs with labels in a flat) = faces of Lemma 5.7, with ranks | all 186 pairs `(k̄, h)`, `n ≤ 5` |
| B | formula (2.2) = number of `F_q`-points of `Hess_k̄(M, h)`, counted by listing partial flags | `n = 4`, `q = 5, 7`, 72 cases |
| C | Lemma 5.10: `P_{Hess(h̃)} = P_X · ∏ [k_a]_q!` | all 2,949 pairs, `n ≤ 7` |
| D | the data recovered by Lemma 5.11 determine the Poincaré polynomial | all 2,949 pairs, `n ≤ 7` (824 classes) |

## What this read does not cover

It is a second reading by a different reader, with the sources open, not a referee's report from
a specialist in toric topology. The inputs taken on trust are the twin theorem (AB21, Thm 3.11),
Ayzenberg–Cherepanov (AC22, Thm 1) and the smoothness and even cohomology of regular semisimple
Hessenberg varieties. §5.1 was read only where §5.2 uses it; Theorem 5.4 is machine-checked in
Lean in any case.
