import Formal.LocalCohomologyIdeal

/-!
# GKM rings as a definition (Track G7)

GKM theory computes the equivariant cohomology of a GKM manifold as the ring of *graph
functions* of its GKM graph: functions on the vertices whose differences along each edge are
divisible by the edge label. Mathlib has no equivariant cohomology, so here the GKM ring is the
**definition**, and everything below is pure commutative algebra.

**Boundary of what is verified.** That this ring is `H*_T(X)` for a GKM manifold `X` is the GKM
theorem (thesis Theorem 4.8), which is *not* formalized. What is verified is the algebra once
that identification is granted.

## Main definitions

* `LabelledGraph V E R` : a multigraph with vertices `V`, edges `E` and edge labels in `R`.
  Parallel edges are allowed, as they must be: the GKM graph of `S^{2n}` has `n` of them.
* `LabelledGraph.gkmRing` : the subalgebra of graph functions in `V → R`.
* `LabelledGraph.sphere α` : the GKM graph of the compactified representation `S^{2n}`, two
  vertices `0 = false`, `∞ = true` joined by `n` edges labelled `α 1, …, α n`.

## Main results

* `mem_iInf_iff_exists_gkm` : restricting the graph functions of `sphere α` that vanish at `∞` to
  the vertex `0` gives exactly the ideal `⋂ⱼ (αⱼ)`, the GKM model of `H*_T(S^{2n}, ∞)`.
* `iInf_span_eq_span_prod` : for pairwise non-associated linear forms over a field,
  `⋂ⱼ (αⱼ) = (∏ⱼ αⱼ)`. This is thesis Proposition 4.12 in the GKM setting.
* `gkm_relative_determines_weights` : combined with G2, the relative ideal of a GKM sphere
  determines its weights up to order and nonzero scalars.
* `iInf_span_ne_span_prod_of_repeated` : without pairwise independence the GKM model and the
  product differ: for the weights `(X₀, X₀)` one gets `(X₀) ≠ (X₀²)`. This is why the thesis's
  main theorem is proved through the Thom isomorphism, which sees multiplicities.
-/

open MvPolynomial

namespace MatroidToric

/-- An edge-labelled multigraph: edges `E` with endpoints in `V` and labels in `R`. -/
structure LabelledGraph (V E R : Type*) where
  /-- One endpoint of each edge. -/
  src : E → V
  /-- The other endpoint of each edge. -/
  tgt : E → V
  /-- The label (weight) of each edge. -/
  label : E → R

namespace LabelledGraph

variable {V E R : Type*} [CommRing R] (Γ : LabelledGraph V E R)

/-- The **GKM ring** of graph functions: `f : V → R` such that `label e` divides
`f (src e) - f (tgt e)` for every edge `e`. -/
def gkmRing : Subalgebra R (V → R) where
  carrier := {f | ∀ e, Γ.label e ∣ f (Γ.src e) - f (Γ.tgt e)}
  mul_mem' {f g} hf hg e := by
    have : (f * g) (Γ.src e) - (f * g) (Γ.tgt e) =
        f (Γ.src e) * (g (Γ.src e) - g (Γ.tgt e)) + g (Γ.tgt e) * (f (Γ.src e) - f (Γ.tgt e)) := by
      simp only [Pi.mul_apply]; ring
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right (hg e) _) (dvd_mul_of_dvd_right (hf e) _)
  add_mem' {f g} hf hg e := by
    have : (f + g) (Γ.src e) - (f + g) (Γ.tgt e) =
        (f (Γ.src e) - f (Γ.tgt e)) + (g (Γ.src e) - g (Γ.tgt e)) := by
      simp only [Pi.add_apply]; ring
    rw [this]
    exact dvd_add (hf e) (hg e)
  algebraMap_mem' r e := by simp

lemma mem_gkmRing {f : V → R} :
    f ∈ Γ.gkmRing ↔ ∀ e, Γ.label e ∣ f (Γ.src e) - f (Γ.tgt e) := Iff.rfl

/-- The GKM graph of the one-point compactification `S^{2n}` of a representation with weights
`α 1, …, α n`: two fixed points, `0 = false` and `∞ = true`, joined by `n` edges. -/
def sphere {n : ℕ} (α : Fin n → R) : LabelledGraph Bool (Fin n) R :=
  ⟨fun _ ↦ false, fun _ ↦ true, α⟩

/-- The graph functions on `sphere α` vanishing at `∞`, restricted to `0`, form the ideal
`⋂ⱼ (αⱼ)`: the GKM model of `H*_T(S^{2n}, ∞) → H*_T(0)`. -/
theorem mem_iInf_iff_exists_gkm {n : ℕ} (α : Fin n → R) (g : R) :
    g ∈ ⨅ j, Ideal.span {α j} ↔
      ∃ f ∈ (sphere α).gkmRing, f true = 0 ∧ f false = g := by
  simp only [Submodule.mem_iInf, Ideal.mem_span_singleton]
  constructor
  · intro h
    refine ⟨fun b ↦ if b then 0 else g, fun e ↦ ?_, rfl, rfl⟩
    simpa [sphere] using h e
  · rintro ⟨f, hf, h0, rfl⟩ j
    simpa [sphere, h0] using hf j

end LabelledGraph

variable {σ K : Type*} [Field K]

/-- If pairwise non-associated linear forms each divide `g`, so does their product. -/
theorem prod_dvd_of_forall_dvd {ι : Type*} (s : Finset ι) (α : ι → MvPolynomial σ K)
    (hlin : ∀ j ∈ s, (α j).totalDegree = 1)
    (hind : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ¬ Associated (α i) (α j))
    {g : MvPolynomial σ K} (hg : ∀ j ∈ s, α j ∣ g) : ∏ j ∈ s, α j ∣ g := by
  classical
  induction s using Finset.induction_on generalizing g with
  | empty => simp
  | insert k s hk ih =>
    rw [Finset.prod_insert hk]
    obtain ⟨h, rfl⟩ := ih (fun j hj ↦ hlin j (Finset.mem_insert_of_mem hj))
      (fun i hi j hj ↦ hind i (Finset.mem_insert_of_mem hi) j (Finset.mem_insert_of_mem hj))
      (fun j hj ↦ hg j (Finset.mem_insert_of_mem hj))
    have hirr : ∀ j ∈ insert k s, Irreducible (α j) := fun j hj ↦ irreducible_of_linear (hlin j hj)
    have hprime : Prime (α k) := (hirr k (Finset.mem_insert_self k s)).prime
    have hk' : α k ∣ (∏ j ∈ s, α j) * h := hg k (Finset.mem_insert_self k s)
    rcases hprime.dvd_or_dvd hk' with hdiv | hdiv
    · exfalso
      obtain ⟨j, hj, hkj⟩ := hprime.exists_mem_finset_dvd hdiv
      have hjk : k ≠ j := fun h ↦ hk (h ▸ hj)
      exact hind k (Finset.mem_insert_self k s) j (Finset.mem_insert_of_mem hj) hjk
        ((hirr k (Finset.mem_insert_self k s)).associated_of_dvd
          (hirr j (Finset.mem_insert_of_mem hj)) hkj)
    · rw [mul_comm (∏ j ∈ s, α j) h]
      exact mul_dvd_mul_right hdiv _

/-- **Thesis Proposition 4.12 in the GKM setting.** For pairwise non-associated linear forms
over a field (the GKM condition: weights pairwise linearly independent), the GKM model of the
relative cohomology of `S^{2n}` is the principal ideal of the product of the weights. -/
theorem iInf_span_eq_span_prod {n : ℕ} (α : Fin n → MvPolynomial σ K)
    (hlin : ∀ j, (α j).totalDegree = 1) (hind : Pairwise fun i j ↦ ¬ Associated (α i) (α j)) :
    ⨅ j, Ideal.span {α j} = Ideal.span {∏ j, α j} := by
  apply le_antisymm
  · intro g hg
    simp only [Submodule.mem_iInf, Ideal.mem_span_singleton] at hg
    exact Ideal.mem_span_singleton.mpr (prod_dvd_of_forall_dvd Finset.univ α
      (fun j _ ↦ hlin j) (fun i _ j _ hij ↦ hind hij) (fun j _ ↦ hg j))
  · refine le_iInf fun j ↦ ?_
    rw [Ideal.span_singleton_le_span_singleton]
    exact Finset.dvd_prod_of_mem α (Finset.mem_univ j)

/-- **G7 + G2.** For GKM spheres (pairwise non-associated linear weights), the relative ideal
`⋂ⱼ (αⱼ)` determines the weights up to order and nonzero scalars: two such spheres have the same
relative ideal iff their weight multisets agree up to associates. -/
theorem gkm_relative_determines_weights {n m : ℕ} (α : Fin n → MvPolynomial σ K)
    (β : Fin m → MvPolynomial σ K)
    (hα : ∀ j, (α j).totalDegree = 1) (hβ : ∀ j, (β j).totalDegree = 1)
    (hαi : Pairwise fun i j ↦ ¬ Associated (α i) (α j))
    (hβi : Pairwise fun i j ↦ ¬ Associated (β i) (β j)) :
    (⨅ j, Ideal.span {α j}) = (⨅ j, Ideal.span {β j}) ↔
      Multiset.Rel Associated (Finset.univ.val.map α) (Finset.univ.val.map β) := by
  rw [iInf_span_eq_span_prod α hα hαi, iInf_span_eq_span_prod β hβ hβi, ← span_prod_eq_iff]
  · rfl
  · simpa using hα
  · simpa using hβ

/-- Without pairwise independence the GKM model loses multiplicities: for the weights `(X₀, X₀)`,
`⋂ⱼ (αⱼ) = (X₀)` is strictly larger than `(X₀²)`. -/
theorem iInf_span_ne_span_prod_of_repeated [Nonempty σ] :
    let x : MvPolynomial σ K := X (Classical.arbitrary σ)
    (⨅ j : Fin 2, Ideal.span {(![x, x] : Fin 2 → MvPolynomial σ K) j}) ≠
      Ideal.span {∏ j : Fin 2, (![x, x] : Fin 2 → MvPolynomial σ K) j} := by
  intro x hEq
  have hx : x ∈ ⨅ j : Fin 2, Ideal.span {(![x, x] : Fin 2 → MvPolynomial σ K) j} := by
    simp only [Submodule.mem_iInf]
    intro j
    fin_cases j <;> exact Ideal.mem_span_singleton_self x
  rw [hEq, Ideal.mem_span_singleton, Fin.prod_univ_two] at hx
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one] at hx
  have hirr : Irreducible x := irreducible_of_linear (by simp [x, totalDegree_X])
  have hx0 : x ≠ 0 := hirr.ne_zero
  have : x ∣ 1 := by
    rw [← mul_dvd_mul_iff_left hx0, mul_one]
    exact hx
  exact hirr.not_isUnit (isUnit_of_dvd_one this)

end MatroidToric
