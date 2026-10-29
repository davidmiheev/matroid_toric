import Formal.FlatLattice
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Algebra.Polynomial.Eval.Defs
import Mathlib.Data.Nat.Choose.Sum

/-!
# The characteristic polynomial of a matroid (Track G4)

For a matroid on a finite type, the characteristic polynomial is defined on the lattice of flats
(`MatroidToric.Flats`, Track G3) through the Möbius function of Mathlib's incidence algebra:

  `χ_M(t) = ∑_{F flat} μ(⊥, F) t^{r(E) - r(F)}`.

The main theorem is Whitney's Boolean expansion for loopless matroids:

  `χ_M(t) = ∑_{A ⊆ E} (-1)^{|A|} t^{r(E) - r(A)}`.

This repairs Track B item 5 of the plan: the thesis stated the expansion with a sum over
subsets but a Möbius function that lives on flats. The proof groups subsets by their closure
and identifies `∑_{cl A = F} (-1)^{|A|}` with `μ(⊥, F)` by Möbius inversion.

## Main definitions

* `Flats.coRk M X` : `r(E) - r(X)` as a natural number.
* `Flats.charPoly M` : the characteristic polynomial, in `ℤ[X]`.

## Main results

* `Flats.sum_closure_eq_mu` : for loopless `M`, `∑_{A ⊆ E, cl A = F} (-1)^{|A|} = μ(⊥, F)`.
* `Flats.charPoly_eq_sum_subsets` : Whitney's Boolean expansion.
-/

open Polynomial IncidenceAlgebra

namespace MatroidToric

namespace Flats

variable {α : Type*} {M : Matroid α}

noncomputable instance : DecidableEq (Flats M) := Classical.decEq _

instance [Finite α] : Finite (Flats M) := by
  unfold Flats; infer_instance

noncomputable instance [Finite α] : Fintype (Flats M) := Fintype.ofFinite _

open Classical in
noncomputable instance [Finite α] : LocallyFiniteOrder (Flats M) :=
  Fintype.toLocallyFiniteOrder

variable (M)

/-- The corank `r(E) - r(X)`, as a natural number (the ranks are finite for a finite type). -/
noncomputable def coRk (X : Set α) : ℕ := (M.eRk M.E).toNat - (M.eRk X).toNat

@[simp] lemma coRk_closure (X : Set α) : coRk M (M.closure X) = coRk M X := by
  simp [coRk, Matroid.eRk_closure_eq]

open Classical in
/-- The characteristic polynomial `χ_M(t) = ∑_F μ(⊥, F) t^{r(E) - r(F)}`, the sum running over
the lattice of flats. -/
noncomputable def charPoly [Finite α] : ℤ[X] :=
  ∑ F : Flats M, C (mu ℤ ⊥ F) * X ^ coRk M F.toSet

variable [Fintype α]

open Classical in
/-- The ground set as a finset. -/
noncomputable def groundFinset : Finset α := Finset.univ.filter (· ∈ M.E)

@[simp] lemma coe_groundFinset : (groundFinset M : Set α) = M.E := by
  classical
  ext x; simp [groundFinset]

lemma coe_subset_ground {A : Finset α} (hA : A ∈ (groundFinset M).powerset) :
    (A : Set α) ⊆ M.E := by
  rw [← coe_groundFinset M]; exact Finset.coe_subset.mpr (Finset.mem_powerset.mp hA)

open Classical in
/-- For a loopless matroid, the signed count of the spanning sets of a flat `F` is the Möbius
function `μ(⊥, F)` of the lattice of flats. -/
theorem sum_closure_eq_mu [M.Loopless] (F : Flats M) :
    ∑ A ∈ (groundFinset M).powerset.filter (fun A : Finset α ↦ span M (A : Set α) = F),
      (-1 : ℤ) ^ A.card = mu ℤ ⊥ F := by
  set f : Flats M → ℤ := fun G ↦
    ∑ A ∈ (groundFinset M).powerset.filter (fun A : Finset α ↦ span M (A : Set α) = G),
      (-1 : ℤ) ^ A.card
  -- the partial sums of `f` below a flat are an alternating sum over its subsets
  have hg : ∀ G : Flats M, (if G = ⊥ then (1 : ℤ) else 0) = ∑ y ∈ Finset.Iic G, f y := by
    intro G
    dsimp only [f]
    rw [Finset.sum_fiberwise_eq_sum_filter]
    have hfilt : ((groundFinset M).powerset.filter
        fun A : Finset α ↦ span M (A : Set α) ∈ Finset.Iic G) =
        (Finset.univ.filter (· ∈ G.toSet)).powerset := by
      ext A
      simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_Iic]
      constructor
      · rintro ⟨hAE, hAG⟩ x hx
        have hAE' : (A : Set α) ⊆ M.E := by
          rw [← coe_groundFinset M]; exact Finset.coe_subset.mpr hAE
        simpa using (span_le_iff_subset hAE').mp hAG hx
      · intro hAG
        have hAG' : (A : Set α) ⊆ G.toSet := fun x hx ↦ by simpa using hAG hx
        have hAE' : (A : Set α) ⊆ M.E := hAG'.trans G.toSet_subset_ground
        refine ⟨?_, (span_le_iff_subset hAE').mpr hAG'⟩
        rw [← Finset.coe_subset, coe_groundFinset]; exact hAE'
    rw [hfilt, Finset.sum_powerset_neg_one_pow_card]
    congr 1
    apply propext
    rw [Finset.filter_eq_empty_iff]
    constructor
    · rintro rfl x - hx
      simp [toSet_bot, Matroid.closure_empty] at hx
    · intro h
      apply ext
      rw [toSet_bot, Matroid.closure_empty, Matroid.loops_eq_empty]
      exact Set.eq_empty_of_forall_notMem fun x hx ↦ h (Finset.mem_univ x) hx
  have := moebius_inversion_bot (𝕜 := ℤ) f (fun G ↦ if G = ⊥ then 1 else 0) hg F
  change f F = _
  rw [this, Finset.sum_eq_single ⊥]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_Iic.mpr bot_le) h

open Classical in
/-- **Whitney's Boolean expansion.** For a loopless matroid on a finite type,
`χ_M(t) = ∑_{A ⊆ E} (-1)^{|A|} t^{r(E) - r(A)}`. -/
theorem charPoly_eq_sum_subsets [M.Loopless] :
    charPoly M =
      ∑ A ∈ (groundFinset M).powerset, C ((-1 : ℤ) ^ A.card) * X ^ coRk M (A : Set α) := by
  have hsum : ∀ A ∈ (groundFinset M).powerset,
      C ((-1 : ℤ) ^ A.card) * X ^ coRk M (A : Set α) =
        C ((-1 : ℤ) ^ A.card) * X ^ coRk M (span M (A : Set α)).toSet := by
    intro A _; simp [toSet_span]
  rw [Finset.sum_congr rfl hsum,
    ← Finset.sum_fiberwise (groundFinset M).powerset (fun A : Finset α ↦ span M (A : Set α)),
    charPoly]
  refine Finset.sum_congr rfl fun F _ ↦ ?_
  rw [← sum_closure_eq_mu M F, map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun A hA ↦ ?_
  rw [(Finset.mem_filter.mp hA).2]

end Flats

end MatroidToric
