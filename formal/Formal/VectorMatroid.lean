/-
G1 (PLAN.md Track G): the linear matroid of a finite family of vectors.

Mathlib has an extensive `Matroid` API but no matroid of a family of vectors. For a finite
index type `ι` and `v : ι → V` over a field `K`, the independent sets are the `I ⊆ ι` on which
`v` is linearly independent (thesis v2, Definition 2.24). Repeated or proportional vectors give
parallel elements, which is the setting of Theorem 4.15.
-/
import Mathlib

open Module Submodule Set

namespace MatroidToric

variable {ι K V : Type*} [Finite ι] [Field K] [AddCommGroup V] [Module K V]

omit [Finite ι] in
/-- If `v` is linearly independent on a finite set `I`, the span of `v '' I` has dimension `#I`. -/
theorem finrank_span_image_eq_ncard {v : ι → V} {I : Set ι} (hI : LinearIndepOn K v I) :
    finrank K (span K (v '' I)) = I.ncard := by
  rw [finrank_span_set_eq_ncard hI.id_image, hI.injOn.ncard_image]

/-- The exchange axiom for linear independence of a finite family. -/
theorem linearIndepOn_augment {v : ι → V} {I J : Set ι} (hI : LinearIndepOn K v I)
    (hJ : LinearIndepOn K v J) (hlt : I.ncard < J.ncard) :
    ∃ e ∈ J, e ∉ I ∧ LinearIndepOn K v (insert e I) := by
  by_contra! h
  -- every vector of `J` lies in the span of `v '' I`
  have hsub : v '' J ⊆ span K (v '' I) := by
    rintro _ ⟨e, he, rfl⟩
    by_cases heI : e ∈ I
    · exact subset_span (mem_image_of_mem v heI)
    · by_contra hns
      exact h e he heI (hI.insert hns)
  have hle : span K (v '' J) ≤ span K (v '' I) := span_le.mpr hsub
  have : FiniteDimensional K (span K (v '' I)) :=
    FiniteDimensional.span_of_finite K ((toFinite I).image v)
  have := Submodule.finrank_mono hle
  rw [finrank_span_image_eq_ncard hI, finrank_span_image_eq_ncard hJ] at this
  omega

/-- **G1.** The linear matroid of a finite family of vectors `v : ι → V` over a field. -/
noncomputable def vectorMatroid (v : ι → V) : Matroid ι :=
  (IndepMatroid.ofFinite (E := univ) (toFinite _) (fun I => LinearIndepOn K v I)
    (linearIndepOn_empty K v)
    (fun _ _ hJ hIJ => hJ.mono hIJ)
    (fun _ _ hI hJ hlt => linearIndepOn_augment hI hJ hlt)
    (fun _ _ => subset_univ _)).matroid

@[simp] theorem vectorMatroid_E (v : ι → V) : (vectorMatroid (K := K) v).E = univ := rfl

@[simp] theorem vectorMatroid_indep_iff {v : ι → V} {I : Set ι} :
    (vectorMatroid (K := K) v).Indep I ↔ LinearIndepOn K v I := by
  simp [vectorMatroid]

end MatroidToric
