import Formal.VectorMatroid
import Formal.FlatLattice

/-!
# Fixed subspaces of a torus representation and the lattice of flats (Track G6)

The combinatorial core of thesis Теорема 7 (Ayzenberg–Cherepanov, thesis Theorem 4.22): for a
fixed point `x` with tangent weights `α : ι → M`, the faces containing `x` correspond to the
fixed subrepresentations `V^H = ⊕_{j ∈ F(H)} V(α_j)` of subtori `H ⊂ T`, where
`F(H) = {j | α_j vanishes on Lie H}`, and these index sets are exactly the flats of the weight
matroid.

Here closed subgroups of `T` are replaced by subspaces `Φ` of the dual `M*` (Lie subalgebras),
and `V^H` by its index set `F(Φ) = {j | ∀ φ ∈ Φ, φ (α j) = 0}`. The geometric input — the slice
theorem, and `V^H = ⊕_{j ∈ F(H)} V(α_j)` — is not formalized; it is where the topology lives.

## Main results

* `vectorMatroid_closure` : in a vector matroid, `cl X = {j | v j ∈ span (v '' X)}`.
* `vectorMatroid_isFlat_iff` : the flats are exactly the preimages `v ⁻¹' W` of subspaces.
* `isFlat_fixedIdx`, `exists_fixedIdx_eq` : the fixed index sets `F(Φ)` are exactly the flats;
  the flat `F` is `F(Φ)` for `Φ` the annihilator of `span (v '' F)`.
* `fixedIdxOrderIso` : the poset of fixed index sets, ordered by inclusion, is isomorphic to
  the lattice of flats `Flats (vectorMatroid v)` (Track G3).
-/

open Set Submodule

namespace MatroidToric

variable {ι K V : Type*} [Finite ι] [Field K] [AddCommGroup V] [Module K V]

/-- Closure of an independent set in a vector matroid. -/
theorem vectorMatroid_closure_of_indep {v : ι → V} {I : Set ι} (hI : LinearIndepOn K v I) :
    (vectorMatroid (K := K) v).closure I = {j | v j ∈ span K (v '' I)} := by
  have hI' : (vectorMatroid (K := K) v).Indep I := vectorMatroid_indep_iff.mpr hI
  ext j
  rw [hI'.mem_closure_iff]
  change _ ∨ j ∈ I ↔ v j ∈ span K (v '' I)
  by_cases hj : j ∈ I
  · exact ⟨fun _ ↦ subset_span (mem_image_of_mem v hj), fun _ ↦ Or.inr hj⟩
  · rw [or_iff_left hj, Matroid.dep_iff, vectorMatroid_indep_iff, linearIndepOn_insert hj]
    simp [hI]

/-- **Closure in a vector matroid**: the indices whose vectors lie in the span. -/
theorem vectorMatroid_closure (v : ι → V) (X : Set ι) :
    (vectorMatroid (K := K) v).closure X = {j | v j ∈ span K (v '' X)} := by
  set M := vectorMatroid (K := K) v
  obtain ⟨I, hI⟩ := M.exists_isBasis' X
  have hIind : LinearIndepOn K v I := vectorMatroid_indep_iff.mp hI.indep
  have hspan : span K (v '' I) = span K (v '' X) := by
    refine le_antisymm (span_mono (image_mono hI.subset)) (span_le.mpr ?_)
    rintro _ ⟨x, hx, rfl⟩
    have hxcl : x ∈ M.closure X := M.subset_closure X (by simp [M]) hx
    rw [← hI.closure_eq_closure, vectorMatroid_closure_of_indep hIind] at hxcl
    exact hxcl
  rw [← hI.closure_eq_closure, vectorMatroid_closure_of_indep hIind, hspan]

/-- The flats of a vector matroid are exactly the preimages of subspaces. -/
theorem vectorMatroid_isFlat_iff (v : ι → V) {F : Set ι} :
    (vectorMatroid (K := K) v).IsFlat F ↔ ∃ W : Submodule K V, F = v ⁻¹' W := by
  constructor
  · intro hF
    refine ⟨span K (v '' F), ?_⟩
    have := hF.closure
    rw [vectorMatroid_closure] at this
    exact this.symm
  · rintro ⟨W, rfl⟩
    rw [Matroid.isFlat_iff_closure_eq, vectorMatroid_closure]
    refine le_antisymm (fun j hj ↦ ?_) (fun j hj ↦ subset_span (mem_image_of_mem v hj))
    exact (span_le.mpr (image_preimage_subset v W)) hj

/-- The fixed index set of a subspace `Φ` of the dual (the Lie algebra of a subtorus): the
weights that vanish on `Φ`. It indexes the fixed subrepresentation `V^H`. -/
def fixedIdx (v : ι → V) (Φ : Submodule K (Module.Dual K V)) : Set ι :=
  {j | ∀ φ ∈ Φ, φ (v j) = 0}

lemma fixedIdx_eq_preimage (v : ι → V) (Φ : Submodule K (Module.Dual K V)) :
    fixedIdx v Φ = v ⁻¹' Φ.dualCoannihilator := by
  ext j
  simp [fixedIdx, mem_dualCoannihilator]

/-- A larger Lie algebra fixes fewer weights. -/
lemma fixedIdx_antitone (v : ι → V) : Antitone (fixedIdx (K := K) v) :=
  fun _ _ h _ hj φ hφ ↦ hj φ (h hφ)

/-- Every fixed index set is a flat of the weight matroid. -/
theorem isFlat_fixedIdx (v : ι → V) (Φ : Submodule K (Module.Dual K V)) :
    (vectorMatroid (K := K) v).IsFlat (fixedIdx v Φ) :=
  (vectorMatroid_isFlat_iff v).mpr ⟨_, fixedIdx_eq_preimage v Φ⟩

/-- Every flat is a fixed index set: the flat `F` is fixed exactly by the annihilator of
`span (v '' F)`, the Lie algebra of the subtorus `H_F`. -/
theorem exists_fixedIdx_eq (v : ι → V) {F : Set ι} (hF : (vectorMatroid (K := K) v).IsFlat F) :
    fixedIdx v (span K (v '' F)).dualAnnihilator = F := by
  rw [fixedIdx_eq_preimage, Subspace.dualAnnihilator_dualCoannihilator_eq]
  have := hF.closure
  rw [vectorMatroid_closure] at this
  exact this

/-- The fixed index sets are exactly the flats. -/
theorem range_fixedIdx (v : ι → V) :
    range (fixedIdx (K := K) v) = {F | (vectorMatroid (K := K) v).IsFlat F} := by
  ext F
  exact ⟨fun ⟨Φ, hΦ⟩ ↦ hΦ ▸ isFlat_fixedIdx v Φ, fun hF ↦ ⟨_, exists_fixedIdx_eq v hF⟩⟩

/-- **G6.** The poset of fixed index sets (equivalently, of fixed subrepresentations `V^H`),
ordered by inclusion, is isomorphic to the lattice of flats of the weight matroid. -/
noncomputable def fixedIdxOrderIso (v : ι → V) :
    {S : Set ι // S ∈ range (fixedIdx (K := K) v)} ≃o Flats (vectorMatroid (K := K) v) where
  toFun S := Flats.ofIsFlat S.1 (by
    obtain ⟨Φ, hΦ⟩ := S.2
    exact hΦ ▸ isFlat_fixedIdx v Φ)
  invFun F := ⟨F.toSet, ⟨_, exists_fixedIdx_eq v F.isFlat⟩⟩
  left_inv S := rfl
  right_inv F := rfl
  map_rel_iff' := Iff.rfl

end MatroidToric
