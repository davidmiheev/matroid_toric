import Mathlib.Combinatorics.Matroid.Closure
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Order.Atoms
import Mathlib.Order.ModularLattice

/-!
# The lattice of flats of a matroid (Track G3)

Mathlib has flats (`Matroid.IsFlat`) and the closure operator `Matroid.subtypeClosure`
whose closed elements are the flats, but no bundled lattice of flats. This file builds it
and proves the standard structure theory, for matroids on an arbitrary type (no finiteness).

## Main definitions

* `MatroidToric.Flats M` : the flats of `M`, as the closed elements of `M.subtypeClosure`,
  with the `CompleteLattice` lifted along the Galois insertion `M.subtypeClosure.gi`.
* `Flats.span M X` : the flat `M.closure X`.
* `Flats.eRk F` : the rank `M.eRk F` of a flat.

## Main results

* `Flats.toSet_inf`, `Flats.toSet_sup`, `Flats.toSet_sSup`, `Flats.toSet_sInf`,
  `Flats.toSet_bot`, `Flats.toSet_top` : meet is intersection, join is closure of union,
  the bottom flat is the set of loops, the top flat is the ground set.
* `Flats.eRk_inf_add_eRk_sup_le` : the rank function is submodular on the lattice.
* `Flats.covBy_span_insert`, `Flats.covBy_iff` : `F ⋖ G` iff `G = cl(F ∪ {e})` for some
  `e ∈ E \ F` (the covering form of the exchange axiom).
* `Flats.eRk_eq_add_one_of_covBy` : covers raise the rank by exactly one.
* `Flats.eRk_add_one_le_of_lt` : a strictly larger flat has strictly larger rank.
* Instances `IsUpperModularLattice (Flats M)` and `IsAtomistic (Flats M)`:
  the lattice of flats is (upper) semimodular and atomistic, i.e. geometric in the
  finite-rank case.
-/

open Set

namespace MatroidToric

variable {α : Type*}

/-- The flats of a matroid `M`, as the closed elements of the closure operator
`M.subtypeClosure` on subsets of the ground set. -/
def Flats (M : Matroid α) : Type _ := M.subtypeClosure.Closeds

namespace Flats

variable {M : Matroid α} {X : Set α} {e : α}

/- `Flats M` is a `def`, not an `abbrev`, so that its only order structure is this lattice
(otherwise the subtype order and the lattice order would form an instance diamond). -/
noncomputable instance : CompleteLattice (Flats M) :=
  (M.subtypeClosure.gi.liftCompleteLattice : CompleteLattice M.subtypeClosure.Closeds)

/-- The underlying set of a flat. -/
def toSet (F : Flats M) : Set α := F.1.1

lemma isFlat (F : Flats M) : M.IsFlat F.toSet :=
  Matroid.isClosed_iff_isFlat.mp F.2

lemma toSet_subset_ground (F : Flats M) : F.toSet ⊆ M.E := F.1.2

/-- Bundle a flat. -/
def ofIsFlat (F : Set α) (hF : M.IsFlat F) : Flats M :=
  ⟨⟨F, hF.subset_ground⟩, Matroid.isClosed_iff_isFlat.mpr hF⟩

@[simp] lemma toSet_ofIsFlat (F : Set α) (hF : M.IsFlat F) : (ofIsFlat F hF).toSet = F := rfl

lemma toSet_injective : Function.Injective (toSet : Flats M → Set α) :=
  fun _ _ h ↦ Subtype.ext (Subtype.ext h)

@[ext] lemma ext {F G : Flats M} (h : F.toSet = G.toSet) : F = G := toSet_injective h

lemma le_iff {F G : Flats M} : F ≤ G ↔ F.toSet ⊆ G.toSet := Iff.rfl

lemma lt_iff {F G : Flats M} : F < G ↔ F.toSet ⊂ G.toSet := by
  rw [lt_iff_le_not_ge, le_iff, le_iff, ssubset_iff_subset_not_subset]

lemma closure_toSet (F : Flats M) : M.closure F.toSet = F.toSet := F.isFlat.closure

/-- The flat spanned by a set: its closure. -/
noncomputable def span (M : Matroid α) (X : Set α) : Flats M :=
  ofIsFlat (M.closure X) (Matroid.isFlat_closure X)

@[simp] lemma toSet_span (X : Set α) : (span M X).toSet = M.closure X := rfl

lemma span_le_iff {F : Flats M} : span M X ≤ F ↔ X ∩ M.E ⊆ F.toSet := by
  rw [le_iff, toSet_span]
  refine ⟨fun h ↦ (M.inter_ground_subset_closure X).trans h, fun h ↦ ?_⟩
  rw [← Matroid.closure_inter_ground, ← F.closure_toSet]
  exact M.closure_subset_closure h

lemma subset_toSet_span (hX : X ⊆ M.E) : X ⊆ (span M X).toSet :=
  M.subset_closure X hX

/-- `span` and `toSet` form a Galois connection (on subsets of the ground set). -/
lemma span_le_iff_subset (hX : X ⊆ M.E) {F : Flats M} : span M X ≤ F ↔ X ⊆ F.toSet := by
  rw [span_le_iff, inter_eq_self_of_subset_left hX]

@[simp] lemma span_toSet (F : Flats M) : span M F.toSet = F := ext F.closure_toSet

/-! ### Meets and joins -/

@[simp] lemma toSet_inf (F G : Flats M) : (F ⊓ G).toSet = F.toSet ∩ G.toSet := by
  have hFG : M.IsFlat (F.toSet ∩ G.toSet) := by
    rw [inter_eq_iInter]
    exact Matroid.IsFlat.iInter fun b ↦ by cases b <;> simp [isFlat]
  have h1 : ofIsFlat _ hFG ≤ F := le_iff.mpr inter_subset_left
  have h2 : ofIsFlat _ hFG ≤ G := le_iff.mpr inter_subset_right
  have h3 : F ⊓ G ≤ ofIsFlat _ hFG :=
    le_iff.mpr (subset_inter (le_iff.mp inf_le_left) (le_iff.mp inf_le_right))
  exact congrArg toSet (h3.antisymm (le_inf h1 h2))

@[simp] lemma toSet_sup (F G : Flats M) : (F ⊔ G).toSet = M.closure (F.toSet ∪ G.toSet) := by
  have hU : F.toSet ∪ G.toSet ⊆ M.E := union_subset F.toSet_subset_ground G.toSet_subset_ground
  have h1 : F ≤ span M (F.toSet ∪ G.toSet) :=
    le_iff.mpr (subset_union_left.trans (subset_toSet_span hU))
  have h2 : G ≤ span M (F.toSet ∪ G.toSet) :=
    le_iff.mpr (subset_union_right.trans (subset_toSet_span hU))
  have h3 : span M (F.toSet ∪ G.toSet) ≤ F ⊔ G :=
    (span_le_iff_subset hU).mpr (union_subset (le_iff.mp le_sup_left) (le_iff.mp le_sup_right))
  exact congrArg toSet ((sup_le h1 h2).antisymm h3)

@[simp] lemma toSet_sSup (S : Set (Flats M)) :
    (sSup S).toSet = M.closure (⋃ F ∈ S, F.toSet) := by
  have hU : (⋃ F ∈ S, F.toSet) ⊆ M.E := iUnion₂_subset fun F _ ↦ F.toSet_subset_ground
  have h1 : ∀ F ∈ S, F ≤ span M (⋃ F ∈ S, F.toSet) := fun F hF ↦
    le_iff.mpr ((subset_biUnion_of_mem (u := toSet) hF).trans (subset_toSet_span hU))
  have h2 : span M (⋃ F ∈ S, F.toSet) ≤ sSup S :=
    (span_le_iff_subset hU).mpr (iUnion₂_subset fun F hF ↦ le_iff.mp (le_sSup hF))
  exact congrArg toSet ((sSup_le h1).antisymm h2)

@[simp] lemma toSet_sInf (S : Set (Flats M)) :
    (sInf S).toSet = M.E ∩ ⋂ F ∈ S, F.toSet := by
  have hI : M.IsFlat (M.E ∩ ⋂ F ∈ S, F.toSet) := by
    rw [Matroid.isFlat_iff_closure_eq]
    refine (subset_inter (M.closure_subset_ground _) (subset_iInter₂ fun F hF ↦ ?_)).antisymm
      (M.subset_closure _ inter_subset_left)
    rw [← F.closure_toSet]
    exact M.closure_subset_closure (inter_subset_right.trans (biInter_subset_of_mem hF))
  have h1 : ∀ F ∈ S, ofIsFlat _ hI ≤ F := fun F hF ↦
    le_iff.mpr (inter_subset_right.trans (biInter_subset_of_mem hF))
  have h2 : sInf S ≤ ofIsFlat _ hI := le_iff.mpr (subset_inter (sInf S).toSet_subset_ground
    (subset_iInter₂ fun F hF ↦ le_iff.mp (sInf_le hF)))
  exact congrArg toSet (h2.antisymm (le_sInf h1))

/-- The bottom flat is the set of loops. -/
@[simp] lemma toSet_bot : (⊥ : Flats M).toSet = M.closure ∅ := by
  have h : span M ∅ ≤ ⊥ := span_le_iff.mpr (by simp)
  exact congrArg toSet (bot_le.antisymm h)

/-- The top flat is the ground set. -/
@[simp] lemma toSet_top : (⊤ : Flats M).toSet = M.E := by
  have h : (⊤ : Flats M) ≤ ofIsFlat M.E M.ground_isFlat := le_iff.mpr (toSet_subset_ground _)
  exact congrArg toSet (h.antisymm le_top)

/-! ### Rank -/

/-- The rank of a flat. -/
noncomputable def eRk (F : Flats M) : ℕ∞ := M.eRk F.toSet

lemma eRk_mono : Monotone (eRk : Flats M → ℕ∞) := fun _ _ h ↦ M.eRk_mono (le_iff.mp h)

@[simp] lemma eRk_span (X : Set α) : (span M X).eRk = M.eRk X := M.eRk_closure_eq X

/-- The rank function of a matroid is submodular on its lattice of flats. -/
theorem eRk_inf_add_eRk_sup_le (F G : Flats M) : (F ⊓ G).eRk + (F ⊔ G).eRk ≤ F.eRk + G.eRk := by
  simp only [eRk, toSet_inf, toSet_sup, Matroid.eRk_closure_eq]
  exact M.eRk_inter_add_eRk_union_le _ _

/-! ### Covers -/

/-- Adjoining an element outside a flat and closing up gives a cover. This is the covering
form of the Mac Lane–Steinitz exchange property. -/
theorem covBy_span_insert (F : Flats M) (he : e ∈ M.E \ F.toSet) :
    F ⋖ span M (insert e F.toSet) := by
  have hins : insert e F.toSet ⊆ M.E := insert_subset he.1 F.toSet_subset_ground
  have heS : e ∈ (span M (insert e F.toSet)).toSet := subset_toSet_span hins (mem_insert _ _)
  refine ⟨lt_iff.mpr ⟨(subset_insert _ _).trans (subset_toSet_span hins),
    fun h ↦ he.2 (h heS)⟩, fun H hFH hHS ↦ ?_⟩
  obtain ⟨f, hfH, hfF⟩ := exists_of_ssubset (lt_iff.mp hFH)
  have hfS : f ∈ M.closure (insert e F.toSet) := (lt_iff.mp hHS).subset hfH
  have hex : e ∈ M.closure (insert f F.toSet) \ M.closure F.toSet :=
    Matroid.closure_exchange ⟨hfS, by rwa [F.closure_toSet]⟩
  have heH : e ∈ H.toSet := by
    rw [← H.closure_toSet]
    exact M.closure_subset_closure (insert_subset hfH (lt_iff.mp hFH).subset) hex.1
  exact (lt_iff.mp hHS).not_subset
    (le_iff.mp ((span_le_iff_subset hins).mpr (insert_subset heH (lt_iff.mp hFH).subset)))

/-- Every cover arises from `covBy_span_insert`. -/
theorem covBy_iff {F G : Flats M} :
    F ⋖ G ↔ ∃ e ∈ M.E \ F.toSet, G = span M (insert e F.toSet) := by
  refine ⟨fun h ↦ ?_, fun ⟨e, he, hG⟩ ↦ hG ▸ covBy_span_insert F he⟩
  obtain ⟨e, heG, heF⟩ := exists_of_ssubset (lt_iff.mp h.lt)
  have he : e ∈ M.E \ F.toSet := ⟨G.toSet_subset_ground heG, heF⟩
  have hins : insert e F.toSet ⊆ M.E := insert_subset he.1 F.toSet_subset_ground
  have hle : span M (insert e F.toSet) ≤ G :=
    (span_le_iff_subset hins).mpr (insert_subset heG (le_iff.mp h.le))
  refine ⟨e, he, ?_⟩
  obtain h' | h' := h.eq_or_eq (covBy_span_insert F he).le hle
  · exact absurd h' (covBy_span_insert F he).lt.ne'
  · exact h'.symm

/-- Covers raise the rank by exactly one. -/
theorem eRk_eq_add_one_of_covBy {F G : Flats M} (h : F ⋖ G) : G.eRk = F.eRk + 1 := by
  obtain ⟨e, he, rfl⟩ := covBy_iff.mp h
  rw [eRk_span, eRk]
  exact Matroid.eRk_insert_eq_add_one (by rwa [F.closure_toSet])

/-- A strictly larger flat has rank at least one more. -/
theorem eRk_add_one_le_of_lt {F G : Flats M} (h : F < G) : F.eRk + 1 ≤ G.eRk := by
  obtain ⟨e, heG, heF⟩ := exists_of_ssubset (lt_iff.mp h)
  have he : e ∈ M.E \ F.toSet := ⟨G.toSet_subset_ground heG, heF⟩
  have hins : insert e F.toSet ⊆ M.E := insert_subset he.1 F.toSet_subset_ground
  rw [← eRk_eq_add_one_of_covBy (covBy_span_insert F he)]
  exact eRk_mono ((span_le_iff_subset hins).mpr (insert_subset heG (le_iff.mp h.le)))

/-- On flats of finite rank the rank function is strictly monotone. -/
theorem eRk_lt_eRk_of_lt {F G : Flats M} (h : F < G) (hF : F.eRk ≠ ⊤) : F.eRk < G.eRk :=
  (ENat.lt_add_one_iff hF).mpr le_rfl |>.trans_le (eRk_add_one_le_of_lt h)

/-! ### Semimodularity and atomicity -/

/-- The lattice of flats is upper semimodular. -/
instance : IsUpperModularLattice (Flats M) where
  covBy_sup_of_inf_covBy {a b} h := by
    obtain ⟨e, he, ha⟩ := covBy_iff.mp h
    have heb : e ∈ M.E \ b.toSet := ⟨he.1, fun heb ↦ he.2 ⟨by
      rw [ha]; exact subset_toSet_span (insert_subset he.1 (a ⊓ b).toSet_subset_ground)
        (mem_insert _ _), heb⟩⟩
    convert covBy_span_insert b heb using 1
    ext1
    rw [toSet_sup, toSet_span, ha, toSet_span, Matroid.closure_union_closure_left_eq, toSet_inf,
      insert_union, union_eq_self_of_subset_left inter_subset_right]

/-- The atoms of the lattice of flats are the closures of non-loops. -/
lemma isAtom_span_insert_bot (he : e ∈ M.E \ M.closure ∅) :
    IsAtom (span M (insert e (⊥ : Flats M).toSet)) :=
  bot_covBy_iff.mp (covBy_span_insert ⊥ (by rwa [toSet_bot]))

/-- The lattice of flats is atomistic: every flat is the join of the atoms below it. -/
instance : IsAtomistic (Flats M) where
  isLUB_atoms b := by
    refine ⟨{a | IsAtom a ∧ a ≤ b}, ?_, fun a ha ↦ ha.1⟩
    suffices hb : b = sSup {a | IsAtom a ∧ a ≤ b} by
      conv_rhs => rw [hb]
      exact isLUB_sSup _
    refine le_antisymm (fun x hx ↦ ?_) (sSup_le fun a ha ↦ ha.2)
    by_cases hx0 : x ∈ (⊥ : Flats M).toSet
    · exact le_iff.mp bot_le hx0
    have hxE : x ∈ M.E := b.toSet_subset_ground hx
    have hins : insert x (⊥ : Flats M).toSet ⊆ M.E :=
      insert_subset hxE (⊥ : Flats M).toSet_subset_ground
    have hab : span M (insert x (⊥ : Flats M).toSet) ≤ b :=
      (span_le_iff_subset hins).mpr (insert_subset hx (le_iff.mp bot_le))
    have hat := isAtom_span_insert_bot (M := M) ⟨hxE, by rwa [← toSet_bot]⟩
    exact le_iff.mp (le_sSup (show _ ∈ {a | IsAtom a ∧ a ≤ b} from ⟨hat, hab⟩)) (subset_toSet_span hins (mem_insert _ _))

end Flats

end MatroidToric
