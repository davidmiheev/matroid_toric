import Formal.CharPoly
import Mathlib.Combinatorics.Enumerative.IncidenceAlgebra
import Mathlib.Order.Preorder.Chain

/-!
# Philip Hall's theorem, combinatorial form (Track G5)

For elements `a < b` of a locally finite partial order, the Möbius function `μ(a, b)` equals the
reduced Euler characteristic of the order complex of the open interval `(a, b)`:

  `μ(a, b) = ∑_{C} (-1)^{|C| - 1}`,

the sum running over all chains `C ⊆ (a, b)`, the empty chain included. The faces of the order
complex are exactly these chains, a chain with `i` elements being an `(i - 1)`-simplex.

This repairs Track B item 4 of the plan (thesis Предложение 3): the correct statement is the
*reduced* Euler characteristic, `χ̃ = μ(0̂, 1̂)`, with no absolute value. No topology is needed.

## Main definitions

* `chainsIoo a b` : the chains of the open interval `(a, b)`, as a finset of finsets.
* `redEulerChar a b` : `∑_{C ∈ chainsIoo a b} (-1)^{|C| + 1}`.

## Main results

* `redEulerChar_eq` : for `a < b`, `χ̃(a, b) = -1 - ∑_{x ∈ (a, b)} χ̃(a, x)` (split a chain at its
  greatest element).
* `mu_eq_redEulerChar` : **Philip Hall's theorem**, `μ(a, b) = χ̃(a, b)` for `a < b`.
* `Flats.mu_bot_top_eq_redEulerChar` : the statement for the lattice of flats of a matroid.
-/

open Finset IncidenceAlgebra

namespace MatroidToric

variable {α : Type*} [PartialOrder α] [LocallyFiniteOrder α] [DecidableEq α]

open Classical in
/-- The chains of the open interval `(a, b)`: the subsets of `Ioo a b` that are totally ordered.
These are the faces of the order complex of `(a, b)`, together with the empty chain. -/
noncomputable def chainsIoo (a b : α) : Finset (Finset α) :=
  (Ioo a b).powerset.filter fun s ↦ IsChain (· ≤ ·) (s : Set α)

/-- The reduced Euler characteristic of the order complex of `(a, b)`: a chain with `i` elements
is an `(i - 1)`-simplex and contributes `(-1)^(i - 1) = (-1)^(i + 1)`; the empty chain
contributes `-1`. -/
noncomputable def redEulerChar (a b : α) : ℤ := ∑ s ∈ chainsIoo a b, (-1) ^ (s.card + 1)

omit [DecidableEq α] in
lemma mem_chainsIoo {a b : α} {s : Finset α} :
    s ∈ chainsIoo a b ↔ s ⊆ Ioo a b ∧ IsChain (· ≤ ·) (s : Set α) := by
  classical
  simp [chainsIoo]

omit [LocallyFiniteOrder α] [DecidableEq α] in
/-- A nonempty finite chain has a greatest element. -/
lemma exists_greatest_of_isChain {s : Finset α} (hs : s.Nonempty)
    (hc : IsChain (· ≤ ·) (s : Set α)) : ∃ x ∈ s, ∀ y ∈ s, y ≤ x := by
  obtain ⟨m, hm, hmax⟩ := s.exists_maximal hs
  refine ⟨m, hm, fun y hy ↦ ?_⟩
  rcases eq_or_ne y m with rfl | hne
  · exact le_rfl
  rcases hc hy hm hne with h | h
  · exact h
  · exact hmax hy h

omit [LocallyFiniteOrder α] [DecidableEq α] in
lemma greatest_unique {s : Finset α} {x y : α} (hx : x ∈ s) (hx' : ∀ z ∈ s, z ≤ x)
    (hy : y ∈ s) (hy' : ∀ z ∈ s, z ≤ y) : x = y :=
  le_antisymm (hy' x hx) (hx' y hy)

open Classical in
/-- The chains of `(a, b)` whose greatest element is `x` are obtained from the chains of `(a, x)`
by adding `x`. -/
lemma sum_chains_greatest {a b x : α} (hx : x ∈ Ioo a b) :
    ∑ s ∈ (chainsIoo a b).filter (fun s ↦ x ∈ s ∧ ∀ y ∈ s, y ≤ x), ((-1 : ℤ) ^ (s.card + 1)) =
      -redEulerChar a x := by
  rw [redEulerChar, ← Finset.sum_neg_distrib]
  have hxab := Finset.mem_Ioo.mp hx
  refine Finset.sum_nbij' (fun s ↦ s.erase x) (fun t ↦ insert x t) ?_ ?_ ?_ ?_ ?_
  · intro s hs
    simp only [Finset.mem_filter, mem_chainsIoo] at hs ⊢
    obtain ⟨⟨hsub, hc⟩, hxs, hgr⟩ := hs
    refine ⟨fun y hy ↦ ?_, hc.mono (by simp)⟩
    have hy' := Finset.mem_erase.mp hy
    have := Finset.mem_Ioo.mp (hsub hy'.2)
    exact Finset.mem_Ioo.mpr ⟨this.1, lt_of_le_of_ne (hgr y hy'.2) hy'.1⟩
  · intro t ht
    simp only [Finset.mem_filter, mem_chainsIoo] at ht ⊢
    obtain ⟨hsub, hc⟩ := ht
    have hlt : ∀ y ∈ t, y < x := fun y hy ↦ (Finset.mem_Ioo.mp (hsub hy)).2
    refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self _ _, ?_⟩
    · refine Finset.insert_subset hx fun y hy ↦ ?_
      have := Finset.mem_Ioo.mp (hsub hy)
      exact Finset.mem_Ioo.mpr ⟨this.1, this.2.trans hxab.2⟩
    · rw [Finset.coe_insert]
      refine hc.insert fun y hy _ ↦ Or.inr (hlt y hy).le
    · intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact le_rfl
      · exact (hlt y hy).le
  · intro s hs
    simp only [Finset.mem_filter] at hs
    exact Finset.insert_erase hs.2.1
  · intro t ht
    have hxt : x ∉ t := fun h ↦ (Finset.mem_Ioo.mp ((mem_chainsIoo.mp ht).1 h)).2.false
    exact Finset.erase_insert hxt
  · intro s hs
    simp only [Finset.mem_filter] at hs
    rw [Finset.card_erase_of_mem hs.2.1]
    have hpos : 0 < s.card := Finset.card_pos.mpr ⟨x, hs.2.1⟩
    obtain ⟨k, hk⟩ : ∃ k, s.card = k + 1 := ⟨s.card - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel, pow_succ]
    ring

open Classical in
/-- Splitting a chain of `(a, b)` at its greatest element:
`χ̃(a, b) = -1 - ∑_{x ∈ (a, b)} χ̃(a, x)`. -/
theorem redEulerChar_eq (a b : α) :
    redEulerChar a b = -1 - ∑ x ∈ Ioo a b, redEulerChar a x := by
  have hempty : (∅ : Finset α) ∈ chainsIoo a b := mem_chainsIoo.mpr ⟨by simp, by simp⟩
  have key : ∑ s ∈ (chainsIoo a b).erase ∅, ((-1 : ℤ) ^ (s.card + 1)) =
      ∑ x ∈ Ioo a b, -redEulerChar a x := by
    rw [show (∑ x ∈ Ioo a b, -redEulerChar a x) = ∑ x ∈ Ioo a b,
        ∑ s ∈ (chainsIoo a b).filter (fun s ↦ x ∈ s ∧ ∀ y ∈ s, y ≤ x), ((-1 : ℤ) ^ (s.card + 1))
        from Finset.sum_congr rfl fun x hx ↦ (sum_chains_greatest hx).symm]
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm, ← Finset.filter_ne', Finset.sum_filter]
    refine Finset.sum_congr rfl fun s hs ↦ ?_
    obtain ⟨hsub, hc⟩ := mem_chainsIoo.mp hs
    by_cases h : s = ∅
    · subst h; simp
    · obtain ⟨g, hg, hgr⟩ :=
        exists_greatest_of_isChain (Finset.nonempty_iff_ne_empty.mpr h) hc
      rw [ite_eq_left h, Finset.sum_eq_single g]
      · rw [ite_eq_left ⟨hg, hgr⟩]
      · intro x _ hxg
        rw [ite_eq_right]
        rintro ⟨hx, hxgr⟩
        exact hxg (greatest_unique hx hxgr hg hgr)
      · intro hg'
        exact absurd (hsub hg) hg'
  rw [redEulerChar, ← Finset.add_sum_erase _ _ hempty, key, Finset.sum_neg_distrib]
  simp only [Finset.card_empty, zero_add, pow_one]
  ring

omit [DecidableEq α] in
lemma card_Ico_lt {a b x : α} (hx : x ∈ Ioo a b) : (Ico a x).card < (Ico a b).card := by
  have hxab := Finset.mem_Ioo.mp hx
  refine Finset.card_lt_card ⟨Finset.Ico_subset_Ico_right hxab.2.le, fun hsub ↦ ?_⟩
  have := Finset.mem_Ico.mp (hsub (Finset.mem_Ico.mpr ⟨hxab.1.le, hxab.2⟩))
  exact lt_irrefl x this.2

/-- **Philip Hall's theorem.** For `a < b`, the Möbius function `μ(a, b)` is the reduced Euler
characteristic of the order complex of the open interval `(a, b)`. -/
theorem mu_eq_redEulerChar {a b : α} (hab : a < b) : mu ℤ a b = redEulerChar a b := by
  induction hn : (Ico a b).card using Nat.strong_induction_on generalizing b with
  | _ n ih =>
    rw [mu_eq_neg_sum_Ico_of_ne hab.ne, ← Finset.Ioo_insert_left hab,
      Finset.sum_insert Finset.left_notMem_Ioo, mu_self, redEulerChar_eq]
    rw [Finset.sum_congr rfl fun x hx ↦
      ih _ (hn ▸ card_Ico_lt hx) (Finset.mem_Ioo.mp hx).1 rfl]
    ring

/-- Philip Hall's theorem for the lattice of flats of a matroid on a finite type:
`μ(0̂, 1̂) = χ̃(ord(ℒ ∖ {0̂, 1̂}))`, with the sign included. This is the corrected form of thesis
Предложение 3. -/
theorem Flats.mu_bot_top_eq_redEulerChar {β : Type*} [Finite β] (M : Matroid β)
    (h : (⊥ : Flats M) < ⊤) :
    mu ℤ (⊥ : Flats M) ⊤ = redEulerChar (⊥ : Flats M) ⊤ :=
  mu_eq_redEulerChar h

end MatroidToric
