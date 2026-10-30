import Formal.EdgeReconstruction
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Subgraph
import Mathlib.Data.Fintype.Perm
import Mathlib.Order.Bounds.OrderIso

/-!
# The cluster-permutohedron determines the graph (Theorem A)

Thesis v2, Theorem 4.35; `experiments/question1/PROOF.md`, Theorem A.

For a simple graph `Γ` on a finite type `V`, an element of the cluster-permutohedron `Cl_Γ`
(Ayzenberg–Buchstaber) is a clustering of `V` into blocks inducing connected subgraphs, together
with label sets partitioning the labels, one per block and of the same size. We take the labels
to be `V` itself and encode an element as the map `a : V → Finset V` sending each vertex to the
label set of its block. Blocks are then the fibres of `a`, and the order of `Cl_Γ` (refinement,
with label sets uniting) is the pointwise order `a ≤ b ↔ ∀ v, a v ⊆ b v`.

## Main results

* `isMin_iff` : the minimal elements are the maps `v ↦ {p v}` for permutations `p`, so there
  are `|V|!` of them (`card_min`).
* `covBy_bot_iff` : above the minimal element `v ↦ {v}`, the covering elements are the atoms
  `atom e` of the edges `e` of `Γ`.
* `nu_*` : the number `ν` of minimal elements below a join of atoms tells whether two edges meet
  (`6` against at most `4`) and whether three pairwise meeting edges form a triangle (`6`
  against `24`).
* `cl_rigid` : **Theorem A**, `Cl_Γ ≃o Cl_Γ' → Γ ≃g Γ'` for graphs on nonempty finite types.
-/

open Finset

namespace MatroidToric

namespace Cluster

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

/-- The fibre of `a` through `v`: the block of `v`. -/
def fib (a : V → Finset V) (v : V) : Finset V := univ.filter fun w ↦ a w = a v

lemma mem_fib {a : V → Finset V} {v w : V} : w ∈ fib a v ↔ a w = a v := by
  simp [fib]

lemma self_mem_fib (a : V → Finset V) (v : V) : v ∈ fib a v := mem_fib.mpr rfl

/-- `a` is an element of `Cl_Γ`: label sets of distinct blocks are disjoint, each label set has
the size of its block, and each block induces a connected subgraph. -/
structure IsCl (a : V → Finset V) : Prop where
  eq_or_disjoint : ∀ v w, a v = a w ∨ Disjoint (a v) (a w)
  card_eq : ∀ v, (a v).card = (fib a v).card
  connected : ∀ v, (G.induce (fib a v : Set V)).Connected

/-- The cluster-permutohedron `Cl_Γ`, ordered pointwise. -/
abbrev Cl := {a : V → Finset V // IsCl G a}

noncomputable instance : Fintype (Cl G) := by classical exact Subtype.fintype _

variable {G}

lemma le_iff {a b : Cl G} : a ≤ b ↔ ∀ v, a.1 v ⊆ b.1 v := Iff.rfl

lemma nonempty_val (a : Cl G) (v : V) : (a.1 v).Nonempty := by
  rw [← card_pos, a.2.card_eq v]
  exact card_pos.mpr ⟨v, self_mem_fib _ _⟩

/-- Two label sets that meet are equal. -/
lemma eq_of_mem (a : Cl G) {v w : V} {ℓ : V} (hv : ℓ ∈ a.1 v) (hw : ℓ ∈ a.1 w) :
    a.1 v = a.1 w :=
  (a.2.eq_or_disjoint v w).resolve_right fun h ↦ Finset.disjoint_left.mp h hv hw

/-! ### Minimal elements -/

lemma connected_singleton (v : V) : (G.induce ({v} : Set V)).Connected := by
  rw [SimpleGraph.induce_singleton_eq_top]
  exact SimpleGraph.connected_top

/-- The minimal element of a permutation `p`: each vertex is its own block, labelled `p v`. -/
def sing (p : Equiv.Perm V) : Cl G :=
  ⟨fun v ↦ {p v},
    { eq_or_disjoint := fun v w ↦ by
        by_cases h : p v = p w
        · exact Or.inl (by rw [h])
        · exact Or.inr (Finset.disjoint_singleton.mpr h)
      card_eq := fun v ↦ by
        have : fib (fun v ↦ ({p v} : Finset V)) v = {v} := by
          ext w; simp [mem_fib, p.injective.eq_iff]
        rw [this]; rfl
      connected := fun v ↦ by
        have : (fib (fun v ↦ ({p v} : Finset V)) v : Set V) = {v} := by
          ext w; simp [mem_fib, p.injective.eq_iff]
        rw [this]
        exact connected_singleton v }⟩

@[simp] lemma sing_val (p : Equiv.Perm V) (v : V) : (sing (G := G) p).1 v = {p v} := rfl

lemma sing_injective : Function.Injective (sing (G := G)) := by
  intro p q h
  ext v
  have := congrArg (fun a : Cl G ↦ a.1 v) h
  simpa using this

/-- Every element has a transversal: a permutation choosing one label from each label set,
bijectively on every block. -/
lemma exists_transversal (a : Cl G) : ∃ p : Equiv.Perm V, ∀ v, p v ∈ a.1 v := by
  classical
  have hcard : ∀ S, (∃ v, a.1 v = S) →
      Fintype.card {w // a.1 w = S} = Fintype.card {ℓ // ℓ ∈ S} := by
    rintro S ⟨v, rfl⟩
    rw [Fintype.card_subtype, Fintype.card_coe, a.2.card_eq v]
    rfl
  let E : ∀ S, (∃ v, a.1 v = S) → ({w // a.1 w = S} ≃ {ℓ // ℓ ∈ S}) :=
    fun S hS ↦ Fintype.equivOfCardEq (hcard S hS)
  have hEcongr : ∀ {S T : Finset V} (hST : S = T) (hS : ∃ v, a.1 v = S) (hT : ∃ v, a.1 v = T)
      (x : V) (hx : a.1 x = S) (hx' : a.1 x = T), (E S hS ⟨x, hx⟩).1 = (E T hT ⟨x, hx'⟩).1 := by
    intro S T hST
    subst hST
    intros
    rfl
  let f : V → V := fun v ↦ (E (a.1 v) ⟨v, rfl⟩ ⟨v, rfl⟩).1
  have hf : ∀ v, f v ∈ a.1 v := fun v ↦ (E (a.1 v) ⟨v, rfl⟩ ⟨v, rfl⟩).2
  have hinj : Function.Injective f := by
    intro v w h
    have hvw : a.1 v = a.1 w := eq_of_mem a (hf v) (h ▸ hf w)
    have h1 : f v = (E (a.1 w) ⟨w, rfl⟩ ⟨v, hvw⟩).1 := hEcongr hvw ⟨v, rfl⟩ ⟨w, rfl⟩ v rfl hvw
    have := (E (a.1 w) ⟨w, rfl⟩).injective (Subtype.ext (h1.symm.trans h))
    exact congrArg Subtype.val this
  exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), hf⟩

/-- The minimal elements are exactly the elements `sing p`. -/
theorem isMin_iff {a : Cl G} : IsMin a ↔ ∃ p, a = sing p := by
  constructor
  · intro ha
    obtain ⟨p, hp⟩ := exists_transversal a
    refine ⟨p, ?_⟩
    have hle : sing p ≤ a := fun v ↦ by simpa using hp v
    have hge := ha hle
    exact le_antisymm hge hle
  · rintro ⟨p, rfl⟩ b hb v
    have h := hb v
    simp only [sing_val, Finset.subset_singleton_iff] at h
    rcases h with h | h
    · exact absurd h (nonempty_val b v).ne_empty
    · rw [h]; simp

/-- The minimal elements below `a` correspond to the permutations `p` with `p v ∈ a v`. -/
noncomputable def minBelowEquiv (a : Cl G) :
    {b : Cl G // IsMin b ∧ b ≤ a} ≃ {p : Equiv.Perm V // ∀ v, p v ∈ a.1 v} where
  toFun b := ⟨(isMin_iff.mp b.2.1).choose, fun v ↦ by
    have h := b.2.2 v
    rw [(isMin_iff.mp b.2.1).choose_spec] at h
    simpa using h⟩
  invFun p := ⟨sing p.1, isMin_iff.mpr ⟨p.1, rfl⟩, fun v ↦ by simpa using p.2 v⟩
  left_inv b := Subtype.ext (isMin_iff.mp b.2.1).choose_spec.symm
  right_inv p := by
    apply Subtype.ext
    apply sing_injective (G := G)
    exact (isMin_iff.mp (isMin_iff.mpr ⟨p.1, rfl⟩ : IsMin (sing (G := G) p.1))).choose_spec.symm

/-- `ν(a)`: the number of minimal elements below `a`. -/
noncomputable def nu (a : Cl G) : ℕ := by
  classical exact Fintype.card {b : Cl G // IsMin b ∧ b ≤ a}

lemma nu_eq (a : Cl G) :
    nu a = Fintype.card {p : Equiv.Perm V // ∀ v, p v ∈ a.1 v} := by
  classical
  rw [nu, Fintype.card_congr (minBelowEquiv a)]

open Classical in
/-- There are `|V|!` minimal elements. -/
theorem card_min : Fintype.card {a : Cl G // IsMin a} = (Fintype.card V).factorial := by
  rw [← Fintype.card_perm]
  refine (Fintype.card_congr ?_)
  exact {
    toFun := fun a ↦ (isMin_iff.mp a.2).choose
    invFun := fun p ↦ ⟨sing p, isMin_iff.mpr ⟨p, rfl⟩⟩
    left_inv := fun a ↦ Subtype.ext (isMin_iff.mp a.2).choose_spec.symm
    right_inv := fun p ↦ sing_injective (G := G)
      (isMin_iff.mp (isMin_iff.mpr ⟨p, rfl⟩ : IsMin (sing (G := G) p))).choose_spec.symm }

/-! ### Elements above the base point -/

/-- The base point: every vertex its own block, labelled by itself. -/
def base : Cl G := sing (Equiv.refl V)

@[simp] lemma base_val (v : V) : (base (G := G)).1 v = {v} := rfl

lemma base_le_iff {a : Cl G} : base ≤ a ↔ ∀ v, v ∈ a.1 v := by
  simp [le_iff, base_val]

/-- Above the base point, the label set of a block is the block itself. -/
lemma eq_fib_of_base_le {a : Cl G} (ha : base ≤ a) (v : V) : a.1 v = fib a.1 v := by
  rw [base_le_iff] at ha
  ext ℓ
  rw [mem_fib]
  exact ⟨fun h ↦ (eq_of_mem a (ha ℓ) h), fun h ↦ h ▸ ha ℓ⟩

/-- A single block `S`, every other vertex alone. -/
def blkFun (S : Finset V) (v : V) : Finset V := if v ∈ S then S else {v}

lemma fib_blkFun_of_mem {S : Finset V} {v : V} (hv : v ∈ S) : fib (blkFun S) v = S := by
  ext w
  rw [mem_fib, blkFun, blkFun, if_pos hv]
  by_cases hw : w ∈ S
  · simp [hw]
  · simp only [hw, if_false, iff_false]
    intro h
    exact hw (h ▸ Finset.mem_singleton_self w)

lemma fib_blkFun_of_not_mem {S : Finset V} {v : V} (hv : v ∉ S) : fib (blkFun S) v = {v} := by
  ext w
  rw [mem_fib, blkFun, blkFun, if_neg hv, Finset.mem_singleton]
  by_cases hw : w ∈ S
  · rw [if_pos hw]
    constructor
    · intro h
      have hw' := hw
      rw [h, Finset.mem_singleton] at hw'
      exact absurd (hw' ▸ hw) hv
    · rintro rfl; exact absurd hw hv
  · simp [hw]

/-- The element with the single (connected) block `S`. -/
def blk (S : Finset V) (hS : (G.induce (S : Set V)).Connected) : Cl G :=
  ⟨blkFun S,
    { eq_or_disjoint := fun v w ↦ by
        unfold blkFun
        by_cases hv : v ∈ S <;> by_cases hw : w ∈ S
        · left; rw [if_pos hv, if_pos hw]
        · right; rw [if_pos hv, if_neg hw]; exact Finset.disjoint_singleton_right.mpr hw
        · right; rw [if_neg hv, if_pos hw]; exact Finset.disjoint_singleton_left.mpr hv
        · rw [if_neg hv, if_neg hw]
          by_cases hvw : v = w
          · exact Or.inl (by rw [hvw])
          · exact Or.inr (Finset.disjoint_singleton.mpr hvw)
      card_eq := fun v ↦ by
        by_cases hv : v ∈ S
        · rw [fib_blkFun_of_mem hv, blkFun, if_pos hv]
        · rw [fib_blkFun_of_not_mem hv, blkFun, if_neg hv]
      connected := fun v ↦ by
        by_cases hv : v ∈ S
        · rw [fib_blkFun_of_mem hv]; exact hS
        · rw [fib_blkFun_of_not_mem hv, Finset.coe_singleton]; exact connected_singleton v }⟩

lemma blk_val {S : Finset V} (hS : (G.induce (S : Set V)).Connected) (v : V) :
    (blk S hS).1 v = if v ∈ S then S else {v} := rfl

lemma base_le_blk {S : Finset V} (hS : (G.induce (S : Set V)).Connected) : base ≤ blk S hS := by
  rw [base_le_iff]
  intro v
  rw [blk_val]
  split_ifs with h
  · exact h
  · exact Finset.mem_singleton_self v

/-- `ν` of a single block is `|S|!`. -/
theorem nu_blk {S : Finset V} (hS : (G.induce (S : Set V)).Connected) :
    nu (blk S hS) = S.card.factorial := by
  classical
  rw [nu_eq]
  have hiff : ∀ p : Equiv.Perm V, (∀ v, p v ∈ (blk S hS).1 v) ↔ ∀ v, v ∉ S → p v = v := by
    intro p
    constructor
    · intro h v hv
      have := h v
      rwa [blk_val, if_neg hv, Finset.mem_singleton] at this
    · intro h v
      rw [blk_val]
      split_ifs with hv
      · by_contra hpv
        have := h (p v) hpv
        exact hpv (by rw [p.injective this]; exact hv)
      · exact Finset.mem_singleton.mpr (h v hv)
  rw [Fintype.card_congr (Equiv.subtypeEquivRight hiff),
    ← Fintype.card_congr (Equiv.Perm.subtypeEquivSubtypePerm (· ∈ S)), Fintype.card_perm,
    Fintype.card_coe]

/-- Two label sets above the base point that share a vertex are the same block. -/
lemma blk_le_iff {a : Cl G} (ha : base ≤ a) {S : Finset V}
    (hS : (G.induce (S : Set V)).Connected) :
    blk S hS ≤ a ↔ ∀ x ∈ S, ∀ y ∈ S, a.1 x = a.1 y := by
  have hself : ∀ v, v ∈ a.1 v := base_le_iff.mp ha
  constructor
  · intro h x hx y hy
    have hxy : y ∈ a.1 x := by
      have := h x
      rw [blk_val, if_pos hx] at this
      exact this hy
    exact eq_of_mem a hxy (hself y)
  · intro h x
    rw [blk_val]
    split_ifs with hx
    · intro y hy
      rw [h x hx y hy]
      exact hself y
    · intro y hy
      rw [Finset.mem_singleton.mp hy]
      exact hself x

/-! ### Edges and atoms -/

/-- The two endpoints of an edge, as a finset. -/
def edgeFin (e : Sym2 V) : Finset V := univ.filter (· ∈ e)

lemma mem_edgeFin {e : Sym2 V} {x : V} : x ∈ edgeFin e ↔ x ∈ e := by
  simp [edgeFin]

lemma edgeFin_mk (u v : V) : edgeFin s(u, v) = {u, v} := by
  ext x; simp [mem_edgeFin, Sym2.mem_iff]

lemma connected_edgeFin (e : G.edgeSet) : (G.induce (edgeFin (e : Sym2 V) : Set V)).Connected := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h u v =>
    rw [edgeFin_mk, Finset.coe_insert, Finset.coe_singleton]
    exact SimpleGraph.induce_pair_connected_of_adj he

lemma card_edgeFin (e : G.edgeSet) : (edgeFin (e : Sym2 V)).card = 2 := by
  obtain ⟨e, he⟩ := e
  induction e using Sym2.ind with
  | h u v =>
    rw [edgeFin_mk, Finset.card_pair (G.ne_of_adj he)]

/-- The atom of an edge: its two endpoints form one block. -/
def atom (e : G.edgeSet) : Cl G := blk (edgeFin (e : Sym2 V)) (connected_edgeFin e)

lemma atom_injective : Function.Injective (atom (G := G)) := by
  intro e f h
  obtain ⟨u, hu⟩ : ∃ u, u ∈ (e : Sym2 V) := ⟨_, Sym2.out_fst_mem _⟩
  have h1 := congrArg (fun a : Cl G ↦ a.1 u) h
  simp only [atom, blk_val, mem_edgeFin.mpr hu, if_true] at h1
  have hu' : u ∈ (f : Sym2 V) := by
    by_contra hf
    rw [if_neg (fun h ↦ hf (mem_edgeFin.mp h))] at h1
    have := congrArg Finset.card h1
    rw [card_edgeFin, Finset.card_singleton] at this
    exact absurd this (by omega)
  rw [if_pos (mem_edgeFin.mpr hu')] at h1
  exact Subtype.ext (Sym2.ext fun x ↦ by rw [← mem_edgeFin, h1, mem_edgeFin])

lemma base_lt_atom (e : G.edgeSet) : base < atom e := by
  refine lt_of_le_of_ne (base_le_blk _) fun h ↦ ?_
  obtain ⟨u, hu⟩ : ∃ u, u ∈ (e : Sym2 V) := ⟨_, Sym2.out_fst_mem _⟩
  have h1 := congrArg (fun a : Cl G ↦ (a.1 u).card) h
  simp only [base_val, Finset.card_singleton, atom, blk_val, mem_edgeFin.mpr hu, if_true,
    card_edgeFin] at h1
  exact absurd h1 (by omega)

/-- A connected set with two distinct vertices contains an edge. -/
lemma exists_adj_of_connected {S : Set V} (hS : (G.induce S).Connected) {v w : V} (hv : v ∈ S)
    (hw : w ∈ S) (hvw : v ≠ w) : ∃ a b, a ∈ S ∧ b ∈ S ∧ G.Adj a b := by
  obtain ⟨p⟩ := hS.preconnected ⟨v, hv⟩ ⟨w, hw⟩
  cases p with
  | nil => exact absurd rfl hvw
  | cons h _ => exact ⟨_, _, hv, Subtype.coe_prop _, h⟩

/-- Above the base point, the covering elements are exactly the atoms. -/
theorem covBy_base_iff {a : Cl G} : base ⋖ a ↔ ∃ e, a = atom e := by
  constructor
  · intro h
    have hle := h.le
    have hself : ∀ v, v ∈ a.1 v := base_le_iff.mp hle
    -- some block of `a` has two vertices
    obtain ⟨v, hv⟩ : ∃ v, a.1 v ≠ {v} := by
      by_contra hcon
      push_neg at hcon
      exact h.lt.ne (Subtype.ext (funext fun v ↦ (hcon v).symm))
    obtain ⟨w, hw, hwv⟩ : ∃ w ∈ a.1 v, w ≠ v := by
      by_contra hcon
      push_neg at hcon
      exact hv (Finset.eq_singleton_iff_unique_mem.mpr ⟨hself v, hcon⟩)
    have hconn := a.2.connected v
    rw [← eq_fib_of_base_le hle v] at hconn
    obtain ⟨x, y, hx, hy, hxy⟩ := exists_adj_of_connected hconn (hself v) hw hwv.symm
    let e : G.edgeSet := ⟨s(x, y), hxy⟩
    have hle' : atom e ≤ a := by
      rw [atom, blk_le_iff hle]
      intro p hp q hq
      simp only [e, edgeFin_mk, Finset.mem_insert, Finset.mem_singleton] at hp hq
      have hx' : a.1 x = a.1 v := eq_of_mem a (hself x) (by exact_mod_cast hx)
      have hy' : a.1 y = a.1 v := eq_of_mem a (hself y) (by exact_mod_cast hy)
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> simp [hx', hy']
    refine ⟨e, ?_⟩
    rcases hle'.lt_or_eq with hlt | heq
    · exact absurd hlt (h.2 (base_lt_atom e))
    · exact heq.symm
  · rintro ⟨e, rfl⟩
    refine ⟨base_lt_atom e, fun z hz hz' ↦ ?_⟩
    have hzle := hz'.le
    have hself : ∀ v, v ∈ z.1 v := base_le_iff.mp hz.le
    -- some block of `z` has two vertices; it must be the edge
    obtain ⟨v, hv⟩ : ∃ v, z.1 v ≠ {v} := by
      by_contra hcon
      push_neg at hcon
      exact hz.ne (Subtype.ext (funext fun v ↦ (hcon v).symm))
    have hzv := hzle v
    simp only [atom, blk_val] at hzv
    split_ifs at hzv with hve
    · -- `z v` lies in the edge, contains `v`, and is not `{v}`: it is the edge
      have hzv_eq : z.1 v = edgeFin (e : Sym2 V) := by
        apply Finset.eq_of_subset_of_card_le hzv
        rw [card_edgeFin]
        by_contra hlt
        push_neg at hlt
        have hc : (z.1 v).card = 1 := by
          have := Finset.card_pos.mpr ⟨v, hself v⟩
          omega
        obtain ⟨x, hx⟩ := Finset.card_eq_one.mp hc
        have hxv : x = v := (Finset.mem_singleton.mp (hx ▸ hself v)).symm
        exact hv (hxv ▸ hx)
      apply hz'.ne
      apply Subtype.ext
      funext x
      simp only [atom, blk_val]
      split_ifs with hxe
      · have : z.1 x = z.1 v := eq_of_mem z (hself x) (hzv_eq ▸ hxe)
        rw [this, hzv_eq]
      · have hx := hzle x
        simp only [atom, blk_val, if_neg hxe] at hx
        exact Finset.Subset.antisymm hx (Finset.singleton_subset_iff.mpr (hself x))
    · exact hv (Finset.Subset.antisymm hzv (Finset.singleton_subset_iff.mpr (hself v)))

/-! ### Joins of atoms and the invariant `ν` -/

lemma connected_union {S T : Finset V} (hS : (G.induce (S : Set V)).Connected)
    (hT : (G.induce (T : Set V)).Connected) (hST : (S ∩ T).Nonempty) :
    (G.induce ((S ∪ T : Finset V) : Set V)).Connected := by
  rw [Finset.coe_union]
  exact SimpleGraph.induce_union_connected hS.preconnected hT.preconnected
    (by exact_mod_cast hST)

/-- Within one block of an element above the base point. -/
lemma same_block {a : Cl G} (ha : base ≤ a) {S : Finset V}
    (hS : (G.induce (S : Set V)).Connected) (h : blk S hS ≤ a) {x y : V} (hx : x ∈ S)
    (hy : y ∈ S) : a.1 x = a.1 y :=
  (blk_le_iff ha hS).mp h x hx y hy

/-- The join of two single blocks that overlap is their union. -/
theorem isLUB_blk_pair {S T : Finset V} (hS : (G.induce (S : Set V)).Connected)
    (hT : (G.induce (T : Set V)).Connected) (hST : (S ∩ T).Nonempty) :
    IsLUB {blk S hS, blk T hT} (blk (S ∪ T) (connected_union hS hT hST)) := by
  have hU := connected_union hS hT hST
  have hbase : base ≤ blk (S ∪ T) hU := base_le_blk hU
  have hU_block : ∀ x ∈ S ∪ T, (blk (S ∪ T) hU).1 x = S ∪ T := fun x hx ↦ by
    rw [blk_val, if_pos hx]
  refine ⟨?_, fun y hy ↦ ?_⟩
  · rintro z (rfl | rfl)
    · refine (blk_le_iff hbase hS).mpr fun x hx x' hx' ↦ ?_
      rw [hU_block x (Finset.mem_union_left _ hx), hU_block x' (Finset.mem_union_left _ hx')]
    · refine (blk_le_iff hbase hT).mpr fun x hx x' hx' ↦ ?_
      rw [hU_block x (Finset.mem_union_right _ hx), hU_block x' (Finset.mem_union_right _ hx')]
  · have hyS : blk S hS ≤ y := hy (Set.mem_insert _ _)
    have hyT : blk T hT ≤ y := hy (Set.mem_insert_of_mem _ rfl)
    have hy0 : base ≤ y := (base_le_blk hS).trans hyS
    obtain ⟨c, hc⟩ := hST
    rw [Finset.mem_inter] at hc
    have key : ∀ x ∈ S ∪ T, y.1 x = y.1 c := by
      intro x hx
      rcases Finset.mem_union.mp hx with hx | hx
      · exact same_block hy0 hS hyS hx hc.1
      · exact same_block hy0 hT hyT hx hc.2
    refine (blk_le_iff hy0 hU).mpr fun x hx x' hx' ↦ ?_
    rw [key x hx, key x' hx']

/-- The join of three pairwise overlapping single blocks is their union. -/
theorem isLUB_blk_triple {S T U : Finset V} (hS : (G.induce (S : Set V)).Connected)
    (hT : (G.induce (T : Set V)).Connected) (hU : (G.induce (U : Set V)).Connected)
    (hST : (S ∩ T).Nonempty) (hSTU : ((S ∪ T) ∩ U).Nonempty) :
    IsLUB {blk S hS, blk T hT, blk U hU}
      (blk (S ∪ T ∪ U) (connected_union (connected_union hS hT hST) hU hSTU)) := by
  have h2 := isLUB_blk_pair hS hT hST
  have h3 := isLUB_blk_pair (connected_union hS hT hST) hU hSTU
  -- the join of the first two, then with the third
  refine ⟨?_, fun y hy ↦ ?_⟩
  · rintro z (rfl | rfl | rfl)
    · exact (h2.1 (Set.mem_insert _ _)).trans (h3.1 (Set.mem_insert _ _))
    · exact (h2.1 (Set.mem_insert_of_mem _ rfl)).trans (h3.1 (Set.mem_insert _ _))
    · exact h3.1 (Set.mem_insert_of_mem _ rfl)
  · have hy2 : blk (S ∪ T) (connected_union hS hT hST) ≤ y := h2.2 fun z hz ↦ by
      rcases hz with rfl | rfl
      · exact hy (Set.mem_insert _ _)
      · exact hy (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    exact h3.2 fun z hz ↦ by
      rcases hz with rfl | rfl
      · exact hy2
      · exact hy (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl))

/-- `ν` is monotone. -/
lemma nu_mono {a b : Cl G} (h : a ≤ b) : nu a ≤ nu b := by
  classical
  unfold nu
  exact Fintype.card_le_of_embedding
    ⟨fun c ↦ ⟨c.1, c.2.1, c.2.2.trans h⟩, by
      intro c d hcd
      simp only [Subtype.mk.injEq] at hcd
      exact Subtype.ext hcd⟩

/-- Two disjoint blocks `S` and `T`, every other vertex alone. -/
def blk2Fun (S T : Finset V) (v : V) : Finset V := if v ∈ S then S else if v ∈ T then T else {v}

/-- The element with two disjoint (connected) blocks. -/
def blk2 (S T : Finset V) (hS : (G.induce (S : Set V)).Connected)
    (hT : (G.induce (T : Set V)).Connected) (hST : Disjoint S T) : Cl G :=
  ⟨blk2Fun S T, by
    have hfib : ∀ v, fib (blk2Fun S T) v = blk2Fun S T v := by
      intro v
      ext w
      rw [mem_fib]
      unfold blk2Fun
      by_cases hv : v ∈ S
      · rw [if_pos hv]
        by_cases hw : w ∈ S
        · simp [hw]
        · have hwS : (if w ∈ T then T else {w}) ≠ S := by
            split_ifs with hwT
            · intro h; exact Finset.disjoint_left.mp hST hv (by rw [h]; exact hv)
            · intro h; exact hw (h ▸ Finset.mem_singleton_self w)
          simp [hw, hwS]
      · rw [if_neg hv]
        by_cases hvT : v ∈ T
        · rw [if_pos hvT]
          by_cases hw : w ∈ S
          · have : S ≠ T := fun h ↦ hv (h ▸ hvT)
            simp only [hw, if_true, this, false_iff]
            exact fun hwT ↦ Finset.disjoint_left.mp hST hw hwT
          · by_cases hwT : w ∈ T
            · simp [hw, hwT]
            · have : ({w} : Finset V) ≠ T := fun h ↦ hwT (h ▸ Finset.mem_singleton_self w)
              simp [hw, hwT, this]
        · rw [if_neg hvT]
          by_cases hw : w ∈ S
          · have : S ≠ {v} := fun h ↦ hv (h ▸ Finset.mem_singleton_self v)
            simp only [hw, if_true, this, false_iff, Finset.mem_singleton]
            rintro rfl; exact hv hw
          · by_cases hwT : w ∈ T
            · have : T ≠ {v} := fun h ↦ hvT (h ▸ Finset.mem_singleton_self v)
              simp only [hw, hwT, if_true, if_false, this, false_iff, Finset.mem_singleton]
              rintro rfl; exact hvT hwT
            · simp [hw, hwT, Finset.singleton_inj, eq_comm]
    exact {
      eq_or_disjoint := fun v w ↦ by
        rcases eq_or_ne (blk2Fun S T v) (blk2Fun S T w) with h | h
        · exact Or.inl h
        · right
          unfold blk2Fun at h ⊢
          split_ifs at h ⊢ <;> first
            | exact absurd rfl h
            | exact hST
            | exact hST.symm
            | exact Finset.disjoint_singleton_right.mpr ‹_›
            | exact Finset.disjoint_singleton_left.mpr ‹_›
            | exact Finset.disjoint_singleton.mpr (fun e ↦ h (by rw [e]))
      card_eq := fun v ↦ by rw [hfib]
      connected := fun v ↦ by
        rw [hfib]
        unfold blk2Fun
        by_cases hv : v ∈ S
        · rw [if_pos hv]; exact hS
        · rw [if_neg hv]
          by_cases hvT : v ∈ T
          · rw [if_pos hvT]; exact hT
          · rw [if_neg hvT, Finset.coe_singleton]; exact connected_singleton v }⟩

lemma blk2_val {S T : Finset V} (hS : (G.induce (S : Set V)).Connected)
    (hT : (G.induce (T : Set V)).Connected) (hST : Disjoint S T) (v : V) :
    (blk2 S T hS hT hST).1 v = if v ∈ S then S else if v ∈ T then T else {v} := rfl

lemma blk_le_blk2_left {S T : Finset V} (hS : (G.induce (S : Set V)).Connected)
    (hT : (G.induce (T : Set V)).Connected) (hST : Disjoint S T) :
    blk S hS ≤ blk2 S T hS hT hST := fun v ↦ by
  rw [blk_val, blk2_val]
  split_ifs <;> simp_all

lemma blk_le_blk2_right {S T : Finset V} (hS : (G.induce (S : Set V)).Connected)
    (hT : (G.induce (T : Set V)).Connected) (hST : Disjoint S T) :
    blk T hT ≤ blk2 S T hS hT hST := fun v ↦ by
  rw [blk_val, blk2_val]
  by_cases hvT : v ∈ T
  · have hvS : v ∉ S := Finset.disjoint_right.mp hST hvT
    simp [hvT, hvS]
  · rw [if_neg hvT]
    split_ifs with h1 <;> simp [*]

/-- `ν` of two disjoint blocks is at most `|S|! |T|!`. -/
theorem nu_blk2_le {S T : Finset V} (hS : (G.induce (S : Set V)).Connected)
    (hT : (G.induce (T : Set V)).Connected) (hST : Disjoint S T) :
    nu (blk2 S T hS hT hST) ≤ S.card.factorial * T.card.factorial := by
  classical
  rw [nu_eq]
  have hmaps : ∀ p : {p : Equiv.Perm V // ∀ v, p v ∈ (blk2 S T hS hT hST).1 v},
      (∀ x, x ∈ S ↔ p.1 x ∈ S) ∧ (∀ x, x ∈ T ↔ p.1 x ∈ T) := by
    rintro ⟨p, hp⟩
    have hfix : ∀ x, x ∉ S → x ∉ T → p x = x := fun x hxS hxT ↦ by
      have := hp x
      rwa [blk2_val, if_neg hxS, if_neg hxT, Finset.mem_singleton] at this
    have hS' : ∀ x ∈ S, p x ∈ S := fun x hx ↦ by
      have := hp x; rwa [blk2_val, if_pos hx] at this
    have hT' : ∀ x ∈ T, p x ∈ T := fun x hx ↦ by
      have := hp x
      rwa [blk2_val, if_neg (Finset.disjoint_right.mp hST hx), if_pos hx] at this
    refine ⟨fun x ↦ ⟨hS' x, fun hpx ↦ ?_⟩, fun x ↦ ⟨hT' x, fun hpx ↦ ?_⟩⟩
    · by_contra hx
      by_cases hxT : x ∈ T
      · exact Finset.disjoint_left.mp hST hpx (hT' x hxT)
      · exact hx (hfix x hx hxT ▸ hpx)
    · by_contra hx
      by_cases hxS : x ∈ S
      · exact Finset.disjoint_left.mp hST (hS' x hxS) hpx
      · exact hx (hfix x hxS hx ▸ hpx)
  let f : {p : Equiv.Perm V // ∀ v, p v ∈ (blk2 S T hS hT hST).1 v} →
      Equiv.Perm {x // x ∈ S} × Equiv.Perm {x // x ∈ T} :=
    fun p ↦ (p.1.subtypePerm fun x ↦ ((hmaps p).1 x).symm,
      p.1.subtypePerm fun x ↦ ((hmaps p).2 x).symm)
  have hf : Function.Injective f := by
    rintro ⟨p, hp⟩ ⟨q, hq⟩ hpq
    simp only [f, Prod.mk.injEq] at hpq
    apply Subtype.ext
    ext x
    by_cases hxS : x ∈ S
    · have := congrArg (fun r : Equiv.Perm {x // x ∈ S} ↦ (r ⟨x, hxS⟩ : V)) hpq.1
      simpa using this
    by_cases hxT : x ∈ T
    · have := congrArg (fun r : Equiv.Perm {x // x ∈ T} ↦ (r ⟨x, hxT⟩ : V)) hpq.2
      simpa using this
    · have h1 := hp x
      have h2 := hq x
      rw [blk2_val, if_neg hxS, if_neg hxT, Finset.mem_singleton] at h1 h2
      rw [h1, h2]
  have := Fintype.card_le_of_injective f hf
  rwa [Fintype.card_prod, Fintype.card_perm, Fintype.card_perm, Fintype.card_coe,
    Fintype.card_coe] at this

/-! ### Meeting and triangles from the poset -/

open EdgeRecon in
lemma meet_iff_inter {e f : Sym2 V} : Meet e f ↔ (edgeFin e ∩ edgeFin f).Nonempty := by
  constructor
  · rintro ⟨v, hve, hvf⟩; exact ⟨v, Finset.mem_inter.mpr ⟨mem_edgeFin.mpr hve, mem_edgeFin.mpr hvf⟩⟩
  · rintro ⟨v, hv⟩
    rw [Finset.mem_inter, mem_edgeFin, mem_edgeFin] at hv
    exact ⟨v, hv⟩

/-- Distinct edges share at most one vertex. -/
lemma card_inter_le_one {e f : G.edgeSet} (hef : e ≠ f) :
    (edgeFin (e : Sym2 V) ∩ edgeFin (f : Sym2 V)).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro x hx y hy
  rw [Finset.mem_inter, mem_edgeFin, mem_edgeFin] at hx hy
  exact EdgeRecon.eq_of_mem_of_mem hef hx.1 hx.2 hy.1 hy.2

lemma card_union_of_meet {e f : G.edgeSet} (hef : e ≠ f)
    (h : (edgeFin (e : Sym2 V) ∩ edgeFin (f : Sym2 V)).Nonempty) :
    (edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V)).card = 3 := by
  have h1 := Finset.card_union_add_card_inter (edgeFin (e : Sym2 V)) (edgeFin (f : Sym2 V))
  have h2 := card_inter_le_one hef
  have h3 := Finset.card_pos.mpr h
  rw [card_edgeFin, card_edgeFin] at h1
  omega

open EdgeRecon in
/-- **Meeting from the poset.** Two distinct edges meet iff the join of their atoms exists and
has `ν = 6`; for disjoint edges every join has `ν ≤ 4`. -/
theorem meet_iff_nu {e f : G.edgeSet} (hef : e ≠ f) :
    Meet (e : Sym2 V) f ↔ ∃ y, IsLUB {atom e, atom f} y ∧ nu y = 6 := by
  rw [meet_iff_inter]
  constructor
  · intro h
    refine ⟨_, isLUB_blk_pair (connected_edgeFin e) (connected_edgeFin f) h, ?_⟩
    rw [nu_blk, card_union_of_meet hef h]
    rfl
  · rintro ⟨y, hy, hnu⟩
    by_contra h
    have hdisj : Disjoint (edgeFin (e : Sym2 V)) (edgeFin (f : Sym2 V)) :=
      Finset.disjoint_iff_inter_eq_empty.mpr (Finset.not_nonempty_iff_eq_empty.mp h)
    have hle : y ≤ blk2 _ _ (connected_edgeFin e) (connected_edgeFin f) hdisj := hy.2 (by
      rintro z (rfl | rfl)
      · exact blk_le_blk2_left _ _ _
      · exact blk_le_blk2_right _ _ _)
    have := (nu_mono hle).trans (nu_blk2_le _ _ hdisj)
    rw [hnu, card_edgeFin, card_edgeFin] at this
    exact absurd this (by decide)

open EdgeRecon in
/-- **Triangles from the poset.** Three edges form a triangle iff they pairwise meet, are
distinct, and the join of their atoms has `ν = 6` (it is `24` for three edges with a common
vertex). -/
theorem tri_iff_nu (e f g : G.edgeSet) :
    Tri (e : Sym2 V) f g ↔ Meet (e : Sym2 V) f ∧ Meet (f : Sym2 V) g ∧ Meet (e : Sym2 V) g ∧
      e ≠ f ∧ f ≠ g ∧ e ≠ g ∧ ∃ y, IsLUB {atom e, atom f, atom g} y ∧ nu y = 6 := by
  -- pairwise meeting distinct edges: the join is the single block `e ∪ f ∪ g`
  have hjoin : ∀ (hef : (edgeFin (e : Sym2 V) ∩ edgeFin (f : Sym2 V)).Nonempty)
      (hg : ((edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V)) ∩ edgeFin (g : Sym2 V)).Nonempty),
      IsLUB {atom e, atom f, atom g} (blk _ (connected_union (connected_union
        (connected_edgeFin e) (connected_edgeFin f) hef) (connected_edgeFin g) hg)) :=
    fun hef hg ↦ isLUB_blk_triple _ _ _ hef hg
  have hcard : ∀ (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g)
      (h1 : (edgeFin (e : Sym2 V) ∩ edgeFin (f : Sym2 V)).Nonempty)
      (h2 : (edgeFin (f : Sym2 V) ∩ edgeFin (g : Sym2 V)).Nonempty)
      (h3 : (edgeFin (e : Sym2 V) ∩ edgeFin (g : Sym2 V)).Nonempty),
      (edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V) ∪ edgeFin (g : Sym2 V)).card = 3 ↔
        ¬ ∃ v, v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V) ∧ v ∈ (g : Sym2 V) := by
    intro hef hfg heg h1 h2 h3
    have hEF := card_union_of_meet hef h1
    have hU := Finset.card_union_add_card_inter
      (edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V)) (edgeFin (g : Sym2 V))
    rw [hEF, card_edgeFin] at hU
    have hI : ((edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V)) ∩ edgeFin (g : Sym2 V)).card ≤ 2 :=
      (Finset.card_le_card Finset.inter_subset_right).trans (card_edgeFin g).le
    constructor
    · rintro hc ⟨c, hce, hcf, hcg⟩
      -- the other vertex of `g` lies in neither `e` nor `f`, so the intersection is `{c}`
      have hI1 : ((edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V)) ∩
          edgeFin (g : Sym2 V)).card ≤ 1 := by
        rw [Finset.card_le_one]
        intro x hx y hy
        simp only [Finset.mem_inter, Finset.mem_union, mem_edgeFin] at hx hy
        have hxc : x = c := by
          rcases hx.1 with hxe | hxf
          · exact EdgeRecon.eq_of_mem_of_mem heg hxe hx.2 hce hcg
          · exact EdgeRecon.eq_of_mem_of_mem hfg hxf hx.2 hcf hcg
        have hyc : y = c := by
          rcases hy.1 with hye | hyf
          · exact EdgeRecon.eq_of_mem_of_mem heg hye hy.2 hce hcg
          · exact EdgeRecon.eq_of_mem_of_mem hfg hyf hy.2 hcf hcg
        rw [hxc, hyc]
      omega
    · intro hno
      -- `g` meets `e` and `f` in two distinct vertices
      obtain ⟨x, hx⟩ := h3
      obtain ⟨y, hy⟩ := h2
      rw [Finset.mem_inter, mem_edgeFin, mem_edgeFin] at hx hy
      have hxy : x ≠ y := by
        rintro rfl
        exact hno ⟨x, hx.1, hy.1, hx.2⟩
      have hI2 : 2 ≤ ((edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V)) ∩
          edgeFin (g : Sym2 V)).card := by
        rw [← Finset.card_pair hxy]
        apply Finset.card_le_card
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        simp only [Finset.mem_inter, Finset.mem_union, mem_edgeFin]
        rcases hz with rfl | rfl
        · exact ⟨Or.inl hx.1, hx.2⟩
        · exact ⟨Or.inr hy.1, hy.2⟩
      omega
  constructor
  · intro ht
    obtain ⟨hm1, hm2, hm3, hno⟩ := ht
    have hef : e ≠ f := by
      rintro rfl
      obtain ⟨x, hx1, hx2⟩ := hm3
      exact hno ⟨x, hx1, hx1, hx2⟩
    have hfg : f ≠ g := by
      rintro rfl
      obtain ⟨x, hx1, hx2⟩ := hm1
      exact hno ⟨x, hx1, hx2, hx2⟩
    have heg : e ≠ g := by
      rintro rfl
      obtain ⟨x, hx1, hx2⟩ := hm1
      exact hno ⟨x, hx1, hx2, hx1⟩
    have h1 := meet_iff_inter.mp hm1
    have h2 := meet_iff_inter.mp hm2
    have h3 := meet_iff_inter.mp hm3
    have hg : ((edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V)) ∩ edgeFin (g : Sym2 V)).Nonempty :=
      h3.mono (Finset.inter_subset_inter_right Finset.subset_union_left)
    refine ⟨hm1, hm2, hm3, hef, hfg, heg, _, hjoin h1 hg, ?_⟩
    rw [nu_blk, (hcard hef hfg heg h1 h2 h3).mpr hno]
    rfl
  · rintro ⟨hm1, hm2, hm3, hef, hfg, heg, y, hy, hnu⟩
    have h1 := meet_iff_inter.mp hm1
    have h2 := meet_iff_inter.mp hm2
    have h3 := meet_iff_inter.mp hm3
    have hg : ((edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V)) ∩ edgeFin (g : Sym2 V)).Nonempty :=
      h3.mono (Finset.inter_subset_inter_right Finset.subset_union_left)
    have hyeq := hy.unique (hjoin h1 hg)
    rw [hyeq, nu_blk] at hnu
    refine ⟨hm1, hm2, hm3, (hcard hef hfg heg h1 h2 h3).mp ?_⟩
    -- `k! = 6` forces `k = 3`
    set k := (edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V) ∪ edgeFin (g : Sym2 V)).card
    have hk : 3 ≤ k := by
      have := card_union_of_meet hef h1
      exact this ▸ Finset.card_le_card Finset.subset_union_left
    have hk4 : k ≤ 4 := by
      have hU := Finset.card_union_add_card_inter
        (edgeFin (e : Sym2 V) ∪ edgeFin (f : Sym2 V)) (edgeFin (g : Sym2 V))
      rw [card_union_of_meet hef h1, card_edgeFin] at hU
      have := Finset.card_pos.mpr hg
      omega
    rcases (show k = 3 ∨ k = 4 by omega) with hk3 | hk4'
    · exact hk3
    · rw [hk4'] at hnu
      exact absurd hnu (by decide)

/-! ### Relabelling -/

lemma isCl_map (σ : Equiv.Perm V) (a : Cl G) :
    IsCl G (fun v ↦ (a.1 v).map σ.toEmbedding) := by
  have hfib : ∀ v, fib (fun v ↦ (a.1 v).map σ.toEmbedding) v = fib a.1 v := by
    intro v; ext w; simp [mem_fib, Finset.map_inj]
  exact {
    eq_or_disjoint := fun v w ↦ by
      rcases a.2.eq_or_disjoint v w with h | h
      · exact Or.inl (by rw [h])
      · exact Or.inr (by rwa [Finset.disjoint_map])
    card_eq := fun v ↦ by rw [hfib, Finset.card_map, a.2.card_eq]
    connected := fun v ↦ by rw [hfib]; exact a.2.connected v }

/-- Relabelling by a permutation `σ` of the labels is an automorphism of `Cl_Γ`. -/
def relabel (σ : Equiv.Perm V) : Cl G ≃o Cl G where
  toFun a := ⟨fun v ↦ (a.1 v).map σ.toEmbedding, isCl_map σ a⟩
  invFun a := ⟨fun v ↦ (a.1 v).map σ.symm.toEmbedding, isCl_map σ.symm a⟩
  left_inv a := by
    apply Subtype.ext; funext v; simp [Finset.map_map]
  right_inv a := by
    apply Subtype.ext; funext v; simp [Finset.map_map]
  map_rel_iff' {a b} := by
    show (∀ v, (a.1 v).map σ.toEmbedding ⊆ (b.1 v).map σ.toEmbedding) ↔ ∀ v, a.1 v ⊆ b.1 v
    simp only [Finset.map_subset_map]

lemma relabel_sing (σ p : Equiv.Perm V) : relabel (G := G) σ (sing p) = sing (p.trans σ) := by
  apply Subtype.ext; funext v
  simp [relabel, sing]

/-! ### Transport along an order isomorphism -/

section Transport

variable {V' : Type*} [Fintype V'] [DecidableEq V'] {G' : SimpleGraph V'}

lemma isMin_map (Φ : Cl G ≃o Cl G') {a : Cl G} : IsMin (Φ a) ↔ IsMin a := by
  constructor
  · intro h c hc
    exact Φ.le_iff_le.mp (h (Φ.monotone hc))
  · intro h c hc
    have h1 : Φ.symm c ≤ a := by simpa using Φ.symm.monotone hc
    simpa using Φ.monotone (h h1)

lemma nu_map (Φ : Cl G ≃o Cl G') (a : Cl G) : nu (Φ a) = nu a := by
  classical
  unfold nu
  refine (Fintype.card_congr (Φ.toEquiv.subtypeEquiv fun b ↦ ?_)).symm
  rw [OrderIso.coe_toEquiv, isMin_map Φ, Φ.le_iff_le]

lemma exists_atom (Ψ : Cl G ≃o Cl G') (hΨ : Ψ base = base) (e : G.edgeSet) :
    ∃ e' : G'.edgeSet, Ψ (atom e) = atom e' := by
  have h : base ⋖ atom e := covBy_base_iff.mpr ⟨e, rfl⟩
  rw [← apply_covBy_apply_iff Ψ, hΨ] at h
  exact covBy_base_iff.mp h

lemma symm_base (Ψ : Cl G ≃o Cl G') (hΨ : Ψ base = base) : Ψ.symm base = base := by
  rw [← hΨ, OrderIso.symm_apply_apply]

/-- The bijection of edges induced by a base-preserving isomorphism of cluster-permutohedra. -/
noncomputable def edgeEquiv (Ψ : Cl G ≃o Cl G') (hΨ : Ψ base = base) :
    G.edgeSet ≃ G'.edgeSet where
  toFun e := (exists_atom Ψ hΨ e).choose
  invFun e' := (exists_atom Ψ.symm (symm_base Ψ hΨ) e').choose
  left_inv e := by
    apply atom_injective (G := G)
    have h1 := (exists_atom Ψ hΨ e).choose_spec
    have h2 := (exists_atom Ψ.symm (symm_base Ψ hΨ) (exists_atom Ψ hΨ e).choose).choose_spec
    rw [← h2, ← h1, OrderIso.symm_apply_apply]
  right_inv e' := by
    apply atom_injective (G := G')
    have h1 := (exists_atom Ψ.symm (symm_base Ψ hΨ) e').choose_spec
    have h2 := (exists_atom Ψ hΨ (exists_atom Ψ.symm (symm_base Ψ hΨ) e').choose).choose_spec
    rw [← h2, ← h1, OrderIso.apply_symm_apply]

lemma apply_atom (Ψ : Cl G ≃o Cl G') (hΨ : Ψ base = base) (e : G.edgeSet) :
    Ψ (atom e) = atom (edgeEquiv Ψ hΨ e) :=
  (exists_atom Ψ hΨ e).choose_spec

/-- A property of joins of atoms with given `ν` is transported along `Ψ`. -/
lemma exists_lub_nu_iff (Ψ : Cl G ≃o Cl G') (s : Set (Cl G)) (n : ℕ) :
    (∃ y, IsLUB s y ∧ nu y = n) ↔ ∃ y', IsLUB (Ψ '' s) y' ∧ nu y' = n := by
  constructor
  · rintro ⟨y, hy, hn⟩
    exact ⟨Ψ y, (OrderIso.isLUB_image' Ψ).mpr hy, (nu_map Ψ y).trans hn⟩
  · rintro ⟨y', hy', hn⟩
    exact ⟨Ψ.symm y', (OrderIso.isLUB_image Ψ).mp hy', (nu_map Ψ.symm y').trans hn⟩

open EdgeRecon in
/-- A base-preserving isomorphism of cluster-permutohedra induces an edge bijection that
preserves meeting and triangles. -/
noncomputable def edgeIso (Ψ : Cl G ≃o Cl G') (hΨ : Ψ base = base) : EdgeIso G G' where
  toEquiv := edgeEquiv Ψ hΨ
  meet_iff e f := by
    by_cases hef : e = f
    · subst hef
      exact ⟨fun _ ↦ ⟨_, Sym2.out_fst_mem _, Sym2.out_fst_mem _⟩,
        fun _ ↦ ⟨_, Sym2.out_fst_mem _, Sym2.out_fst_mem _⟩⟩
    rw [meet_iff_nu hef, meet_iff_nu ((edgeEquiv Ψ hΨ).injective.ne hef),
      exists_lub_nu_iff Ψ, Set.image_pair, apply_atom, apply_atom]
  tri_iff e f g := by
    rw [tri_iff_nu, tri_iff_nu, exists_lub_nu_iff Ψ, Set.image_insert_eq, Set.image_pair,
      apply_atom, apply_atom, apply_atom]
    have hm : ∀ x y : G.edgeSet, Meet (x : Sym2 V) y ↔
        Meet (edgeEquiv Ψ hΨ x : Sym2 V') (edgeEquiv Ψ hΨ y) := by
      intro x y
      by_cases hxy : x = y
      · subst hxy
        exact ⟨fun _ ↦ ⟨_, Sym2.out_fst_mem _, Sym2.out_fst_mem _⟩,
          fun _ ↦ ⟨_, Sym2.out_fst_mem _, Sym2.out_fst_mem _⟩⟩
      rw [meet_iff_nu hxy, meet_iff_nu ((edgeEquiv Ψ hΨ).injective.ne hxy),
        exists_lub_nu_iff Ψ, Set.image_pair, apply_atom, apply_atom]
    have hne : ∀ x y : G.edgeSet, x ≠ y ↔ edgeEquiv Ψ hΨ x ≠ edgeEquiv Ψ hΨ y :=
      fun x y ↦ (edgeEquiv Ψ hΨ).injective.ne_iff.symm
    rw [hm e f, hm f g, hm e g, hne e f, hne f g, hne e g]

open Classical in
lemma card_min_eq (Φ : Cl G ≃o Cl G') :
    Fintype.card {a : Cl G // IsMin a} = Fintype.card {a : Cl G' // IsMin a} :=
  Fintype.card_congr (Φ.toEquiv.subtypeEquiv fun _ ↦ (isMin_map Φ).symm)

/-- **Theorem A.** For simple graphs on nonempty finite vertex types, an isomorphism of
cluster-permutohedra `Cl_Γ ≃o Cl_Γ'` implies `Γ ≃g Γ'`. -/
theorem cl_rigid [Nonempty V] [Nonempty V'] (Φ : Cl G ≃o Cl G') : Nonempty (G ≃g G') := by
  classical
  -- `|V|! = |V'|!`, hence `|V| = |V'|`
  have hfact : (Fintype.card V).factorial = (Fintype.card V').factorial := by
    rw [← card_min (G := G), ← card_min (G := G'), card_min_eq Φ]
  have hcard : Fintype.card V = Fintype.card V' := by
    have h1 := Fintype.card_pos (α := V)
    have h2 := Fintype.card_pos (α := V')
    by_cases h : 1 < Fintype.card V ∨ 1 < Fintype.card V'
    · exact (Nat.factorial_inj' h).mp hfact
    · omega
  -- move the image of the base point back to the base point by relabelling
  obtain ⟨p, hp⟩ := isMin_iff.mp ((isMin_map Φ).mpr (isMin_iff.mpr ⟨Equiv.refl V, rfl⟩) :
    IsMin (Φ (base (G := G))))
  let Ψ : Cl G ≃o Cl G' := Φ.trans (relabel p.symm)
  have hΨ : Ψ base = base := by
    simp only [Ψ, OrderIso.trans_apply, hp, relabel_sing, Equiv.self_trans_symm]
    rfl
  exact (edgeIso Ψ hΨ).nonempty_iso hcard

end Transport

end Cluster

end MatroidToric
