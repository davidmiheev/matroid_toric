import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fintype.Card

/-!
# Reconstructing a graph from adjacency and triangles of its edges (Theorem A, first step)

Thesis v2, Lemma 4.33 and Proposition 4.34; `experiments/question1/PROOF.md`, Lemma 2 and
Proposition 3.

Let `φ` be a bijection between the edge sets of two simple graphs such that `φ` and `φ⁻¹`
preserve *meeting* (sharing a vertex) and *triangles* (three edges that pairwise meet without a
common vertex). Then `φ` is induced by a bijection `ψ` between the non-isolated vertices:
`φ s(u, v) = s(ψ u, ψ v)` for every edge. Unlike Whitney's line-graph theorem this has no
exceptions, because triangles are part of the data.

In the cluster-permutohedron `Cl_Γ`, meeting and triangles of edges are read off from the poset
(the number of minimal elements below a join of two atoms, and the rank of a join of three), so
this is the graph-theoretic heart of `Cl_Γ ≅ Cl_Γ' ⇒ Γ ≅ Γ'`.

## Main definitions

* `EdgeRecon.Meet`, `EdgeRecon.Tri` : two edges meet; three edges form a triangle.
* `EdgeRecon.EdgeIso G H` : an edge bijection preserving `Meet` and `Tri`.
* `EdgeRecon.Big G v` : `v` lies on at least two edges.
* `EdgeIso.center` : for a vertex `v` on at least two edges, the common vertex of the images of
  all edges at `v` (the star lemma).

## Main results

* `EdgeIso.exists_center` : the images of the edges at a vertex with at least two edges all pass
  through one vertex.
* `EdgeIso.symm_center_center` : `center` is a bijection between such vertices.
* `EdgeIso.exists_support_equiv` : `φ` is induced by a bijection of the non-isolated vertices.
* `EdgeIso.nonempty_iso` : for finite graphs with the same number of vertices, `G ≃g H`.
-/

namespace MatroidToric

namespace EdgeRecon

variable {V W : Type*}

/-- Two edges meet if they share a vertex. -/
def Meet (e f : Sym2 V) : Prop := ∃ v, v ∈ e ∧ v ∈ f

/-- Three edges form a triangle: they pairwise meet but have no common vertex. -/
def Tri (e f g : Sym2 V) : Prop :=
  Meet e f ∧ Meet f g ∧ Meet e g ∧ ¬ ∃ v, v ∈ e ∧ v ∈ f ∧ v ∈ g

/-- An edge bijection that preserves meeting and triangles. Its inverse does too
(`EdgeIso.symm`), since the conditions are stated as equivalences. -/
structure EdgeIso (G : SimpleGraph V) (H : SimpleGraph W) where
  /-- The bijection of edge sets. -/
  toEquiv : G.edgeSet ≃ H.edgeSet
  meet_iff : ∀ e f : G.edgeSet, Meet (e : Sym2 V) f ↔ Meet (toEquiv e : Sym2 W) (toEquiv f)
  tri_iff : ∀ e f g : G.edgeSet,
    Tri (e : Sym2 V) f g ↔ Tri (toEquiv e : Sym2 W) (toEquiv f) (toEquiv g)

/-- `v` lies on at least two distinct edges. -/
def Big (G : SimpleGraph V) (v : V) : Prop :=
  ∃ e f : G.edgeSet, e ≠ f ∧ v ∈ (e : Sym2 V) ∧ v ∈ (f : Sym2 V)

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- Two distinct edges of a simple graph have at most one common vertex. -/
lemma eq_of_mem_of_mem {e f : G.edgeSet} (hef : e ≠ f) {x y : V}
    (hxe : x ∈ (e : Sym2 V)) (hxf : x ∈ (f : Sym2 V))
    (hye : y ∈ (e : Sym2 V)) (hyf : y ∈ (f : Sym2 V)) : x = y := by
  by_contra hxy
  exact hef (Subtype.ext (Sym2.eq_of_ne_mem hxy hxe hye hxf hyf))

namespace EdgeIso

variable (φ : EdgeIso G H)

/-- The inverse edge bijection. -/
def symm : EdgeIso H G where
  toEquiv := φ.toEquiv.symm
  meet_iff e f := by
    rw [φ.meet_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  tri_iff e f g := by
    rw [φ.tri_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply, Equiv.apply_symm_apply]

@[simp] lemma symm_apply_apply (e : G.edgeSet) : φ.symm.toEquiv (φ.toEquiv e) = e :=
  φ.toEquiv.symm_apply_apply e

@[simp] lemma apply_symm_apply (e : H.edgeSet) : φ.toEquiv (φ.symm.toEquiv e) = e :=
  φ.toEquiv.apply_symm_apply e

/-- **Star lemma.** If `v` lies on two distinct edges, the images of all edges at `v` pass
through one vertex. -/
theorem exists_center {v : V} (hv : Big G v) :
    ∃ w, ∀ g : G.edgeSet, v ∈ (g : Sym2 V) → w ∈ (φ.toEquiv g : Sym2 W) := by
  obtain ⟨e, f, hef, hve, hvf⟩ := hv
  obtain ⟨w, hwe, hwf⟩ := (φ.meet_iff e f).mp ⟨v, hve, hvf⟩
  refine ⟨w, fun g hvg ↦ ?_⟩
  by_cases hge : g = e
  · exact hge ▸ hwe
  by_cases hgf : g = f
  · exact hgf ▸ hwf
  -- `e, f, g` share `v`, so they do not form a triangle, and neither do their images
  have hnot : ¬ Tri (φ.toEquiv e : Sym2 W) (φ.toEquiv f) (φ.toEquiv g) := by
    rw [← φ.tri_iff]
    exact fun h ↦ h.2.2.2 ⟨v, hve, hvf, hvg⟩
  have hfg := (φ.meet_iff f g).mp ⟨v, hvf, hvg⟩
  have heg := (φ.meet_iff e g).mp ⟨v, hve, hvg⟩
  have hcommon : ∃ x, x ∈ (φ.toEquiv e : Sym2 W) ∧ x ∈ (φ.toEquiv f : Sym2 W) ∧
      x ∈ (φ.toEquiv g : Sym2 W) := by
    by_contra h
    exact hnot ⟨⟨w, hwe, hwf⟩, hfg, heg, h⟩
  obtain ⟨x, hxe, hxf, hxg⟩ := hcommon
  have hφef : φ.toEquiv e ≠ φ.toEquiv f := φ.toEquiv.injective.ne hef
  rwa [eq_of_mem_of_mem hφef hwe hwf hxe hxf]

/-- The common vertex of the images of the edges at a vertex with at least two edges. -/
noncomputable def center {v : V} (hv : Big G v) : W := (φ.exists_center hv).choose

lemma center_mem {v : V} (hv : Big G v) {g : G.edgeSet} (hg : v ∈ (g : Sym2 V)) :
    φ.center hv ∈ (φ.toEquiv g : Sym2 W) :=
  (φ.exists_center hv).choose_spec g hg

/-- `center` is characterized by lying on the images of two distinct edges at `v`. -/
lemma center_eq {v : V} (hv : Big G v) {e f : G.edgeSet} (hef : e ≠ f)
    (hve : v ∈ (e : Sym2 V)) (hvf : v ∈ (f : Sym2 V)) {w : W}
    (hwe : w ∈ (φ.toEquiv e : Sym2 W)) (hwf : w ∈ (φ.toEquiv f : Sym2 W)) :
    φ.center hv = w :=
  eq_of_mem_of_mem (φ.toEquiv.injective.ne hef) (φ.center_mem hv hve) (φ.center_mem hv hvf)
    hwe hwf

lemma big_center {v : V} (hv : Big G v) : Big H (φ.center hv) := by
  obtain ⟨e, f, hef, hve, hvf⟩ := hv
  exact ⟨φ.toEquiv e, φ.toEquiv f, φ.toEquiv.injective.ne hef,
    φ.center_mem _ hve, φ.center_mem _ hvf⟩

/-- `center` for `φ⁻¹` inverts `center` for `φ`. -/
theorem symm_center_center {v : V} (hv : Big G v) :
    φ.symm.center (φ.big_center hv) = v := by
  obtain ⟨e, f, hef, hve, hvf⟩ := id hv
  have h1 := φ.symm.center_mem (φ.big_center hv) (g := φ.toEquiv e) (φ.center_mem hv hve)
  have h2 := φ.symm.center_mem (φ.big_center hv) (g := φ.toEquiv f) (φ.center_mem hv hvf)
  simp only [symm_apply_apply] at h1 h2
  exact eq_of_mem_of_mem hef h1 h2 hve hvf


lemma symm_symm : φ.symm.symm = φ := rfl

lemma center_congr {u u' : V} (h : u = u') (hu : Big G u) (hu' : Big G u') :
    φ.center hu = φ.center hu' := by
  subst h; rfl

/-- If a Big vertex `w` of `H` lies on `φ g`, then `φ⁻¹`'s center of `w` lies on `g`. -/
lemma symm_center_mem {w : W} (hw : Big H w) {g : G.edgeSet}
    (hg : w ∈ (φ.toEquiv g : Sym2 W)) : φ.symm.center hw ∈ (g : Sym2 V) := by
  simpa using φ.symm.center_mem hw (g := φ.toEquiv g) hg

end EdgeIso

/-- `v` lies on some edge, i.e. `v` is not isolated. -/
def OnEdge (G : SimpleGraph V) (v : V) : Prop := ∃ g : G.edgeSet, v ∈ (g : Sym2 V)

lemma onEdge_iff_mem_support {v : V} : OnEdge G v ↔ v ∈ G.support := by
  constructor
  · rintro ⟨⟨g, hg⟩, hvg⟩
    induction g using Sym2.ind with
    | h a b =>
      rcases Sym2.mem_iff.mp hvg with rfl | rfl
      · exact ⟨b, hg⟩
      · exact ⟨a, hg.symm⟩
  · rintro ⟨w, hw⟩
    exact ⟨⟨s(v, w), hw⟩, Sym2.mem_mk_left v w⟩

/-- A vertex that is not Big lies on at most one edge. -/
lemma eq_of_not_big {v : V} (hv : ¬ Big G v) {g g' : G.edgeSet} (hg : v ∈ (g : Sym2 V))
    (hg' : v ∈ (g' : Sym2 V)) : g = g' := by
  by_contra h
  exact hv ⟨g, g', h, hg, hg'⟩

/-- In an edge `e` of a simple graph containing `v`, there is only one vertex other than `v`. -/
lemma eq_of_mem_of_ne {e : G.edgeSet} {v x y : V} (hv : v ∈ (e : Sym2 V))
    (hx : x ∈ (e : Sym2 V)) (hy : y ∈ (e : Sym2 V)) (hxv : x ≠ v) (hyv : y ≠ v) : x = y := by
  have he : (e : Sym2 V) = s(v, x) := (Sym2.mem_and_mem_iff hxv.symm).mp ⟨hv, hx⟩
  rw [he, Sym2.mem_iff] at hy
  exact (hy.resolve_left hyv).symm

/-- An edge of a simple graph has a vertex other than any given one of its vertices. -/
lemma exists_ne_mem {e : G.edgeSet} {v : V} (hv : v ∈ (e : Sym2 V)) :
    ∃ x, x ∈ (e : Sym2 V) ∧ x ≠ v :=
  ⟨Sym2.Mem.other hv, Sym2.other_mem hv,
    Sym2.other_ne (G.not_isDiag_of_mem_edgeSet e.2) hv⟩

/-- The two components of `Sym2.out` of an edge are distinct. -/
lemma out_ne (e : G.edgeSet) : (e : Sym2 V).out.1 ≠ (e : Sym2 V).out.2 := by
  intro h
  apply G.not_isDiag_of_mem_edgeSet e.2
  rw [← Sym2.mk_fst_out_snd_out (e : Sym2 V), h]
  exact Sym2.mk_isDiag_iff.mpr rfl

lemma eq_out_of_mem {e : G.edgeSet} {v : V} (hv : v ∈ (e : Sym2 V))
    (h : v ≠ (e : Sym2 V).out.1) : v = (e : Sym2 V).out.2 := by
  have := hv
  rw [← Sym2.mk_fst_out_snd_out (e : Sym2 V), Sym2.mem_iff] at this
  exact this.resolve_left h

namespace EdgeIso

variable (φ : EdgeIso G H)

open Classical in
/-- The vertex map. A vertex on two or more edges goes to its `center`. A leaf `v` on the edge
`g`, whose other endpoint `u` is on two or more edges, goes to the endpoint of `φ g` other than
`center u`. Both endpoints of an isolated edge `g` go to the endpoints of `φ g`, matched through
`Sym2.out`. -/
noncomputable def psi (v : V) (hv : OnEdge G v) : W :=
  if hb : Big G v then φ.center hb
  else if hK : ∃ u, u ∈ (hv.choose : Sym2 V) ∧ u ≠ v ∧ Big G u then
    Sym2.Mem.other (φ.center_mem hK.choose_spec.2.2 hK.choose_spec.1)
  else if v = (hv.choose : Sym2 V).out.1 then (φ.toEquiv hv.choose : Sym2 W).out.1
  else (φ.toEquiv hv.choose : Sym2 W).out.2

lemma psi_of_big {v : V} (hv : OnEdge G v) (hb : Big G v) : φ.psi v hv = φ.center hb := by
  simp [psi, hb]

lemma psi_spec_leaf {v : V} (hv : OnEdge G v) (hb : ¬ Big G v) {g : G.edgeSet}
    (hvg : v ∈ (g : Sym2 V)) {u : V} (hug : u ∈ (g : Sym2 V)) (huv : u ≠ v) (hu : Big G u) :
    φ.psi v hv ∈ (φ.toEquiv g : Sym2 W) ∧ φ.psi v hv ≠ φ.center hu := by
  have hg : hv.choose = g := eq_of_not_big hb hv.choose_spec hvg
  have hK : ∃ u, u ∈ (hv.choose : Sym2 V) ∧ u ≠ v ∧ Big G u := ⟨u, hg ▸ hug, huv, hu⟩
  have hpsi : φ.psi v hv =
      Sym2.Mem.other (φ.center_mem hK.choose_spec.2.2 hK.choose_spec.1) := by
    simp [psi, hb, hK]
  have hu' : hK.choose = u :=
    eq_of_mem_of_ne (hg ▸ hvg) hK.choose_spec.1 (hg ▸ hug) hK.choose_spec.2.1 huv
  rw [← hg, hpsi, φ.center_congr hu'.symm hu hK.choose_spec.2.2]
  exact ⟨Sym2.other_mem _,
    Sym2.other_ne (H.not_isDiag_of_mem_edgeSet (φ.toEquiv hv.choose).2) _⟩

open Classical in
lemma psi_of_isolated_edge {v : V} (hv : OnEdge G v) (hb : ¬ Big G v) {g : G.edgeSet}
    (hvg : v ∈ (g : Sym2 V)) (hK : ∀ u, u ∈ (g : Sym2 V) → u ≠ v → ¬ Big G u) :
    φ.psi v hv = if v = (g : Sym2 V).out.1 then (φ.toEquiv g : Sym2 W).out.1
      else (φ.toEquiv g : Sym2 W).out.2 := by
  have hg : hv.choose = g := eq_of_not_big hb hv.choose_spec hvg
  have hK' : ¬ ∃ u, u ∈ (hv.choose : Sym2 V) ∧ u ≠ v ∧ Big G u := by
    rintro ⟨u, hu, huv, hub⟩
    exact hK u (hg ▸ hu) huv hub
  simp only [psi, hb, hK', dite_false]
  rw [hg]

/-- `ψ v` lies on the image of every edge at `v`. -/
theorem psi_mem {v : V} (hv : OnEdge G v) {g : G.edgeSet} (hvg : v ∈ (g : Sym2 V)) :
    φ.psi v hv ∈ (φ.toEquiv g : Sym2 W) := by
  by_cases hb : Big G v
  · rw [φ.psi_of_big hv hb]
    exact φ.center_mem hb hvg
  obtain ⟨u, hug, huv⟩ := exists_ne_mem hvg
  by_cases hu : Big G u
  · exact (φ.psi_spec_leaf hv hb hvg hug huv hu).1
  · have hK : ∀ u', u' ∈ (g : Sym2 V) → u' ≠ v → ¬ Big G u' := fun u' hu' hu'v ↦
      (eq_of_mem_of_ne hvg hu' hug hu'v huv) ▸ hu
    rw [φ.psi_of_isolated_edge hv hb hvg hK]
    split_ifs
    · exact Sym2.out_fst_mem _
    · exact Sym2.out_snd_mem _

lemma onEdge_psi {v : V} (hv : OnEdge G v) : OnEdge H (φ.psi v hv) :=
  ⟨φ.toEquiv hv.choose, φ.psi_mem hv hv.choose_spec⟩

/-- A vertex of `H` on `φ g` that is Big comes from a Big vertex on `g`. -/
lemma not_big_of_mem {v : V} (hb : ¬ Big G v) {g : G.edgeSet} (hvg : v ∈ (g : Sym2 V))
    {u : V} (hug : u ∈ (g : Sym2 V)) (huv : u ≠ v) (hu : ¬ Big G u)
    {w : W} (hw : w ∈ (φ.toEquiv g : Sym2 W)) : ¬ Big H w := by
  intro hwb
  have hc := φ.symm_center_mem hwb hw
  have hcb := φ.symm.big_center hwb
  by_cases hcv : φ.symm.center hwb = v
  · exact hb (hcv ▸ hcb)
  · exact hu ((eq_of_mem_of_ne hvg hc hug hcv huv) ▸ hcb)

/-- `ψ⁻¹ ∘ ψ = id`, where `ψ⁻¹` is the vertex map of `φ⁻¹`. Stated with `w = ψ v` as a free
variable to avoid dependent rewriting. -/
theorem symm_psi_eq {v : V} (hv : OnEdge G v) {w : W} (hw : OnEdge H w)
    (hwv : φ.psi v hv = w) : φ.symm.psi w hw = v := by
  by_cases hb : Big G v
  · have h1 : w = φ.center hb := hwv ▸ φ.psi_of_big hv hb
    have hxb : Big H w := h1 ▸ φ.big_center hb
    rw [φ.symm.psi_of_big hw hxb, φ.symm.center_congr h1 hxb (φ.big_center hb),
      φ.symm_center_center]
  obtain ⟨g, hvg⟩ := id hv
  obtain ⟨u, hug, huv⟩ := exists_ne_mem hvg
  have hwg : w ∈ (φ.toEquiv g : Sym2 W) := hwv ▸ φ.psi_mem hv hvg
  by_cases hu : Big G u
  · -- `v` is a leaf attached to the Big vertex `u`
    have hwc : w ≠ φ.center hu := hwv ▸ (φ.psi_spec_leaf hv hb hvg hug huv hu).2
    have hcu : φ.center hu ∈ (φ.toEquiv g : Sym2 W) := φ.center_mem hu hug
    have hwb : ¬ Big H w := by
      intro hwb
      have hc := φ.symm_center_mem hwb hwg
      have hcb := φ.symm.big_center hwb
      have hcu' : φ.symm.center hwb = u := by
        by_contra hne
        exact hb ((eq_of_mem_of_ne hug hc hvg hne huv.symm) ▸ hcb)
      obtain ⟨a, b, hab, hwa, hwb'⟩ := id hwb
      have ha := φ.symm.center_mem hwb hwa
      have hb' := φ.symm.center_mem hwb hwb'
      rw [hcu'] at ha hb'
      exact hwc (φ.center_eq hu (φ.symm.toEquiv.injective.ne hab) ha hb'
        (by simpa using hwa) (by simpa using hwb')).symm
    obtain ⟨hmem, hne⟩ := φ.symm.psi_spec_leaf hw hwb hwg hcu hwc.symm (φ.big_center hu)
    simp only [symm_apply_apply] at hmem
    rw [φ.symm_center_center hu] at hne
    by_contra hne'
    exact hne (eq_of_mem_of_ne hvg hmem hug hne' huv)
  · -- `g` is an isolated edge
    have hK : ∀ u', u' ∈ (g : Sym2 V) → u' ≠ v → ¬ Big G u' := fun u' hu' hu'v ↦
      (eq_of_mem_of_ne hvg hu' hug hu'v huv) ▸ hu
    have hwb : ¬ Big H w := φ.not_big_of_mem hb hvg hug huv hu hwg
    have hK' : ∀ x, x ∈ (φ.toEquiv g : Sym2 W) → x ≠ w → ¬ Big H x := fun x hx _ ↦
      φ.not_big_of_mem hb hvg hug huv hu hx
    have hpsi := φ.psi_of_isolated_edge hv hb hvg hK
    have hpsi' := φ.symm.psi_of_isolated_edge hw hwb hwg hK'
    simp only [symm_apply_apply] at hpsi'
    rw [hpsi', ← hwv, hpsi]
    by_cases h1 : v = (g : Sym2 V).out.1
    · simp [h1]
    · have h2 : (φ.toEquiv g : Sym2 W).out.2 ≠ (φ.toEquiv g : Sym2 W).out.1 :=
        (out_ne (φ.toEquiv g)).symm
      rw [ite_eq_right h1, ite_eq_right h2]
      exact (eq_out_of_mem hvg h1).symm

theorem symm_psi_psi {v : V} (hv : OnEdge G v) :
    φ.symm.psi (φ.psi v hv) (φ.onEdge_psi hv) = v :=
  φ.symm_psi_eq hv _ rfl


/-- The bijection between non-isolated vertices induced by `φ`. -/
noncomputable def vertexEquiv : {v // OnEdge G v} ≃ {w // OnEdge H w} where
  toFun v := ⟨φ.psi v.1 v.2, φ.onEdge_psi v.2⟩
  invFun w := ⟨φ.symm.psi w.1 w.2, φ.symm.onEdge_psi w.2⟩
  left_inv v := Subtype.ext (φ.symm_psi_psi v.2)
  right_inv w := Subtype.ext (φ.symm.symm_psi_psi w.2)

@[simp] lemma vertexEquiv_apply (v : {v // OnEdge G v}) :
    (φ.vertexEquiv v : W) = φ.psi v.1 v.2 := rfl

lemma psi_injective {u v : V} (hu : OnEdge G u) (hv : OnEdge G v)
    (h : φ.psi u hu = φ.psi v hv) : u = v := by
  have h1 := φ.symm_psi_eq hu (φ.onEdge_psi hu) rfl
  have h2 := φ.symm_psi_eq hv (φ.onEdge_psi hu) h.symm
  exact h1.symm.trans h2

/-- **Proposition (edge reconstruction).** `φ` maps the edge `uv` to the edge `ψ(u)ψ(v)`. -/
theorem apply_eq {u v : V} (h : G.Adj u v) (hu : OnEdge G u) (hv : OnEdge G v) :
    (φ.toEquiv ⟨s(u, v), h⟩ : Sym2 W) = s(φ.psi u hu, φ.psi v hv) := by
  have hne : φ.psi u hu ≠ φ.psi v hv := fun he ↦ h.ne (φ.psi_injective hu hv he)
  exact (Sym2.mem_and_mem_iff hne).mp
    ⟨φ.psi_mem hu (Sym2.mem_mk_left u v), φ.psi_mem hv (Sym2.mem_mk_right u v)⟩

lemma adj_psi {u v : V} (h : G.Adj u v) (hu : OnEdge G u) (hv : OnEdge G v) :
    H.Adj (φ.psi u hu) (φ.psi v hv) := by
  have := (φ.toEquiv ⟨s(u, v), h⟩).2
  rwa [φ.apply_eq h hu hv, SimpleGraph.mem_edgeSet] at this

/-- **Edge reconstruction.** An edge bijection preserving meeting and triangles is induced by a
bijection of the non-isolated vertices. -/
theorem exists_vertexEquiv :
    ∃ ψ : {v // OnEdge G v} ≃ {w // OnEdge H w}, ∀ (u v : V) (h : G.Adj u v),
      (φ.toEquiv ⟨s(u, v), h⟩ : Sym2 W) =
        s((ψ ⟨u, ⟨⟨s(u, v), h⟩, Sym2.mem_mk_left u v⟩⟩ : W),
          ψ ⟨v, ⟨⟨s(u, v), h⟩, Sym2.mem_mk_right u v⟩⟩) :=
  ⟨φ.vertexEquiv, fun _ _ h ↦ φ.apply_eq h _ _⟩

include φ in
open Classical in
/-- For finite graphs with the same number of vertices, an edge bijection preserving meeting and
triangles yields a graph isomorphism. -/
theorem nonempty_iso [Fintype V] [Fintype W] (hcard : Fintype.card V = Fintype.card W) :
    Nonempty (G ≃g H) := by
  have hc : Fintype.card {v // ¬ OnEdge G v} = Fintype.card {w // ¬ OnEdge H w} := by
    rw [Fintype.card_subtype_compl, Fintype.card_subtype_compl, hcard,
      Fintype.card_congr φ.vertexEquiv]
  let f := Fintype.equivOfCardEq hc
  let e : V ≃ W := (Equiv.sumCompl (OnEdge G)).symm.trans
    ((Equiv.sumCongr φ.vertexEquiv f).trans (Equiv.sumCompl (OnEdge H)))
  have he_pos : ∀ v (hv : OnEdge G v), e v = φ.psi v hv := by
    intro v hv
    simp [e, Equiv.sumCompl_symm_apply_of_pos hv]
  have he_neg : ∀ v, ¬ OnEdge G v → ¬ OnEdge H (e v) := by
    intro v hv
    simp only [e, Equiv.trans_apply, Equiv.sumCompl_symm_apply_of_neg hv, Equiv.sumCongr_apply,
      Sum.map_inr, Equiv.sumCompl_apply_inr]
    exact (f ⟨v, hv⟩).2
  have hpos : ∀ v, OnEdge H (e v) → OnEdge G v := fun v h ↦ by
    by_contra hv
    exact he_neg v hv h
  refine ⟨⟨e, fun {u v} ↦ ⟨fun h ↦ ?_, fun h ↦ ?_⟩⟩⟩
  · have hu := hpos u ⟨⟨s(e u, e v), h⟩, Sym2.mem_mk_left _ _⟩
    have hv := hpos v ⟨⟨s(e u, e v), h⟩, Sym2.mem_mk_right _ _⟩
    rw [he_pos u hu, he_pos v hv] at h
    have := φ.symm.adj_psi h (φ.onEdge_psi hu) (φ.onEdge_psi hv)
    rwa [φ.symm_psi_psi hu, φ.symm_psi_psi hv] at this
  · have hu : OnEdge G u := ⟨⟨s(u, v), h⟩, Sym2.mem_mk_left u v⟩
    have hv : OnEdge G v := ⟨⟨s(u, v), h⟩, Sym2.mem_mk_right u v⟩
    rw [he_pos u hu, he_pos v hv]
    exact φ.adj_psi h hu hv

end EdgeIso

end EdgeRecon

end MatroidToric
