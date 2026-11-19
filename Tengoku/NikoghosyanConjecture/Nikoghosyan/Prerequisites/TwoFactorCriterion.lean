/-
Copyright (c) 2026 Nikoghosyan formalization team. All rights reserved.
-/
import Tengoku.Seed.Combinatorics.SimpleGraph.Connectivity.Connected
import Tengoku.Seed.Combinatorics.SimpleGraph.Tutte
import Tengoku.Seed.Data.Set.Card
import Tengoku.NikoghosyanConjecture.Nikoghosyan.CycleAssembly
import Tengoku.NikoghosyanConjecture.Nikoghosyan.Prerequisites.TwoFactorCanonicalCount

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/canghaimeng/Nikoghosyan-conjecture@ccc8514d6801, `Nikoghosyan/Prerequisites/TwoFactorCriterion.lean`: removed 1 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-!
# Tutte representation bridge and the Δ-criterion

Mathlib `IsTutteViolator` counts odd components of
`((⊤ : H.Subgraph).deleteVerts Z).coe`. The project signed deficiency
counts odd components of `H.induce Zᶜ`. This file supplies the
original-vertex-preserving graph isomorphism, transports odd-support
cardinality, and proves the 2-factor criterion
`Δ ≥ 0` on all disjoint pairs ↔ spanning degree two ↔ original-edge
`CycleFactor`.
-/

universe u

namespace Nikoghosyan
namespace TwoFactor

open Classical
open SimpleGraph Set

set_option maxHeartbeats 800000

/-! ## Original-vertex-preserving remainder isomorphism -/

section IsoBridge

variable {α β : Type u}

/-- Restrict a graph isomorphism to induced subgraphs on corresponding
vertex sets.-/
def isoInduce {H : SimpleGraph α} {H' : SimpleGraph β} (φ : H ≃g H')
    {s : Set α} {t : Set β} (hst : ∀ x, x ∈ s ↔ φ x ∈ t) :
    H.induce s ≃g H'.induce t where
  toFun x := ⟨φ x, (hst x).mp x.property⟩
  invFun y :=
    ⟨φ.symm y, (hst (φ.symm y)).mpr (by
      simpa [Equiv.apply_symm_apply] using y.property)⟩
  left_inv x := Subtype.ext (φ.toEquiv.left_inv x)
  right_inv y := Subtype.ext (φ.toEquiv.right_inv y)
  map_rel_iff' := by
    intro a b
    simp [comap_adj, RelIso.map_rel_iff]

/-- Remainder graphs of a vertex deletion: the Mathlib deleted top
subgraph and the induced complement are isomorphic, and the
isomorphism preserves the original vertex.-/
noncomputable def deleteVertsCoeIsoInduce (H : SimpleGraph α) (Z : Set α) :
    ((⊤ : H.Subgraph).deleteVerts Z).coe ≃g H.induce Zᶜ :=
  (Subgraph.coeDeleteVertsIso (G' := (⊤ : H.Subgraph)) Z).trans <|
    isoInduce Subgraph.topIso fun x => by
      change (x : α) ∉ Z ↔ Subgraph.topIso x ∈ Zᶜ
      simp [Subgraph.topIso, mem_compl_iff]

lemma deleteVertsCoeIsoInduce_val (H : SimpleGraph α) (Z : Set α)
    (x : ((⊤ : H.Subgraph).deleteVerts Z).verts) :
    (deleteVertsCoeIsoInduce H Z x : α) = (x : α) := by
  simp [deleteVertsCoeIsoInduce, isoInduce, Subgraph.coeDeleteVertsIso,
    Subgraph.topIso]

lemma ncard_supp_iso {H : SimpleGraph α} {H' : SimpleGraph β}
    (φ : H ≃g H') (c : H.ConnectedComponent) :
    c.supp.ncard = (φ.connectedComponentEquiv c).supp.ncard :=
  ncard_congr' (ConnectedComponent.isoEquivSupp φ c)

lemma mem_oddComponents_iso {H : SimpleGraph α} {H' : SimpleGraph β}
    (φ : H ≃g H') (c : H.ConnectedComponent) :
    c ∈ H.oddComponents ↔
      φ.connectedComponentEquiv c ∈ H'.oddComponents := by
  simp [oddComponents, ncard_supp_iso φ c]

lemma ncard_oddComponents_iso [Finite α] [Finite β]
    {H : SimpleGraph α} {H' : SimpleGraph β} (φ : H ≃g H') :
    H.oddComponents.ncard = H'.oddComponents.ncard :=
  ncard_congr' (φ.connectedComponentEquiv.subtypeEquiv fun c =>
    mem_oddComponents_iso φ c)

lemma ncard_oddComponents_deleteVerts [Finite α]
    (H : SimpleGraph α) (Z : Set α) :
    ((⊤ : H.Subgraph).deleteVerts Z).coe.oddComponents.ncard =
      (H.induce Zᶜ).oddComponents.ncard := by
  haveI : Finite ((⊤ : H.Subgraph).deleteVerts Z).verts :=
    inferInstanceAs (Finite (↑((⊤ : H.Subgraph).deleteVerts Z).verts))
  haveI : Finite (Zᶜ : Set α) := inferInstance
  exact ncard_oddComponents_iso (deleteVertsCoeIsoInduce H Z)

lemma isTutteViolator_iff_signedDeficiency_pos [Finite α]
    (H : SimpleGraph α) (Z : Set α) :
    H.IsTutteViolator Z ↔ 0 < signedDeficiency H Z := by
  unfold IsTutteViolator signedDeficiency oddComponentCount
  rw [ncard_oddComponents_deleteVerts H Z]
  constructor
  · intro h
    exact sub_pos.mpr (Nat.cast_lt.mpr h)
  · intro h
    exact Nat.cast_lt.mp (sub_pos.mp h)

lemma signedDeficiency_nonpos_iff_not_violator [Finite α]
    (H : SimpleGraph α) (Z : Set α) :
    signedDeficiency H Z ≤ 0 ↔ ¬ H.IsTutteViolator Z := by
  rw [isTutteViolator_iff_signedDeficiency_pos]
  exact not_lt.symm

end IsoBridge

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-! ## Sufficiency: `Δ ≥ 0` on disjoint pairs yields a 2-factor -/

lemma delta_canonical_nonneg_of_all
    (hΔ : ∀ S T : Finset V, Disjoint S T → 0 ≤ delta G S T)
    (Z : Set (GadgetVert G)) :
    0 ≤ delta G (originalS Z) (originalT Z) :=
  hΔ _ _ (disjoint_originalS_originalT Z)

lemma isSpanningDegreeTwo_common {F : G.Subgraph}
    (hF : IsSpanningDegreeTwo F) : Nikoghosyan.IsSpanningDegreeTwo F :=
  hF

/-! ## Necessity: a spanning 2-factor forces `Δ ≥ 0` on pair cuts -/

def pairCut (S T : Finset V) : Set (GadgetVert G) :=
  {x | ∃ v ∈ S, ∃ b : Fin 2, x = .clone v b} ∪
    {x | ∃ v ∈ T, ∃ w, ∃ h : G.Adj v w, x = .port v w h}

lemma clone_mem_pairCut_iff {S T : Finset V} {v : V} {b : Fin 2} :
    (GadgetVert.clone (G := G) v b ∈ pairCut (G := G) S T) ↔ v ∈ S := by
  constructor
  · intro hx
    rcases hx with ⟨v', hv', b', heq⟩ | ⟨_, _, _, _, heq⟩
    · injection heq with hv _
      cases hv
      exact hv'
    · cases heq
  · intro hv
    exact .inl ⟨v, hv, b, rfl⟩

lemma port_mem_pairCut_iff {S T : Finset V} {v w : V} {h : G.Adj v w} :
    (GadgetVert.port (G := G) v w h ∈ pairCut (G := G) S T) ↔ v ∈ T := by
  constructor
  · intro hx
    rcases hx with ⟨_, _, _, heq⟩ | ⟨v', hv', w', h', heq⟩
    · cases heq
    · injection heq with hv _
      cases hv
      exact hv'
  · intro hv
    exact .inr ⟨v, hv, w, h, rfl⟩

lemma hasSurvivingClone_pairCut {S T : Finset V} {v : V} :
    hasSurvivingClone (pairCut (G := G) S T) v ↔ v ∉ S := by
  constructor
  · rintro ⟨b, hb⟩ hv
    exact hb ((clone_mem_pairCut_iff (G := G) (T := T)).mpr hv)
  · intro hv
    refine ⟨0, ?_⟩
    intro hmem
    exact hv ((clone_mem_pairCut_iff (G := G) (T := T)).mp hmem)

lemma hasSurvivingPort_pairCut {S T : Finset V} {v : V} :
    hasSurvivingPort (pairCut (G := G) S T) v ↔ v ∉ T ∧ ∃ w, G.Adj v w := by
  constructor
  · rintro ⟨w, h, hp⟩
    exact ⟨fun hv => hp ((port_mem_pairCut_iff (G := G) (S := S)).mpr hv),
      ⟨w, h⟩⟩
  · rintro ⟨hvT, w, hadj⟩
    exact ⟨w, hadj,
      fun hp => hvT ((port_mem_pairCut_iff (G := G) (S := S)).mp hp)⟩

lemma classS_pairCut {S T : Finset V} {v : V} :
    classS (pairCut (G := G) S T) v ↔ v ∈ S := by
  unfold classS
  rw [hasSurvivingClone_pairCut (G := G) (T := T)]
  exact not_not

lemma classT_pairCut_of_nonisolated {S T : Finset V}
    (hdis : Disjoint S T) (hn : ∀ x : V, ∃ w, G.Adj x w) {v : V} :
    classT (pairCut (G := G) S T) v ↔ v ∈ T := by
  obtain ⟨w, hw⟩ := hn v
  constructor
  · intro h
    have hP : ¬ (v ∉ T ∧ ∃ w', G.Adj v w') := by
      simpa [hasSurvivingPort_pairCut (G := G) (S := S)] using h.2
    by_contra hvT
    exact hP ⟨hvT, w, hw⟩
  · intro hvT
    refine ⟨?_, ?_⟩
    · rw [hasSurvivingClone_pairCut (G := G) (T := T)]
      intro hvS
      exact Finset.disjoint_left.1 hdis hvS hvT
    · intro hP
      exact (hasSurvivingPort_pairCut (G := G) (S := S)).1 hP |>.1 hvT

lemma classU_pairCut_of_nonisolated {S T : Finset V}
    (hn : ∀ x : V, ∃ w, G.Adj x w) {v : V} :
    classU (pairCut (G := G) S T) v ↔ v ∉ S ∧ v ∉ T := by
  obtain ⟨w, hw⟩ := hn v
  constructor
  · intro h
    exact ⟨(hasSurvivingClone_pairCut (G := G) (T := T)).mp h.1,
      ((hasSurvivingPort_pairCut (G := G) (S := S)).mp h.2).1⟩
  · intro ⟨hvS, hvT⟩
    exact ⟨(hasSurvivingClone_pairCut (G := G) (T := T)).mpr hvS,
      (hasSurvivingPort_pairCut (G := G) (S := S)).mpr ⟨hvT, w, hw⟩⟩

lemma originalS_pairCut (S T : Finset V) :
    originalS (pairCut (G := G) S T) = S := by
  refine Finset.ext fun v => ?_
  simp [mem_originalS_iff, classS_pairCut (G := G) (T := T)]

lemma originalT_pairCut (S T : Finset V)
    (hdis : Disjoint S T) (hn : ∀ x : V, ∃ w, G.Adj x w) :
    originalT (pairCut (G := G) S T) = T := by
  refine Finset.ext fun v => ?_
  simp [mem_originalT_iff,
    classT_pairCut_of_nonisolated (G := G) hdis hn]

lemma canonicalCut_pairCut (S T : Finset V)
    (hdis : Disjoint S T) (hn : ∀ x : V, ∃ w, G.Adj x w) :
    canonicalCut (pairCut (G := G) S T) = pairCut (G := G) S T := by
  rw [canonicalCut_eq_pair (G := G), originalS_pairCut (G := G),
    originalT_pairCut (G := G) S T hdis hn]
  rfl

lemma exists_adj_of_spanningDegreeTwo {F : G.Subgraph}
    (hF : IsSpanningDegreeTwo F) (v : V) : ∃ w, G.Adj v w := by
  have hpos : 0 < (F.neighborSet v).ncard := by
    rw [hF.2 v]
    exact two_pos
  obtain ⟨w, hw⟩ := (ncard_pos (Set.toFinite (F.neighborSet v))).1 hpos
  exact ⟨w, F.adj_sub hw⟩

theorem nonisolated_of_spanningDegreeTwo {F : G.Subgraph}
    (hF : IsSpanningDegreeTwo F) : ∀ v : V, ∃ w, G.Adj v w :=
  exists_adj_of_spanningDegreeTwo (G := G) hF

end TwoFactor
end Nikoghosyan
