/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.OpenNormalSubgroups.BasisAtOne
import Tengoku.YamaguchiPapers.Nyll.ProCGroups.ProC.Quotients.DescendingClosedSubgroupQuotients

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Continuous sections of left-quotient projections

Using normalized section data ordered by intermediate closed subgroups, this file applies a chain
upper-bound argument to construct continuous sections of \(G/K \to G/H\). It concludes with a
continuous section of the quotient map by any closed subgroup of a profinite group.
-/

open Set
open scoped Topology Pointwise

namespace ProCGroups.ProC

universe u v

open InverseSystems

/--
If an intermediate closed subgroup is not contained in the base subgroup, the set-theoretic
difference contains an element.-/
theorem exists_mem_of_not_le {G : Type u} [Group G] [TopologicalSpace G] {K L : ClosedSubgroup G}
    (hnotle : ¬ (L : Subgroup G) ≤ (K : Subgroup G)) :
    ∃ x : G, x ∈ (L : Subgroup G) ∧ x ∉ (K : Subgroup G) := by
  by_contra hNo
  apply hnotle
  intro x hxL
  by_cases hxK : x ∈ (K : Set G)
  · exact hxK
  · exact False.elim (hNo ⟨x, hxL, hxK⟩)

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G]

omit [T2Space G] in
/--
For any nontrivial element of a profinite group, there is an open normal subgroup that does not
contain it.-/
theorem exists_openNormalSubgroup_not_mem
    {x : G} (hx : x ≠ 1) :
    ∃ U : OpenNormalSubgroup G, x ∉ (U : Subgroup G) := by
  let W : Set G := ({x} : Set G)ᶜ
  have hW : IsOpen W := by
    simp only [isOpen_compl_iff, finite_singleton, Finite.isClosed, W]
  have h1W : (1 : G) ∈ W := by
    simpa [W] using hx.symm
  obtain ⟨U, hUW⟩ :=
    exists_openNormalSubgroup_sub_open_nhds_of_one (G := G) hW h1W
  refine ⟨U, ?_⟩
  intro hxU
  exact hx <| by
    have hxW : x ∈ W := hUW hxU
    simp only [mem_compl_iff, mem_singleton_iff, not_true_eq_false, W] at hxW

omit [T2Space G] in
/--
A point outside a closed subgroup of a profinite group is omitted by some open subgroup
containing that closed subgroup.-/
theorem exists_openSubgroup_ge_closedSubgroup_not_mem
    (K : ClosedSubgroup G) {x : G} (hx : x ∉ (K : Set G)) :
    ∃ U : OpenSubgroup G, (K : Subgroup G) ≤ (U : Subgroup G) ∧ x ∉ (U : Set G) := by
  have hxInf :
      x ∉ sInf {N : Subgroup G | IsOpen (N : Set G) ∧ (K : Subgroup G) ≤ N} := by
    rw [← closedSubgroup_eq_sInf_open (G := G) K]
    exact hx
  rw [Subgroup.mem_sInf] at hxInf
  push Not at hxInf
  rcases hxInf with ⟨U, hU, hxU⟩
  exact ⟨⟨U, hU.1⟩, hU.2, hxU⟩

/-- The canonical quotient map \(G \to G/\bot\) is a homeomorphism for profinite groups.-/
noncomputable def quotientBotHomeomorph :
    G ≃ₜ G ⧸ (⊥ : Subgroup G) := by
  letI : IsClosed (((⊥ : Subgroup G) : Set G)) := by
    change IsClosed ({(1 : G)} : Set G)
    simp only [finite_singleton, Finite.isClosed]
  exact Continuous.homeoOfEquivCompactToT2
    (f := Equiv.ofBijective
      (QuotientGroup.mk (s := (⊥ : Subgroup G)))
      (by
        constructor
        · intro x y hxy
          have hmem : x⁻¹ * y ∈ (⊥ : Subgroup G) := QuotientGroup.eq.1 hxy
          exact inv_mul_eq_one.mp <| by simpa using hmem
        · intro q
          rcases Quotient.exists_rep q with ⟨g, rfl⟩
          exact ⟨g, rfl⟩))
    (by
      change Continuous
        (QuotientGroup.mk (s := (⊥ : Subgroup G)) : G → G ⧸ (⊥ : Subgroup G))
      exact QuotientGroup.continuous_mk)

omit [T2Space G] in
/-- The continuous equivalence is evaluated by the corresponding comparison formula.-/
@[simp 900] theorem quotientBotHomeomorph_apply (g : G) :
    quotientBotHomeomorph (G := G) g = QuotientGroup.mk (s := (⊥ : Subgroup G)) g :=
  rfl

/--
Data of a normalized continuous section of a left quotient projection \(G/L \to G/H\), ordered
so that smaller intermediate subgroups correspond to larger elements. This is the Zorn package
used for the closed-subgroup section theorem.-/
structure LeftQuotientSectionData (K H : ClosedSubgroup G) where
  /-- The intermediate closed subgroup through which the section is constructed.-/
  L : ClosedSubgroup G
  /-- The lower endpoint \(K\) is contained in the intermediate subgroup \(L\).-/
  hKL : (K : Subgroup G) ≤ (L : Subgroup G)
  /-- The intermediate subgroup \(L\) is contained in the upper endpoint \(H\).-/
  hLH : (L : Subgroup G) ≤ (H : Subgroup G)
  /-- A section from the left quotient by \(H\) to the left quotient by \(L\).-/
  σ : G ⧸ (H : Subgroup G) → G ⧸ (L : Subgroup G)
  /-- The section \(\sigma\) is continuous.-/
  continuous_σ : Continuous σ
  /-- The map \(\sigma\) is a right inverse of the quotient projection from \(G/L\) to \(G/H\).-/
  rightInv : Function.RightInverse σ
    (leftQuotientProjection (L : Subgroup G) (H : Subgroup G) hLH)
  /-- The section sends the identity coset modulo \(H\) to the identity coset modulo \(L\).-/
  one_eq :
    σ (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G)) =
      QuotientGroup.mk (s := (L : Subgroup G)) (1 : G)

namespace LeftQuotientSectionData

variable {K H : ClosedSubgroup G}

/-- The order relation is the refinement relation on the corresponding data.-/
instance instLELeftQuotientSectionData : LE (LeftQuotientSectionData (G := G) K H) where
  le a b :=
    ∃ hba : (b.L : Subgroup G) ≤ (a.L : Subgroup G),
      leftQuotientProjection (b.L : Subgroup G) (a.L : Subgroup G) hba ∘ b.σ = a.σ

/-- The preorder is induced by refinement of the corresponding data.-/
instance instPreorderLeftQuotientSectionData : Preorder (LeftQuotientSectionData (G := G) K H) where
  le_refl a := by
    refine ⟨le_rfl, ?_⟩
    funext x
    simp only [leftQuotientProjection_id, Function.comp_apply, id_eq]
  le_trans a b c hab hbc := by
    rcases hab with ⟨hba, hbaσ⟩
    rcases hbc with ⟨hcb, hcbσ⟩
    refine ⟨hcb.trans hba, ?_⟩
    funext x
    calc
      leftQuotientProjection (c.L : Subgroup G) (a.L : Subgroup G) (hcb.trans hba) (c.σ x)
                = leftQuotientProjection (b.L : Subgroup G) (a.L : Subgroup G) hba
                    (leftQuotientProjection (c.L : Subgroup G) (b.L : Subgroup G) hcb (c.σ x)) := by
                convert
                  (leftQuotientProjection_comp_apply
                    (K := (c.L : Subgroup G)) (H := (b.L : Subgroup G))
                    (L := (a.L : Subgroup G)) hcb hba (c.σ x)).symm
      _ = leftQuotientProjection (b.L : Subgroup G) (a.L : Subgroup G) hba (b.σ x) := by
            exact congrArg (leftQuotientProjection (b.L : Subgroup G) (a.L : Subgroup G) hba)
              (congrFun hcbσ x)
      _ = a.σ x := congrFun hbaσ x

/-- The maximal element of the Zorn poset, given by the identity section over H itself.-/
def top (hKH : (K : Subgroup G) ≤ (H : Subgroup G)) :
    LeftQuotientSectionData (G := G) K H where
  L := H
  hKL := hKH
  hLH := le_rfl
  σ := id
  continuous_σ := continuous_id
  rightInv := by
    intro x
    simp only [id_eq, leftQuotientProjection_id]
  one_eq := rfl

omit [T2Space G] [TotallyDisconnectedSpace G] in
/-- Any nonempty chain of partial sections admits an upper bound over the infimum subgroup.-/
theorem exists_upperBound_of_chain
    (c : Set (LeftQuotientSectionData (G := G) K H))
    (hc : IsChain (· ≤ ·) c) (hcn : c.Nonempty) :
    ∃ ub : LeftQuotientSectionData (G := G) K H, ∀ a ∈ c, a ≤ ub := by
  classical
  let I : Type u := {a : LeftQuotientSectionData (G := G) K H // a ∈ c}
  have hI_nonempty : Nonempty I := by
    rcases hcn with ⟨a, ha⟩
    exact ⟨⟨a, ha⟩⟩
  let L : I → ClosedSubgroup G := fun i => i.1.L
  have hL : ∀ {i j : I}, i ≤ j → (L j : Subgroup G) ≤ (L i : Subgroup G) := by
    intro i j hij
    rcases hij with ⟨hji, -⟩
    exact hji
  have hdir : Directed (· ≤ ·) (id : I → I) := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact ⟨i, le_rfl, le_rfl⟩
    · have hcmp := hc i.2 j.2 (by
        intro hij'
        apply hij
        exact Subtype.ext hij')
      rcases hcmp with hij' | hji'
      · exact ⟨j, hij', le_rfl⟩
      · exact ⟨i, le_rfl, hji'⟩
  obtain ⟨ηinf, hηinf_continuous, hηinf_fac, hηinf_one⟩ :=
    exists_continuous_leftQuotient_lift_of_directed (G := G) L hL hdir
      (η := fun i => i.1.σ) (hηcont := fun i => i.1.continuous_σ)
      (hηcompat := by
        intro i j hij
        rcases hij with ⟨hji, hσ⟩
        exact hσ)
      (QuotientGroup.mk (s := (H : Subgroup G)) (1 : G))
      (by
        intro i
        exact i.1.one_eq)
  let Linf : ClosedSubgroup G := closedSubgroup_sInf L
  have hKinf : (K : Subgroup G) ≤ (Linf : Subgroup G) := by
    intro x hx
    change x ∈ iInf fun i => (L i : Subgroup G)
    rw [Subgroup.mem_iInf]
    intro i
    exact i.1.hKL hx
  let i0 : I := Classical.choice hI_nonempty
  have hInfH : (Linf : Subgroup G) ≤ (H : Subgroup G) := by
    exact (closedSubgroup_sInf_le (L := L) i0).trans i0.1.hLH
  refine ⟨{ L := Linf
            hKL := hKinf
            hLH := hInfH
            σ := ηinf
            continuous_σ := hηinf_continuous
            rightInv := by
              intro y
              calc
                leftQuotientProjection (Linf : Subgroup G) (H : Subgroup G) hInfH (ηinf y)
                    = leftQuotientProjection (i0.1.L : Subgroup G) (H : Subgroup G) i0.1.hLH
                        (leftQuotientProjection (Linf : Subgroup G) (i0.1.L : Subgroup G)
                          (closedSubgroup_sInf_le (L := L) i0) (ηinf y)) := by
                            convert
                              (leftQuotientProjection_comp_apply
                                (K := (Linf : Subgroup G)) (H := (i0.1.L : Subgroup G))
                                (L := (H : Subgroup G)) (closedSubgroup_sInf_le (L := L) i0)
                                i0.1.hLH (ηinf y)).symm
                _ = leftQuotientProjection (i0.1.L : Subgroup G) (H : Subgroup G) i0.1.hLH
                      (i0.1.σ y) := by
                        exact congrArg
                          (leftQuotientProjection (i0.1.L : Subgroup G) (H : Subgroup G) i0.1.hLH)
                          (congrFun (hηinf_fac i0) y)
                _ = y := i0.1.rightInv y
            one_eq := hηinf_one }, ?_⟩
  intro a ha
  refine ⟨closedSubgroup_sInf_le (L := L) ⟨a, ha⟩, ?_⟩
  exact hηinf_fac ⟨a, ha⟩

end LeftQuotientSectionData

end ProCGroups.ProC
