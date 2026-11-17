import Tengoku.AdianRabin.GroupUndecidability.Borisov.Model.ConverseCore
import Tengoku.AdianRabin.GroupUndecidability.Borisov.Assertions.InputsBridge
import Tengoku.AdianRabin.GroupUndecidability.GroupTheory.HNNLemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Base-group calculations used by the `z` compression stage

This file formalizes the part of Section 3.2 of the paper which takes place
in the semantic Borisov tower.  In the `c`-stage it defines `B = ⟨d,e,c⟩` and
`B0 = ⟨d,e,c,s₂⟩`, then proves the base exclusion `P ∉ B0` needed by
the nested normal-form calculation for the double-coset identity in the
proof of Proposition 3.8.
-/

namespace Undecidability
namespace HostZBaseIntersections

open BorisovCStage
open BorisovConverseCore
open BorisovContextNormalForm
open BorisovHNNModel
open BorisovInputsBridge
open HNNLemmas

noncomputable section

variable (datum : Thue.StandingDatum)

abbrev FreeInput : RankFiveFree datum := rankFiveFree datum

/-- The semantic `c`-stage `Gamma₂`.-/
abbrev CStage := Gamma2 datum (FreeInput datum)

/-- `B = ⟨d,e,c⟩ ≤ Gamma₂`.-/
def B : Subgroup (CStage datum) :=
  Subgroup.closure
    ({of3 datum (FreeInput datum) d3,
      of3 datum (FreeInput datum) e3,
      c datum (FreeInput datum)} : Set (CStage datum))

/-- `B₀ = ⟨d,e,c,s₂⟩ ≤ Gamma₂`.-/
def B0 : Subgroup (CStage datum) :=
  Subgroup.closure
    ({of3 datum (FreeInput datum) d3,
      of3 datum (FreeInput datum) e3,
      c datum (FreeInput datum),
      of3 datum (FreeInput datum) s2_3} : Set (CStage datum))

/-- `Delta = ⟨c,e,p⟩`, where `p = P⁻¹tP`.-/
def Delta : Subgroup (TStage datum (FreeInput datum)) :=
  KSubgroup datum (FreeInput datum)

/--
@isnad1 id=le.0h1v.s7.e1b0d8dc3e9a from=translated src=- shape=cfdabf11 vocab=7e036450
-/
theorem CE_le_B :
    CE datum (FreeInput datum) ≤ B datum := by
  rw [CE, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩

/--
@isnad1 id=le.0h1v.s7.94ede79bfc8d from=translated src=- shape=cfdabf11 vocab=790745d0
-/
theorem CD_le_B :
    CD datum (FreeInput datum) ≤ B datum := by
  rw [CD, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp)⟩

/-! ## The larger base `B0 = ⟨d,e,c,s₂⟩` -/

private theorem B0_le_generatedWithStable_J3 :
    B0 datum ≤
      generatedWithStable
        (A := U datum) (B := V datum)
        (phi := cEquiv datum (FreeInput datum)) (J3 1) := by
  rw [B0, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl
  · apply Subgroup.subset_closure
    exact Or.inl ⟨d3, Subgroup.subset_closure (by simp), rfl⟩
  · apply Subgroup.subset_closure
    exact Or.inl ⟨e3, Subgroup.subset_closure (by simp), rfl⟩
  · have ht : (HNNExtension.t : CStage datum) ∈
        generatedWithStable
          (A := U datum) (B := V datum)
          (phi := cEquiv datum (FreeInput datum)) (J3 1) := by
      apply Subgroup.subset_closure
      exact Or.inr rfl
    simpa [c] using
      (generatedWithStable
        (A := U datum) (B := V datum)
        (phi := cEquiv datum (FreeInput datum)) (J3 1)).inv_mem ht
  · apply Subgroup.subset_closure
    exact Or.inl ⟨s2_3, Subgroup.subset_closure (by simp [stable3]), rfl⟩

/-- Exponent sum of the first stable generator after projecting `Gamma3`
to the free group on `s₁,s₂`.-/
def firstExponentFree : FreeGroup (Fin 2) →* Multiplicative ℤ :=
  FreeGroup.lift fun i ↦ if i = 0 then Multiplicative.ofAdd 1 else 1

def firstExponent3 : Gamma3 →* Multiplicative ℤ :=
  (firstExponentFree.comp stableProjection3)

/--
@isnad1 id=eq.0h0v.s7.5f757dc68437 from=translated src=- shape=e2e809a1 vocab=26f9b371
-/
@[simp] theorem firstExponentFree_of_zero :
    firstExponentFree (FreeGroup.of (0 : Fin 2)) =
      Multiplicative.ofAdd 1 := by
  simp [firstExponentFree]

/--
@isnad1 id=eq.0h0v.s7.dfc033036ba7 from=translated src=- shape=622a4905 vocab=9b99facc
-/
@[simp] theorem firstExponentFree_of_one :
    firstExponentFree (FreeGroup.of (1 : Fin 2)) = 1 := by
  simp [firstExponentFree]

/--
@isnad1 id=eq.0h0v.s6.a1d160659a20 from=translated src=- shape=09b15779 vocab=4854eecc
-/
@[simp] theorem firstExponent3_d : firstExponent3 d3 = 1 := by
  simp [firstExponent3, firstExponentFree]

/--
@isnad1 id=eq.0h0v.s6.4eb9e0d342c0 from=translated src=- shape=09b15779 vocab=dcb69fad
-/
@[simp] theorem firstExponent3_e : firstExponent3 e3 = 1 := by
  simp [firstExponent3, firstExponentFree]

/--
@isnad1 id=eq.0h0v.s6.7fb28c5bdb06 from=translated src=- shape=09b15779 vocab=78a164cd
-/
@[simp] theorem firstExponent3_s2 : firstExponent3 s2_3 = 1 := by
  simp [firstExponent3, firstExponentFree]

/--
@isnad1 id=eq.0h1v.s7.17eaff2a8011 from=translated src=- shape=d3903745 vocab=c2ff2272
-/
theorem firstExponent3_positive (w : List (Fin 2)) :
    Multiplicative.toAdd (firstExponent3 (positive3 w)) =
      (w.count (0 : Fin 2) : ℤ) := by
  rw [firstExponent3, MonoidHom.comp_apply, stableProjection3_positive,
    positiveFree_eq_eval]
  have eval_cons (i : Fin 2) (u : List (Fin 2)) :
      Thue.evalPositive (FreeGroup.of (0 : Fin 2)) (FreeGroup.of (1 : Fin 2))
          (i :: u) =
        (if i = 0 then FreeGroup.of 0 else FreeGroup.of 1) *
          Thue.evalPositive (FreeGroup.of 0) (FreeGroup.of 1) u := by
    simp [Thue.evalPositive]
  induction w with
  | nil => simp [Thue.evalPositive]
  | cons i w ih =>
      rw [eval_cons, map_mul]
      fin_cases i <;> simp [ih, add_comm]

private theorem J3_one_le_firstExponent3_ker :
    J3 1 ≤ MonoidHom.ker firstExponent3 := by
  rw [J3, Subgroup.closure_le]
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl
  · simp
  · simp
  · simp [stable3]

/--
@isnad1 id=not.0h1v.s6.3f4518c0c45f from=translated src=- shape=8ee52686 vocab=ab42b839
-/
theorem positive3_not_mem_J3_one : positive3 datum.P ∉ J3 1 := by
  intro hP
  have hker := J3_one_le_firstExponent3_ker hP
  have hexp := congrArg Multiplicative.toAdd hker
  rw [firstExponent3_positive] at hexp
  have hz : datum.P.count (0 : Fin 2) = 0 :=
    Int.ofNat_eq_zero.mp (by simpa using hexp)
  exact (Nat.ne_of_gt
    (BorisovG0NormalForm.count_zero_pos_of_containsBoth datum.P_support)) hz

/-- The stronger exclusion used in the proof of Proposition 3.8:
`P ∉ ⟨d,e,c,s₂⟩`.
@isnad1 id=not.0h1v.s6.ba74b9be3a87 from=translated src=- shape=078fd556 vocab=8578c013
-/
theorem positive2_not_mem_B0 :
    positive2 datum (FreeInput datum) datum.P ∉ B0 datum := by
  intro hP
  have hgenerated := B0_le_generatedWithStable_J3 datum hP
  have hrange : positive2 datum (FreeInput datum) datum.P ∈
      MonoidHom.range
        (HNNExtension.of
          (A := U datum) (B := V datum)
          (φ := cEquiv datum (FreeInput datum))) :=
    ⟨positive3 datum.P, rfl⟩
  have hinter := generatedWithStable_inf_base
    (A := U datum) (B := V datum)
    (phi := cEquiv datum (FreeInput datum)) (J3 1)
    (cEquiv_mem_J3_iff datum (FreeInput datum) 1)
  have hmap : positive2 datum (FreeInput datum) datum.P ∈
      (J3 1).map
        (HNNExtension.of
          (A := U datum) (B := V datum)
          (φ := cEquiv datum (FreeInput datum))) := by
    rw [← hinter]
    exact ⟨hgenerated, hrange⟩
  rcases hmap with ⟨x, hx, hxeq⟩
  have hxP : x = positive3 datum.P := by
    apply of3_injective datum (FreeInput datum)
    simpa [positive2, of3] using hxeq
  apply positive3_not_mem_J3_one datum
  simpa [hxP] using hx

/-! ## The nested double-coset calculation -/

/-- `C₀ = ⟨c⟩` inside `Gamma₂`.-/
def C0 : Subgroup (CStage datum) :=
  Subgroup.closure ({c datum (FreeInput datum)} : Set (CStage datum))

/--
@isnad1 id=iff.0h2v.s8.447c15d9188d from=translated src=- shape=89408553 vocab=e81e3558
-/
theorem C0_le_iff {S : Subgroup (CStage datum)} :
    C0 datum ≤ S ↔ c datum (FreeInput datum) ∈ S := by
  simp [C0, Subgroup.closure_le]

/-- `L = ⟨c,t⟩` inside the `t`-stage.-/
def CT : Subgroup (TStage datum (FreeInput datum)) :=
  generatedWith
    ((C0 datum).map (toTStage datum (FreeInput datum)))
    (tLetter datum (FreeInput datum))

/-- The embedded copy of `B₀ = ⟨d,e,c,s₂⟩` in the `t`-stage.-/
def B0InT : Subgroup (TStage datum (FreeInput datum)) :=
  (B0 datum).map (toTStage datum (FreeInput datum))

/-- The embedded copy of `⟨c⟩` in the `t`-stage.-/
def C0InT : Subgroup (TStage datum (FreeInput datum)) :=
  (C0 datum).map (toTStage datum (FreeInput datum))

/--
@isnad1 id=le.0h1v.s7.21680a7c72eb from=translated src=- shape=935d3ac8 vocab=718fe3d8
-/
theorem B_le_B0 : B datum ≤ B0 datum := by
  rw [B, Subgroup.closure_le]
  simp only [Set.insert_subset_iff, Set.singleton_subset_iff]
  exact ⟨Subgroup.subset_closure (by simp), Subgroup.subset_closure (by simp),
    Subgroup.subset_closure (by simp)⟩

/--
@isnad1 id=le.0h1v.s7.3b983b84e0a1 from=translated src=- shape=cfdabf11 vocab=03f8ebc1
-/
theorem CE_le_B0 : CE datum (FreeInput datum) ≤ B0 datum :=
  (CE_le_B datum).trans (B_le_B0 datum)

/--
@isnad1 id=le.0h1v.s7.768c57897eaf from=translated src=- shape=cfdabf11 vocab=56578d60
-/
theorem CD_le_B0 : CD datum (FreeInput datum) ≤ B0 datum :=
  (CD_le_B datum).trans (B_le_B0 datum)

/--
@isnad1 id=le.0h1v.s7.570174ef4717 from=translated src=- shape=814f2a94 vocab=c150d791
-/
theorem C0_le_CD : C0 datum ≤ CD datum (FreeInput datum) := by
  rw [C0_le_iff]
  apply Subgroup.subset_closure
  simp

/-- The double-coset identity in the proof of Proposition 3.8.
Inside the `t`-stage, `⟨c,t⟩ ∩ (Delta · B₀ · Delta) = ⟨c⟩`.
@isnad1 id=eq.0h1v.s10.797d6efe8964 from=translated src=- shape=789a273c vocab=1f4c060b
-/
theorem CT_inter_deltaDoubleCoset_B0 :
    ((CT datum : Subgroup (TStage datum (FreeInput datum))) :
        Set (TStage datum (FreeInput datum))) ∩
        deltaDoubleCoset (Delta datum) (B0InT datum) =
      (C0InT datum : Set (TStage datum (FreeInput datum))) := by
  simpa [CT, Delta, B0InT, C0InT, KSubgroup, conjugatedT,
      toTStage, tLetter]
    using conjugated_doubleCoset_intersection
      (CE datum (FreeInput datum))
      (CD datum (FreeInput datum))
      (B0 datum) (C0 datum)
      (CE_le_B0 datum) (CD_le_B0 datum) (C0_le_CD datum)
      (positive2 datum (FreeInput datum) datum.P)
      (positive2_not_mem_B0 datum)

end

end HostZBaseIntersections
end Undecidability
