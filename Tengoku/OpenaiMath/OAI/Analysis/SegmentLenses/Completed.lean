import Tengoku.OpenaiMath.OAI.Analysis.SegmentLenses.TailBudget

namespace OAI

/-!
# Completed midpoint bounds and coordinate density
-/

noncomputable section

open scoped BigOperators
open Finset

namespace SegmentLenses

instance infiniteLocallyFiniteBot : LocallyFiniteOrderBot InfiniteVertex := by
  classical
  exact LocallyFiniteOrderBot.ofIic InfiniteVertex (fun b => b.inits.toFinset)
    (fun a x => by simp [List.mem_inits, LE.le])

instance forestLocallyFiniteBot : LocallyFiniteOrderBot ForestVertex := by
  classical
  have hf : ∀ b : ForestVertex, {v : ForestVertex | v ≤ b}.Finite := by
    intro b
    apply Set.Finite.of_injOn (f := fun v : ForestVertex => v.val.2)
      (t := {w : List ℕ | w.IsPrefix b.val.2})
    · intro v hv
      exact hv.2
    · intro v hv w hw he
      apply Subtype.ext
      exact Prod.ext (hv.1.trans hw.1.symm) he
    · exact b.val.2.inits.finite_toSet.subset (by
        intro w hw
        exact (List.mem_inits w b.val.2).mpr hw)
  exact LocallyFiniteOrderBot.ofIic ForestVertex (fun b => (hf b).toFinset)
    (fun a x => by simp)

section FiniteAncestry
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrderBot V]

def ancestralHull (S : Finset V) : Finset V := S.biUnion Finset.Iic

theorem subset_ancestralHull (S : Finset V) : S ⊆ ancestralHull S := by
  intro v hv
  exact Finset.mem_biUnion.mpr ⟨v, hv, Finset.mem_Iic.mpr le_rfl⟩

theorem ancestralHull_ancestral (S : Finset V) : Ancestral (· ≤ ·) (ancestralHull S) := by
  intro v w hv hwv
  obtain ⟨b, hb, hvb⟩ := Finset.mem_biUnion.mp hv
  exact Finset.mem_biUnion.mpr ⟨b, hb, Finset.mem_Iic.mpr (hwv.trans (Finset.mem_Iic.mp hvb))⟩

end FiniteAncestry

section LocalizingTests
variable {V : Type*} [DecidableEq V] [SegmentSystem V]

end LocalizingTests

section CompletedMain
variable {V : Type*} [DecidableEq V] [PartialOrder V] [LocallyFiniteOrder V]
  [LocallyFiniteOrderBot V] [TreeOrder V] [SegmentSystem V] [IntervalSegments V]

end CompletedMain

section CoordinateNorms
variable {V : Type*} [decidableEqV : DecidableEq V] [SegmentSystem V]

theorem norm_test_unit (v : V) : ‖(Test.ofFinsupp (Finsupp.single v 1) : Test V)‖ = 1 := by
  have _ := decidableEqV
  apply le_antisymm
  · change segmentSeminorm V (Finsupp.single v 1) ≤ 1
    rw [segmentSeminorm_apply]
    apply ciSup_le
    intro F
    change ‖F.test (Finsupp.single v 1)‖ ≤ 1
    simpa [SegmentFamily.test, Finsupp.linearCombination_single] using F.norm_column_le v
  · change 1 ≤ segmentSeminorm V (Finsupp.single v 1)
    have h := abs_coord_le (Finsupp.single v (1 : ℝ)) v
    simpa using h

@[simp] theorem norm_unitVector (v : V) : ‖unitVector v‖ = 1 := by
  rw [unitVector, UniformSpace.Completion.norm_coe, norm_test_unit]

@[simp] theorem norm_coordinate (v : V) : ‖coordinate v‖ = 1 := by
  apply le_antisymm
  · apply dual_norm_le _ (by norm_num)
    intro u
    rw [coordinate_apply_test, one_mul]
    exact abs_coord_le u.coeff v
  · have h := (coordinate v).le_opNorm (unitVector v)
    simpa [coordinate_unitVector] using h

theorem coordinate_mem_span (v : V) :
    coordinate v ∈ Submodule.span ℝ (Set.range (coordinate (V := V))) := by
  have _ := decidableEqV
  exact
    Submodule.subset_span ⟨v, rfl⟩

theorem coordinate_mem (v : V) : coordinate v ∈ coordinateSpan V :=
  (Submodule.le_topologicalClosure _) (coordinate_mem_span v)

theorem head_mem_span (H : Finset V) (x : FullDual V) :
    head H x ∈ Submodule.span ℝ (Set.range (coordinate (V := V))) := by
  apply Submodule.sum_mem
  intro v hv
  exact Submodule.smul_mem _ _ (coordinate_mem_span v)

theorem head_mem (H : Finset V) (x : FullDual V) : head H x ∈ coordinateSpan V :=
  (Submodule.le_topologicalClosure _) (head_mem_span H x)

def predualCoordinate (v : V) : CoordinatePredual V := ⟨coordinate v, coordinate_mem v⟩

@[simp] theorem norm_predualCoordinate (v : V) : ‖predualCoordinate v‖ = 1 := norm_coordinate v

end CoordinateNorms

section CoordinateDensity
variable {V : Type*} [DecidableEq V] [PartialOrder V] [locallyFiniteOrderV : LocallyFiniteOrder V]
  [locallyFiniteOrderBotV : LocallyFiniteOrderBot V] [treeOrderV : TreeOrder V] [SegmentSystem V] [intervalSegmentsV : IntervalSegments V]

def predualHead {H : Finset V} (hH : Ancestral (· ≤ ·) H) :
    CoordinatePredual V →L[ℝ] CoordinatePredual V := by
  let f : CoordinatePredual V →ₗ[ℝ] CoordinatePredual V :=
    LinearMap.codRestrict (coordinateSpan V)
      ((headLinear H).comp (coordinateSpan V).subtype)
      (fun x : CoordinatePredual V => head_mem H x.val)
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := CoordinatePredual V)
    (F := CoordinatePredual V) f 1 (fun x => by
    change ‖head H x.val‖ ≤ 1 * ‖x.val‖
    simpa only [one_mul] using norm_head_le hH x.val)

def predualTail {H : Finset V} (hH : Ancestral (· ≤ ·) H) :
    CoordinatePredual V →L[ℝ] CoordinatePredual V := by
  let f : CoordinatePredual V →ₗ[ℝ] CoordinatePredual V :=
    LinearMap.codRestrict (coordinateSpan V)
      ((tailLinear H).comp (coordinateSpan V).subtype)
      (fun x : CoordinatePredual V => (coordinateSpan V).sub_mem x.property (head_mem H x.val))
  exact LinearMap.mkContinuous (𝕜 := ℝ) (𝕜₂ := ℝ) (E := CoordinatePredual V)
    (F := CoordinatePredual V) f 1 (fun x => by
    change ‖tail H x.val‖ ≤ 1 * ‖x.val‖
    simpa only [one_mul] using norm_tail_le hH x.val)

@[simp] theorem predualHead_coe {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : CoordinatePredual V) :
    (predualHead hH x).val = head H x.val := by
  have _ := locallyFiniteOrderBotV
  exact rfl

@[simp] theorem predualTail_coe {H : Finset V} (hH : Ancestral (· ≤ ·) H) (x : CoordinatePredual V) :
    (predualTail hH x).val = tail H x.val := by
  have _ := locallyFiniteOrderBotV
  exact rfl

end CoordinateDensity

end SegmentLenses

end

end OAI
