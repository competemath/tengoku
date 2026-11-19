/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin
-/
module

public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.BalancedPairs
public import Tengoku.Nkbesicovitch.NKBesicovitch.Projection.CornerCoordinates

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Corner mass from two balanced companion families

Choose the first and last companions independently over the middle line.
Their exact fiber masses multiply, giving the corner mass used in pruning.
-/

@[expose] public section

open MeasureTheory Set
open scoped ENNReal

namespace NKBesicovitch.Projection

variable {m : ℕ}

/-- Corners whose center belongs to `G₀` and whose outer lines belong to `A` and `B`.-/
def companionCorners (a b : ℝ) (G₀ A B : Set (Line m)) : Set (CornerCoordinates m) :=
  {p | p.1 ∈ G₀ ∧ cornerFirst a p ∈ A ∧ cornerLast b p ∈ B}

/--
@isnad1 id=measurab.3h6v.s8.5338ecc89ac7 from=translated src=- shape=3d468644 vocab=fe99b083
-/
theorem measurableSet_companionCorners (a b : ℝ) {G₀ A B : Set (Line m)}
    (hG₀ : MeasurableSet G₀) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    MeasurableSet (companionCorners a b G₀ A B) :=
  (hG₀.preimage measurable_fst).inter
    ((hA.preimage (by unfold cornerFirst lineAt atHeight; fun_prop)).inter
      (hB.preimage (by unfold cornerLast lineAt atHeight; fun_prop)))

/--
@isnad1 id=le.3h7v.s6.251cb0b4cf2b from=translated src=- shape=e116d524 vocab=b9fac48b
-/
theorem companionCorners_subset_cornerFamily (a b : ℝ) {G₀ A B G : Set (Line m)}
    (hG₀ : G₀ ⊆ G) (hA : A ⊆ G) (hB : B ⊆ G) :
    companionCorners a b G₀ A B ⊆ cornerFamily a b G :=
  fun _ hp ↦ ⟨hA hp.2.1, hG₀ hp.1, hB hp.2.2⟩

/--
@isnad1 id=mem.1h7v.s5.d446f11efc63 from=translated src=- shape=ac980062 vocab=b7407283
-/
theorem cornerParent_mem_companionPairs {a b : ℝ} {G₀ A B : Set (Line m)}
    {p : CornerCoordinates m} (hp : p ∈ companionCorners a b G₀ A B) :
    cornerParent a p ∈ companionPairs a G₀ A :=
  ⟨by simpa only [first_cornerParent] using hp.1, hp.2.1⟩

/--
@isnad1 id=mem.1h7v.s5.7b2ec9ac5fbd from=translated src=- shape=2ccc7ad8 vocab=dca1a5d1
-/
theorem cornerInner_mem_companionPairs {a b : ℝ} {G₀ A B : Set (Line m)}
    {p : CornerCoordinates m} (hp : p ∈ companionCorners a b G₀ A B) :
    cornerInner b p ∈ companionPairs b G₀ B :=
  ⟨by simpa only [first_cornerInner] using hp.1, hp.2.2⟩

/--
@isnad1 id=eq.3h6v.s10.d945a9497823 from=translated src=- shape=67f7f2d2 vocab=5edbb6bc
-/
theorem volume_companionCorners (a b : ℝ) {G₀ A B : Set (Line m)}
    (hG₀ : MeasurableSet G₀) (hA : MeasurableSet A) (hB : MeasurableSet B) :
    volume (companionCorners a b G₀ A B) =
      ∫⁻ g in G₀, sliceMultiplicity a A (atHeight a g) *
        sliceMultiplicity b B (atHeight b g) := by
  rw [← lintegral_indicator hG₀, Measure.volume_eq_prod,
    Measure.prod_apply (measurableSet_companionCorners a b hG₀ hA hB)]
  apply lintegral_congr
  intro g
  by_cases hg : g ∈ G₀
  · rw [Set.indicator_of_mem hg]
    have he : Prod.mk g ⁻¹' companionCorners a b G₀ A B =
        (lineAt a (atHeight a g) ⁻¹' A) ×ˢ (lineAt b (atHeight b g) ⁻¹' B) := by
      ext s
      simp [companionCorners, cornerFirst, cornerLast, hg]
    rw [he, Measure.volume_eq_prod, Measure.prod_prod]
    rfl
  · rw [Set.indicator_of_notMem hg]
    have he : Prod.mk g ⁻¹' companionCorners a b G₀ A B = ∅ := by
      ext s
      simp [companionCorners, hg]
    rw [he, measure_empty]

/-- The exact product of center mass and the two prescribed companion masses.
@isnad1 id=eq.5h8v.s11.7019ae283012 from=translated src=- shape=db93bedc vocab=34846d4e
-/
theorem volume_companionCorners_of_constant_mass (a b : ℝ) {G₀ A B : Set (Line m)}
    (hG₀ : MeasurableSet G₀) (hA : MeasurableSet A) (hB : MeasurableSet B) (ηₐ ηᵦ : ℝ≥0∞)
    (hηₐ : ∀ g ∈ G₀, sliceMultiplicity a A (atHeight a g) = ηₐ)
    (hηᵦ : ∀ g ∈ G₀, sliceMultiplicity b B (atHeight b g) = ηᵦ) :
    volume (companionCorners a b G₀ A B) = volume G₀ * (ηₐ * ηᵦ) := by
  rw [volume_companionCorners a b hG₀ hA hB]
  calc
    _ = ∫⁻ _g in G₀, ηₐ * ηᵦ :=
      setLIntegral_congr_fun hG₀ (fun g hg ↦ by rw [hηₐ g hg, hηᵦ g hg])
    _ = _ := by simp [mul_comm]

end NKBesicovitch.Projection
