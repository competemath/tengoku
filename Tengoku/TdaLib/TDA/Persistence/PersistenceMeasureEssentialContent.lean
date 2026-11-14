import Tengoku.TdaLib.TDA.Persistence.PersistenceMeasureEssential
import Tengoku.TdaLib.TDA.Persistence.DecoratedRectangleCells
import Tengoku.TdaLib.TDA.Persistence.IntegerContentTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Essential birth-strip content from a q-tame module

The proved essential-strip split law has a signed primitive on the real line. Mathlib's
interval content of that primitive transports along the minus cuts to the actual
decorated birth cells. Its values are the original nonnegative essential quotient counts,
so conversion to natural numbers retains full finite additivity.
-/

universe u w

namespace TDA.Persistence.RectangleMeasure

open Set MeasureTheory
open scoped Classical

variable {k : Type u} [Field k] (M : PModule.{u,0,w} k ℝ)

/-- A signed primitive for essential strip counts, with reference grade zero.-/
noncomputable def essentialSignedPrimitive (t : ℝ) : ℤ :=
  if h : 0 ≤ t then (essentialMeasureValue M h : ℤ)
  else -(essentialMeasureValue M (le_of_not_ge h) : ℤ)

/-- The signed primitive difference is the actual essential birth-strip count.
@isnad1 id=eq.2h4v.s5.a74168b123d0 from=translated src=- shape=05ab537c vocab=1604fca5
-/
theorem essentialSignedPrimitive_sub (hM : M.QTame) {a b : ℝ} (hab : a ≤ b) :
    essentialSignedPrimitive M b - essentialSignedPrimitive M a =
      (essentialMeasureValue M hab : ℤ) := by
  by_cases ha : 0 ≤ a
  · have hb : 0 ≤ b := ha.trans hab
    have h := PModule.QTame.essentialMeasureValue_split_birth M hM ha hab
    simp only [essentialSignedPrimitive, dite_eq_left ha, dite_eq_left hb]
    omega
  · by_cases hb : 0 ≤ b
    · have ha0 : a ≤ 0 := le_of_not_ge ha
      have h := PModule.QTame.essentialMeasureValue_split_birth M hM ha0 hb
      simp only [essentialSignedPrimitive, dite_eq_right ha, dite_eq_left hb]
      omega
    · have hb0 : b ≤ 0 := le_of_not_ge hb
      have h := PModule.QTame.essentialMeasureValue_split_birth M hM hab hb0
      simp only [essentialSignedPrimitive, dite_eq_right ha, dite_eq_right hb]
      omega

/-- Minus-cut preimages retain the half-open interval convention of an essential birth cell.
@isnad1 id=eq.0h2v.s4.2a2a6115e1db from=translated src=- shape=6a4550fe vocab=ca91929f
-/
theorem preimage_cutCell_minusCut (a b : ℝ) :
    minusCut ⁻¹' cutCell a b = Ioc a b := by
  ext t
  simp [cutCell, minusCut]

private theorem preimage_mem_intervals {U : Set (Cut ℝ)} (hU : U ∈ cutCells) :
    minusCut ⁻¹' U ∈ {s : Set ℝ | ∃ a b, a ≤ b ∧ s = Ioc a b} := by
  obtain ⟨a, b, hab, rfl⟩ := hU
  exact ⟨a, b, hab, preimage_cutCell_minusCut a b⟩

/-- The signed essential content is obtained from an actual interval content by preimages.-/
noncomputable def essentialSignedContent : AddContent ℤ (cutCells (α := ℝ)) :=
  preimageContent (AddContent.onIoc (essentialSignedPrimitive M)) minusCut
    (fun _ hU => preimage_mem_intervals hU)

/-- Signed cut-cell contents equal the actual module's essential quotient counts.
@isnad1 id=eq.2h4v.s6.fc0ea42e2fbf from=translated src=- shape=fec9e08a vocab=1b84ba50
-/
theorem essentialSignedContent_apply (hM : M.QTame) {a b : ℝ} (hab : a ≤ b) :
    essentialSignedContent M (cutCell a b) = (essentialMeasureValue M hab : ℤ) := by
  change AddContent.onIoc (essentialSignedPrimitive M) (minusCut ⁻¹' cutCell a b) = _
  rw [preimage_cutCell_minusCut, AddContent.onIoc_apply hab, essentialSignedPrimitive_sub M hM hab]

/-- Actual essential-strip values are nonnegative on every decorated birth cell.
@isnad1 id=le.2h3v.s6.0677bb1a05ed from=translated src=- shape=81ac8389 vocab=15d35b70
-/
theorem essentialSignedContent_nonneg (hM : M.QTame) (U : Set (Cut ℝ)) (hU : U ∈ cutCells) :
    0 ≤ essentialSignedContent M U := by
  obtain ⟨a, b, hab, rfl⟩ := hU
  rw [essentialSignedContent_apply M hM hab]
  exact Int.natCast_nonneg _

/-- The actual natural-valued essential birth-strip additive content.-/
noncomputable def essentialCutContent (hM : M.QTame) : AddContent ℕ (cutCells (α := ℝ)) :=
  naturalContentOfNonnegative (essentialSignedContent M) (essentialSignedContent_nonneg M hM)

/-- Every decorated essential birth cell has its original module essential-strip value.
@isnad1 id=eq.2h4v.s6.98be573a10ac from=translated src=- shape=5e66d45a vocab=7245c9f6
-/
theorem essentialCutContent_apply (hM : M.QTame) {a b : ℝ} (hab : a ≤ b) :
    essentialCutContent M hM (cutCell a b) = essentialMeasureValue M hab := by
  change (essentialSignedContent M (cutCell a b)).toNat = _
  rw [essentialSignedContent_apply M hM hab]
  exact Int.toNat_natCast _

end TDA.Persistence.RectangleMeasure
