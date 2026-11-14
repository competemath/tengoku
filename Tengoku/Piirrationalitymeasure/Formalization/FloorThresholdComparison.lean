import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! A bounded set of integer threshold comparisons determines the floor. -/

namespace PiIrrationality

private theorem floor_le_of_threshold_imp (a b : ℤ) (x y : ℝ)
    (hxhi : x < (b : ℝ)) (hylo : (a : ℝ) - 1 ≤ y)
    (hcmp : ∀ j : ℤ, a ≤ j → j < b → (j : ℝ) ≤ x → (j : ℝ) ≤ y) :
    ⌊x⌋ ≤ ⌊y⌋ := by
  by_contra h
  have hyfloor : a - 1 ≤ ⌊y⌋ := Int.le_floor.mpr (by exact_mod_cast hylo)
  have hxfloor : ⌊x⌋ < b := Int.floor_lt.mpr hxhi
  have hja : a ≤ ⌊y⌋ + 1 := by omega
  have hjb : ⌊y⌋ + 1 < b := by omega
  have hjx : ((⌊y⌋ + 1 : ℤ) : ℝ) ≤ x :=
    Int.le_floor.mp (by omega : ⌊y⌋ + 1 ≤ ⌊x⌋)
  have hjy := hcmp (⌊y⌋ + 1) hja hjb hjx
  have hjy' := Int.le_floor.mpr hjy
  omega

/--
@isnad1 id=eq.5h4v.s6.7e212cff648f from=translated src=- shape=588ab8cb vocab=0bc3cb90
-/
theorem floor_eq_of_threshold_comparisons (a b : ℤ) (x y : ℝ)
    (hxlo : (a : ℝ) - 1 ≤ x) (hxhi : x < (b : ℝ))
    (hylo : (a : ℝ) - 1 ≤ y) (hyhi : y < (b : ℝ))
    (hcmp : ∀ j : ℤ, a ≤ j → j < b → ((j : ℝ) ≤ x ↔ (j : ℝ) ≤ y)) :
    ⌊x⌋ = ⌊y⌋ := by
  exact le_antisymm
    (floor_le_of_threshold_imp a b x y hxhi hylo (fun j hja hjb => (hcmp j hja hjb).mp))
    (floor_le_of_threshold_imp a b y x hyhi hxlo (fun j hja hjb => (hcmp j hja hjb).mpr))

end PiIrrationality
