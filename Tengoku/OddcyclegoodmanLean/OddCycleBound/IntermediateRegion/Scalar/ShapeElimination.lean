import Tengoku.OddcyclegoodmanLean.OddCycleBound.IntermediateRegion.Scalar.Envelope

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set

noncomputable section

namespace OddCycleBound.IntermediateRegion.Scalar

noncomputable def shapeThreshold
    (alpha q L z K : Real) : Real :=
  ((alpha - q) * z + (alpha - L) * K) / (2 * Real.sqrt z)

/--
@isnad1 id=le.6h5v.s7.770180ddde30 from=translated src=- shape=3cdd471c vocab=00556b22
-/
theorem shapeThreshold_lower
    {alpha q L z K : Real}
    (halpha : 0 < alpha)
    (hd : 0 <= alpha - q) (hf : 0 <= alpha - L)
    (hK : 0 <= K) (hz : 2 * alpha <= z) (hz1 : z <= 1) :
    (alpha - q) * Real.sqrt (2 * alpha) / 2 +
        (alpha - L) * K / 2 <=
      shapeThreshold alpha q L z K := by
  let d := alpha - q
  let f := alpha - L
  let r := Real.sqrt z
  let s := Real.sqrt (2 * alpha)
  have hzpos : 0 < z := by nlinarith
  have hrpos : 0 < r := by
    dsimp [r]
    exact Real.sqrt_pos.2 hzpos
  have hrsq : r ^ 2 = z := by
    dsimp [r]
    exact Real.sq_sqrt (le_of_lt hzpos)
  have hsle : s <= r := by
    dsimp [s, r]
    exact Real.sqrt_le_sqrt hz
  have hr0 : 0 <= r := le_of_lt hrpos
  have hr1 : r <= 1 := by
    nlinarith [sq_nonneg (r - 1)]
  have hdpart : d * s / 2 <= d * r / 2 := by
    exact div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hsle (by simpa [d] using hd)) (by norm_num)
  have hfK : 0 <= f * K :=
    mul_nonneg (by simpa [f] using hf) hK
  have hfpart : f * K / 2 <= f * K / (2 * r) := by
    apply (le_div_iff₀ (by positivity : 0 < 2 * r)).2
    have hmul : f * K * r <= f * K := by
      nlinarith [mul_nonneg hfK (sub_nonneg.mpr hr1)]
    nlinarith
  calc
    (alpha - q) * Real.sqrt (2 * alpha) / 2 +
          (alpha - L) * K / 2 = d * s / 2 + f * K / 2 := rfl
    _ <= d * r / 2 + f * K / (2 * r) := add_le_add hdpart hfpart
    _ = shapeThreshold alpha q L z K := by
      change d * r / 2 + f * K / (2 * r) =
        (d * z + f * K) / (2 * r)
      field_simp [ne_of_gt hrpos]
      nlinarith [hrsq]

end OddCycleBound.IntermediateRegion.Scalar
