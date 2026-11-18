import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.Complex.Norm
import Tengoku.Seed.Algebra.BigOperators.GroupWithZero.Finset
import Tengoku.Seed.Tactic.FieldSimp
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

namespace SevenEighths.Probe
noncomputable section

def principalScalar {ι : Type*} (slots : Finset ι) (Z ℓ : ℝ) (S : ι → ℝ) : ℝ :=
  (-1) ^ slots.card * Z ^ (-ℓ / 6) * ∏ i ∈ slots, S i

/--
@isnad1 id=ne.2h5v.s6.db3c4eeee077 from=translated src=- shape=832eed23 vocab=58915645
-/
theorem principalScalar_ne_zero {ι : Type*} (slots : Finset ι)
    {Z ℓ : ℝ} {S : ι → ℝ} (hZ : 0 < Z)
    (hS : ∀ i ∈ slots, 0 < S i) : principalScalar slots Z ℓ S ≠ 0 := by
  unfold principalScalar
  apply mul_ne_zero
  · exact mul_ne_zero (pow_ne_zero _ (by norm_num))
      (ne_of_gt (Real.rpow_pos_of_pos hZ _))
  · exact ne_of_gt (Finset.prod_pos hS)

def normalizedProbe (I A : ℝ → ℂ) (c : ℂ) (Z : ℝ) : ℂ := I Z / (c * A Z)

/--
@isnad1 id=eq.2h5v.s6.4e7101198296 from=translated src=- shape=3bb33357 vocab=d5a87bc9
-/
theorem normalizedProbe_error (I A f : ℝ → ℂ) {c : ℂ} {Z : ℝ}
    (hc : c ≠ 0) (hA : A Z ≠ 0) :
    normalizedProbe I A c Z - f Z = (I Z - (c * A Z) * f Z) / (c * A Z) := by
  unfold normalizedProbe
  field_simp

/--
@isnad1 id=le.3h7v.s7.8981b98080a0 from=translated src=- shape=fd208c67 vocab=1a9fa699
-/
theorem norm_div_bound {I B : ℂ} {Z C D a ε : ℝ} (hZ : 0 < Z)
    (hI : ‖I‖ ≤ C * Z ^ a) (hB : ‖B⁻¹‖ ≤ D * Z ^ ε) :
    ‖I / B‖ ≤ (C * D) * Z ^ (a + ε) := by
  rw [div_eq_mul_inv, norm_mul, Real.rpow_add hZ]
  calc
    ‖I‖ * ‖B⁻¹‖ ≤ (C * Z ^ a) * (D * Z ^ ε) :=
      mul_le_mul hI hB (norm_nonneg _) ((norm_nonneg _).trans hI)
    _ = C * D * (Z ^ a * Z ^ ε) := by ring

/--
@isnad1 id=and.6h11v.s8.443c567fb2ff from=translated src=- shape=a3babbf9 vocab=7ef87863
-/
theorem common_normalization_bounds (I A f : ℝ → ℂ) {c : ℂ}
    {Z C_low C_high D a b ε : ℝ} (hZ : 0 < Z)
    (hc : c ≠ 0) (hA : A Z ≠ 0)
    (hrecip : ‖(c * A Z)⁻¹‖ ≤ D * Z ^ ε)
    (hlow : ‖I Z‖ ≤ C_low * Z ^ a)
    (hhigh : ‖I Z - (c * A Z) * f Z‖ ≤ C_high * Z ^ b) :
    ‖normalizedProbe I A c Z‖ ≤ (C_low * D) * Z ^ (a + ε) ∧
    ‖normalizedProbe I A c Z - f Z‖ ≤ (C_high * D) * Z ^ (b + ε) := by
  constructor
  · exact norm_div_bound hZ hlow hrecip
  · rw [normalizedProbe_error I A f hc hA]
    exact norm_div_bound hZ hhigh hrecip

end
end SevenEighths.Probe

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
