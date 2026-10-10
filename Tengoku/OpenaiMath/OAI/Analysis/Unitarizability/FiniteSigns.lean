import Tengoku

namespace OAI

/-! Finite independent signs. Expectations are explicit finite sums over all sign
assignments with equal weight. -/
noncomputable section
namespace Dixmier
namespace FiniteSigns
open Finset
variable {J : Type*} [Fintype J]
local instance : DecidableEq J := Classical.decEq J

def sign (b : Bool) : ℝ := if b then 1 else -1

def value (a : J → ℝ) (σ : J → Bool) : ℝ := ∑ j, a j * sign (σ j)

theorem sign_mgf (a : J → ℝ) :
    ∑ σ : J → Bool, Real.exp (value a σ) =
      (2 : ℝ) ^ Fintype.card J * ∏ j, Real.cosh (a j) := by
  simp only [value, Real.exp_sum]
  rw [← Fintype.prod_sum (fun j (b : Bool) => Real.exp (a j * sign b))]
  have h (j : J) : (∑ b : Bool, Real.exp (a j * sign b)) = 2 * Real.cosh (a j) := by
    simp [sign, Real.cosh_eq]
    ring
  simp_rw [h]
  rw [Finset.prod_mul_distrib]
  simp

theorem value_smul (a : J → ℝ) (t : ℝ) (σ : J → Bool) :
    value (fun j => t * a j) σ = t * value a σ := by
  simp only [value, Finset.mul_sum, mul_assoc]

theorem value_neg (a : J → ℝ) (σ : J → Bool) : value (fun j => -a j) σ = -value a σ := by
  simp [value, Finset.sum_neg_distrib]

end FiniteSigns
end Dixmier

end

end OAI
