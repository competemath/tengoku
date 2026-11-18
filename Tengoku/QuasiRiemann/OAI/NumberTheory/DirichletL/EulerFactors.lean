import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Deriv
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Real
import Tengoku.Seed.Analysis.Calculus.FDeriv.Mul
import Tengoku.Seed.Tactic.Positivity
import Tengoku.Seed.Tactic.Linarith

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.QuasiRiemann end Tengoku.QuasiRiemann open Tengoku.QuasiRiemann
namespace OAI

namespace SevenEighths.EulerFactors

noncomputable section

def factor (N : ℝ) (a s : ℂ) : ℂ := 1 - a * (N : ℂ) ^ (-s)

/--
@isnad1 id=lt.3h3v.s6.dd6c03278d3e from=translated src=- shape=bb326470 vocab=4315be5d
-/
theorem norm_term_lt_one {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : ‖a * (N : ℂ) ^ (-s)‖ < 1 := by
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N),
    Complex.neg_re]
  calc
    ‖a‖ * N ^ (-s.re) ≤ 1 * N ^ (-s.re) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by linarith) _)
    _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hN (neg_neg_of_pos hs)

/--
@isnad1 id=ne.3h3v.s5.7d9e7421f9ce from=translated src=- shape=8c21d11c vocab=e3655ccf
-/
theorem factor_ne_zero {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : factor N a s ≠ 0 := by
  intro h
  have heq : a * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_term_lt_one hN ha hs
  rw [heq, norm_one] at hlt
  exact (lt_irrefl _ hlt)

/--
@isnad1 id=differen.1h2v.s6.d9b52351a1fa from=translated src=- shape=bf8aac77 vocab=34ed73e4
-/
theorem differentiable_factor {N : ℝ} (hN : 0 < N) (a : ℂ) :
    Differentiable ℂ (factor N a) := by
  exact (differentiable_const (1 : ℂ)).sub ((differentiable_const a).mul
    (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))))

def deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ) (a : ι → ℂ)
    (s : ℂ) : ℂ := ∏ p ∈ S, factor (N p) (a p) s

/--
@isnad1 id=ne.3h5v.s6.f64be0eaa1db from=translated src=- shape=a2d5ebce vocab=58ce9050
-/
theorem deletedProduct_ne_zero {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedProduct S N a s ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact factor_ne_zero (hN p hp) (ha p hp) hs

/--
@isnad1 id=differen.1h4v.s6.453b76664267 from=translated src=- shape=89cfc8e7 vocab=b4dba225
-/
theorem differentiable_deletedProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedProduct S N a) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Differentiable ℂ (fun _ : ℂ => (1 : ℂ))
    exact differentiable_const _
  | @insert p S hp ih =>
    have hpN := hN p (Finset.mem_insert_self p S)
    have hSN : ∀ q ∈ S, 0 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have heq : deletedProduct (insert p S) N a =
        fun s => factor (N p) (a p) s * deletedProduct S N a s := by
      funext s
      simp only [deletedProduct, Finset.prod_insert hp]
    rw [heq]
    exact (differentiable_factor hpN (a p)).mul (ih hSN)

/--
@isnad1 id=iff.4h7v.s7.5e9f2406590e from=translated src=- shape=d280e786 vocab=fb58ab11
-/
theorem deleted_eq_zero_iff {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {L Ldeleted : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hidentity : Ldeleted s = deletedProduct S N a s * L s) :
    Ldeleted s = 0 ↔ L s = 0 := by
  rw [hidentity, mul_eq_zero]
  exact or_iff_right (deletedProduct_ne_zero S N a hN ha hs)

end

end SevenEighths.EulerFactors

end OAI
-- Tengoku: root names of this library moved to Tengoku.QuasiRiemann so they do not collide with other libraries (generated)
