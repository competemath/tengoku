import Tengoku.FltAnthropic.Definitions.Def_CuspForm_Petersson
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FundamentalDomainVolume

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_petersson_self_re_nonneg.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_petersson_self_re_nonneg

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm ComplexConjugate Modular

namespace AlliAux1Pet

variable {N : ℕ} {k : ℤ}

def tr (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) : ℍ → ℂ :=
  ⇑f ∣[k] (σ⁻¹ : SL(2, ℤ))

def summand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (τ : ℍ) : ℂ :=
  UpperHalfPlane.petersson k (tr f q.out) (tr g q.out) τ

theorem integrand_eq_finsum (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f g τ = ∑ᶠ q, summand f g q τ := rfl

theorem integrand_eq_sum [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f g τ = ∑ q, summand f g q τ := by
  rw [integrand_eq_finsum, finsum_eq_sum_of_fintype]

def selfDensity [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) : ℝ :=
  ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ‖tr f q.out τ‖ ^ 2 * τ.im ^ k

theorem petersson_self_pt (h : ℍ → ℂ) (τ : ℍ) :
    UpperHalfPlane.petersson k h h τ = ((‖h τ‖ ^ 2 * τ.im ^ k : ℝ) : ℂ) := by
  unfold UpperHalfPlane.petersson
  rw [Complex.conj_mul']
  push_cast
  ring

theorem integrand_self_eq [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f f τ = (selfDensity f τ : ℂ) := by
  rw [integrand_eq_sum, selfDensity, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  exact petersson_self_pt _ _

theorem selfDensity_nonneg [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) : 0 ≤ selfDensity f τ :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (sq_nonneg _) (zpow_nonneg τ.im_pos.le _)

def twoI : ℍ := ⟨2 * Complex.I, by simp⟩

theorem petersson_self_eq_integral [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson f f = ((∫ τ in 𝒟, selfDensity f τ : ℝ) : ℂ) := by
  rw [CuspForm.petersson_def, ← integral_complex_ofReal]
  exact integral_congr_ae (Eventually.of_forall fun τ => integrand_self_eq f τ)

section fin
variable [NeZero N]

scoped instance : Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
  Subgroup.finite_quotient_of_finiteIndex

theorem petersson_self_re_nonneg' (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    0 ≤ (CuspForm.petersson f f).re := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  rw [petersson_self_eq_integral, Complex.ofReal_re]
  exact setIntegral_nonneg ModularGroup.isClosed_fd.measurableSet fun τ _ => selfDensity_nonneg f τ

end fin

end AlliAux1Pet
open scoped _root_.P2MW.S_CuspForm_petersson_self_re_nonneg.AlliAux1Pet
theorem solution {N : ℕ} {k : ℤ} [NeZero N]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    0 ≤ (CuspForm.petersson f f).re :=
  AlliAux1Pet.petersson_self_re_nonneg' f

end
open scoped _root_.P2MW.S_CuspForm_petersson_self_re_nonneg.AlliAux1Pet
