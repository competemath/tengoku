import Tengoku.FltAnthropic.Definitions.Def_CuspForm_Petersson
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FundamentalDomainVolume

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_petersson_smul_left.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_petersson_smul_left

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

/--
@isnad1 id=eq.0h5v.s9.24d726c0c1b3 from=translated src=- shape=0eebad85 vocab=9f25e406
-/
theorem integrand_eq_finsum (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f g τ = ∑ᶠ q, summand f g q τ := rfl

/--
@isnad1 id=eq.0h5v.s9.d10408f7c846 from=translated src=- shape=8850e7dc vocab=2d8caf12
-/
theorem integrand_eq_sum [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f g τ = ∑ q, summand f g q τ := by
  rw [integrand_eq_finsum, finsum_eq_sum_of_fintype]

def selfDensity [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) : ℝ :=
  ∑ q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, ‖tr f q.out τ‖ ^ 2 * τ.im ^ k

def twoI : ℍ := ⟨2 * Complex.I, by simp⟩

/--
@isnad1 id=eq.0h7v.s10.ab48959d9709 from=translated src=- shape=7c39cec7 vocab=8340ef5a
-/
theorem summand_smul (c : ℂ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    summand (c • f) g q τ = starRingEnd ℂ c * summand f g q τ := by
  simp only [summand, tr, FunLike.coe_smul, ModularForm.SL_smul_slash,
    UpperHalfPlane.petersson, Pi.smul_apply, smul_eq_mul, map_mul]
  ring

/--
@isnad1 id=eq.0h6v.s10.aa9ac5861628 from=translated src=- shape=805525c4 vocab=13df73b7
-/
theorem integrand_smul [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (c : ℂ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    CuspForm.peterssonIntegrand (c • f) g τ = starRingEnd ℂ c * CuspForm.peterssonIntegrand f g τ := by
  rw [integrand_eq_sum, integrand_eq_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun q _ => summand_smul c f g q τ

section fin
variable [NeZero N]

scoped instance : Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
  Subgroup.finite_quotient_of_finiteIndex

end fin

end AlliAux1Pet
open scoped _root_.P2MW.S_CuspForm_petersson_smul_left.AlliAux1Pet
/--
@isnad1 id=eq.0h5v.s9.716523ae47ef from=translated src=- shape=9e5daad1 vocab=4ba95c97
-/
theorem solution {N : ℕ} {k : ℤ} [NeZero N]
    (c : ℂ) (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (c • f) g = starRingEnd ℂ c * CuspForm.petersson f g := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  rw [CuspForm.petersson_def, CuspForm.petersson_def, ← MeasureTheory.integral_const_mul]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun τ => AlliAux1Pet.integrand_smul c f g τ)

end
open scoped _root_.P2MW.S_CuspForm_petersson_smul_left.AlliAux1Pet
