import Tengoku.FltAnthropic.Definitions.Def_CuspForm_Petersson
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FundamentalDomainVolume

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_petersson_conj_symm.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_petersson_conj_symm

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
@isnad1 id=eq.0h5v.s9.bd1150f52612 from=translated src=- shape=0eebad85 vocab=bf12f60b
-/
theorem integrand_eq_finsum (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f g τ = ∑ᶠ q, summand f g q τ := rfl

/--
@isnad1 id=eq.0h5v.s9.494fbf6b3c03 from=translated src=- shape=8850e7dc vocab=493f0076
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
@isnad1 id=eq.0h6v.s8.5b68109856a1 from=translated src=- shape=a9ed8c42 vocab=ac383525
-/
theorem summand_conj (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    starRingEnd ℂ (summand g f q τ) = summand f g q τ := by
  simp only [summand, UpperHalfPlane.petersson, map_mul, starRingEnd_self_apply, map_zpow₀,
    Complex.conj_ofReal]
  ring

/--
@isnad1 id=eq.0h5v.s8.5c532976e40b from=translated src=- shape=3ff7ddb5 vocab=e66352a8
-/
theorem integrand_conj [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    starRingEnd ℂ (CuspForm.peterssonIntegrand g f τ) = CuspForm.peterssonIntegrand f g τ := by
  rw [integrand_eq_sum, integrand_eq_sum, map_sum]
  exact Finset.sum_congr rfl fun q _ => summand_conj f g q τ

section fin
variable [NeZero N]

scoped instance : Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
  Subgroup.finite_quotient_of_finiteIndex

end fin

end AlliAux1Pet
open scoped _root_.P2MW.S_CuspForm_petersson_conj_symm.AlliAux1Pet
/--
@isnad1 id=eq.0h4v.s8.b8d1060ddeda from=translated src=- shape=03a78823 vocab=6d8b8778
-/
theorem solution {N : ℕ} {k : ℤ} [NeZero N]
    (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    starRingEnd ℂ (CuspForm.petersson g f) = CuspForm.petersson f g := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  rw [CuspForm.petersson_def, CuspForm.petersson_def, ← integral_conj]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun τ => AlliAux1Pet.integrand_conj f g τ)

end
open scoped _root_.P2MW.S_CuspForm_petersson_conj_symm.AlliAux1Pet
