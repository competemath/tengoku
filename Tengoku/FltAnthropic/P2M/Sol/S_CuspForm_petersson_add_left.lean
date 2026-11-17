import Tengoku.FltAnthropic.Definitions.Def_CuspForm_Petersson
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FundamentalDomainVolume

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CuspForm_petersson_add_left.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CuspForm_petersson_add_left

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane Filter Topology
open scoped MatrixGroups ModularForm ComplexConjugate Modular

namespace AlliAux1Pet

variable {N : ℕ} {k : ℤ}

def tr (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) : ℍ → ℂ :=
  ⇑f ∣[k] (σ⁻¹ : SL(2, ℤ))

/--
@isnad1 id=eq.0h4v.s13.1b2517679022 from=translated src=- shape=f9eb3a95 vocab=a55f365f
-/
theorem tr_eq_coe_translate (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    tr f σ = ⇑(CuspForm.translate f (σ⁻¹ : SL(2, ℤ))) := by
  rw [CuspForm.coe_translate]; rfl

/--
@isnad1 id=continuo.0h4v.s7.ae1185b4a311 from=translated src=- shape=ae879e3f vocab=2f9a0466
-/
theorem continuous_tr (f : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) :
    Continuous (tr f σ) := by
  rw [tr_eq_coe_translate]
  exact (CuspForm.translate f (σ⁻¹ : SL(2, ℤ))).holo'.continuous

/--
@isnad1 id=eq.0h6v.s10.115e77fc368c from=translated src=- shape=394a9385 vocab=108c9c32
-/
theorem petersson_tr (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (σ : SL(2, ℤ)) (τ : ℍ) :
    UpperHalfPlane.petersson k (tr f σ) (tr g σ) τ =
      UpperHalfPlane.petersson k ⇑f ⇑g ((σ⁻¹ : SL(2, ℤ)) • τ) :=
  UpperHalfPlane.petersson_slash_SL k ⇑f ⇑g σ⁻¹ τ

def summand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (τ : ℍ) : ℂ :=
  UpperHalfPlane.petersson k (tr f q.out) (tr g q.out) τ

/--
@isnad1 id=eq.0h5v.s9.658ab28be66a from=translated src=- shape=0eebad85 vocab=67fb2db6
-/
theorem integrand_eq_finsum (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : ℍ) :
    CuspForm.peterssonIntegrand f g τ = ∑ᶠ q, summand f g q τ := rfl

/--
@isnad1 id=eq.0h5v.s9.52a76bf8a596 from=translated src=- shape=8850e7dc vocab=01862d55
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
@isnad1 id=eq.0h7v.s10.4c5654aaaf48 from=translated src=- shape=21f63344 vocab=34f045ba
-/
theorem summand_add (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k)
    (q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) (τ : UpperHalfPlane) :
    summand (f₁ + f₂) g q τ = summand f₁ g q τ + summand f₂ g q τ := by
  simp only [summand, tr, FunLike.coe_add, SlashAction.add_slash, UpperHalfPlane.petersson,
    Pi.add_apply, map_add]
  ring

/--
@isnad1 id=eq.0h6v.s10.0b64699b79bc from=translated src=- shape=015defda vocab=33b1f5ed
-/
theorem integrand_add [Fintype (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)]
    (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k) (τ : UpperHalfPlane) :
    CuspForm.peterssonIntegrand (f₁ + f₂) g τ =
      CuspForm.peterssonIntegrand f₁ g τ + CuspForm.peterssonIntegrand f₂ g τ := by
  rw [integrand_eq_sum, integrand_eq_sum, integrand_eq_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun q _ => summand_add f₁ f₂ g q τ

section fin
variable [NeZero N]

scoped instance : Finite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N) :=
  Subgroup.finite_quotient_of_finiteIndex

/--
@isnad1 id=continuo.0h4v.s8.e5c63b78f98c from=translated src=- shape=0ced7056 vocab=67088e24
-/
theorem continuous_integrand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    Continuous (CuspForm.peterssonIntegrand f g) := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  have : CuspForm.peterssonIntegrand f g = fun τ => ∑ q, summand f g q τ :=
    funext (integrand_eq_sum f g)
  rw [this]
  refine continuous_finsetSum _ fun q _ => ?_
  exact UpperHalfPlane.petersson_continuous k (continuous_tr f _) (continuous_tr g _)

/--
@isnad1 id=ex.0h4v.s8.72c708d3f074 from=translated src=- shape=0a49eb34 vocab=ff8aad7e
-/
theorem integrand_bounded (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    ∃ C, ∀ τ, ‖CuspForm.peterssonIntegrand f g τ‖ ≤ C := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  obtain ⟨C, hC⟩ := CuspFormClass.petersson_bounded_left k
    (CongruenceSubgroup.Gamma0 N : Subgroup (GL (Fin 2) ℝ)) f g
  refine ⟨∑ _q : SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N, C, fun τ => ?_⟩
  rw [integrand_eq_sum]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
  unfold summand
  rw [petersson_tr]
  exact hC _

/--
@isnad1 id=integrab.0h4v.s8.e67a332d238d from=translated src=- shape=0836fcd4 vocab=efeb5c72
-/
theorem integrableOn_integrand (f g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    IntegrableOn (CuspForm.peterssonIntegrand f g) 𝒟 volume := by
  obtain ⟨C, hC⟩ := integrand_bounded f g
  refine Measure.integrableOn_of_bounded (M := C)
    FLT.FundamentalDomainVolume.volume_fd_lt_top.ne
    (continuous_integrand f g).aestronglyMeasurable ?_
  exact Eventually.of_forall hC

end fin

end AlliAux1Pet
open scoped _root_.P2MW.S_CuspForm_petersson_add_left.AlliAux1Pet
/--
@isnad1 id=eq.0h5v.s10.a4c7303ea64d from=translated src=- shape=e75303a7 vocab=ac0d93c5
-/
theorem solution {N : ℕ} {k : ℤ} [NeZero N]
    (f₁ f₂ g : CuspForm (CongruenceSubgroup.Gamma0 N) k) :
    CuspForm.petersson (f₁ + f₂) g = CuspForm.petersson f₁ g + CuspForm.petersson f₂ g := by
  haveI := Fintype.ofFinite (SL(2, ℤ) ⧸ CongruenceSubgroup.Gamma0 N)
  rw [CuspForm.petersson_def, CuspForm.petersson_def, CuspForm.petersson_def,
    ← MeasureTheory.integral_add (AlliAux1Pet.integrableOn_integrand f₁ g)
      (AlliAux1Pet.integrableOn_integrand f₂ g)]
  exact MeasureTheory.integral_congr_ae
    (Filter.Eventually.of_forall fun τ => AlliAux1Pet.integrand_add f₁ f₂ g τ)

end
open scoped _root_.P2MW.S_CuspForm_petersson_add_left.AlliAux1Pet
