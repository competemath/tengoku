import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_BinaryFormRep
import Tengoku.FltAnthropic.Definitions.Def_Gamma0CoeffCohomology
import Tengoku.FltAnthropic.Definitions.Def_HeckeEis_EichlerIntegral

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HeckeEis_IsEichlerIntegral_slash.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HeckeEis_IsEichlerIntegral_slash

set_option autoImplicit false

noncomputable section

namespace HeckeEis
export _root_.HeckeEis (BinaryForm binarySubst binaryFormRepSL binaryFormRepSL_apply_coe linePow jFactor jFactor_eq_denom jFactor_ne_zero binaryFormRepSL_linePow IsEichlerIntegral)
open _root_.HeckeEis

open UpperHalfPlane MvPolynomial ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

namespace EichlerIntegralAux

section Expansion

variable {K : Type*} [CommRing K] {n : ℕ}

variable (n) in

def degExps : Finset (Fin 2 →₀ ℕ) :=
  (Finset.range (n + 1)).image fun k => Finsupp.single 0 k + Finsupp.single 1 (n - k)

variable (n) in
/--
@isnad1 id=iff.0h2v.s7.ab243cdaa4d5 from=translated src=- shape=9552f26d vocab=338e06f0
-/
theorem mem_degExps_iff (d : Fin 2 →₀ ℕ) : d ∈ degExps n ↔ d.degree = n := by
  rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
  simp only [degExps, Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp
    omega
  · intro h
    refine ⟨d 0, by omega, ?_⟩
    ext i
    fin_cases i <;> simp <;> omega

/--
@isnad1 id=eq.2h4v.s8.6c8f59208978 from=translated src=- shape=3ba52479 vocab=5b5c970a
-/
theorem coeff_eq_zero_of_not_mem_degExps {p : MvPolynomial (Fin 2) K} (hp : p ∈ BinaryForm K n)
    {d : Fin 2 →₀ ℕ} (hd : d ∉ degExps n) : coeff d p = 0 :=
  ((mem_homogeneousSubmodule n p).mp hp).coeff_eq_zero (by rwa [mem_degExps_iff] at hd)

theorem eq_sum_degExps {p : MvPolynomial (Fin 2) K} (hp : p ∈ BinaryForm K n) :
    p = ∑ e ∈ degExps n, monomial e (coeff e p) := by
  refine MvPolynomial.ext _ _ fun d => ?_
  rw [coeff_sum]
  simp only [coeff_monomial]
  by_cases hd : d ∈ degExps n
  · rw [Finset.sum_eq_single d (fun e _ hne => ite_eq_right hne) (fun h => (h hd).elim), ite_eq_left rfl]
  · rw [Finset.sum_eq_zero (fun e he => ite_eq_right (fun h : e = d => hd (h ▸ he))),
      coeff_eq_zero_of_not_mem_degExps hp hd]

/--
@isnad1 id=eq.0h5v.s12.4377d2b421ab from=translated src=- shape=1775eaa8 vocab=520c5519
-/
theorem coeff_binaryFormRepSL_eq_sum (g : SL(2, ℤ)) (v : ↥(BinaryForm K n)) (d : Fin 2 →₀ ℕ) :
    coeff d ((binaryFormRepSL K n g v : ↥(BinaryForm K n)) : MvPolynomial (Fin 2) K)
      = ∑ e ∈ degExps n, coeff e (v : MvPolynomial (Fin 2) K)
          * coeff d (binarySubst K (g : Matrix (Fin 2) (Fin 2) ℤ) (monomial e 1)) := by
  rw [binaryFormRepSL_apply_coe]
  conv_lhs => rw [eq_sum_degExps v.2, map_sum, coeff_sum]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [show monomial e (coeff e (v : MvPolynomial (Fin 2) K)) = coeff e (v : MvPolynomial (Fin 2) K) • monomial e (1 : K) by
      rw [smul_monomial, smul_eq_mul, mul_one],
    map_smul, coeff_smul, smul_eq_mul]

end Expansion

section Calculus

/--
@isnad1 id=hasderiv.0h2v.s9.c3774eefdf2c from=translated src=- shape=c1929f93 vocab=7e3a74bb
-/
theorem hasDerivAt_smul_ofComplex (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ))
      (denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  set G : GL (Fin 2) ℝ := Matrix.SpecialLinearGroup.mapGL ℝ γ with hG
  have hdet : (G : Matrix (Fin 2) (Fin 2) ℝ).det = 1 := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply, hG, Matrix.SpecialLinearGroup.det_mapGL,
      Units.val_one]
  have hpos : (0:ℝ) < (G : Matrix (Fin 2) (Fin 2) ℝ).det := by rw [hdet]; norm_num
  have h1 := (UpperHalfPlane.hasStrictDerivAt_smul hpos τ).hasDerivAt
  have h2 : (fun z : ℂ => ((G • ofComplex z : ℍ) : ℂ))
      = fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ) := by
    funext z
    rw [MulAction.compHom_smul_def]
  rw [h2] at h1
  convert h1 using 1 <;> try rfl
  rw [hdet]
  push_cast
  rw [zpow_neg, one_div]
  norm_cast

/--
@isnad1 id=hasderiv.1h4v.s9.fdd325c12de0 from=translated src=- shape=ff059be4 vocab=0fcab145
-/
theorem hasDerivAt_comp_smul {G : ℍ → ℂ} {g : ℍ → ℂ}
    (hG : ∀ τ : ℍ, HasDerivAt (G ∘ ofComplex) (g τ) ↑τ) (γ : SL(2, ℤ)) (τ : ℍ) :
    HasDerivAt (fun z : ℂ => G (γ • ofComplex z))
      (g (γ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ γ) ↑τ ^ (-2 : ℤ)) ↑τ := by
  have hfun : (fun z : ℂ => G (γ • ofComplex z))
      = (G ∘ ofComplex) ∘ (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) := by
    funext z
    simp only [Function.comp_apply, ofComplex_apply]
  have houter : HasDerivAt (G ∘ ofComplex) (g (γ • τ))
      ((fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) ↑τ) := by
    simpa only [ofComplex_apply] using hG (γ • τ)
  have hcomp := houter.comp (↑τ : ℂ) (hasDerivAt_smul_ofComplex γ τ)
  rwa [← hfun] at hcomp

end Calculus

section RepDeriv

variable {n : ℕ}

/--
@isnad1 id=hasderiv.1h6v.s13.c7afa1e49479 from=translated src=- shape=3fe82683 vocab=3327de7e
-/
theorem hasDerivAt_coeff_binaryFormRepSL {H : ℂ → ↥(BinaryForm ℂ n)} {w : ↥(BinaryForm ℂ n)} {z₀ : ℂ}
    (hH : ∀ e : Fin 2 →₀ ℕ, HasDerivAt (fun z : ℂ => coeff e ((H z : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      (coeff e ((w : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) z₀)
    (g : SL(2, ℤ)) (d : Fin 2 →₀ ℕ) :
    HasDerivAt
      (fun z : ℂ => coeff d ((binaryFormRepSL ℂ n g (H z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      (coeff d ((binaryFormRepSL ℂ n g w : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) z₀ := by
  have hfun : (fun z : ℂ => coeff d ((binaryFormRepSL ℂ n g (H z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      = fun z : ℂ => ∑ e ∈ degExps n,
          coeff e ((H z : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)
            * coeff d (binarySubst ℂ (g : Matrix (Fin 2) (Fin 2) ℤ) (monomial e 1)) :=
    funext fun z => coeff_binaryFormRepSL_eq_sum g (H z) d
  rw [hfun, coeff_binaryFormRepSL_eq_sum g w d]
  exact HasDerivAt.fun_sum fun e _ =>
    (hH e).mul_const (coeff d (binarySubst ℂ (g : Matrix (Fin 2) (Fin 2) ℤ) (monomial e 1)))

end RepDeriv

end EichlerIntegralAux

open EichlerIntegralAux in

/--
@isnad1 id=iseichle.1h4v.s12.41c9a56667d9 from=translated src=- shape=caf969fb vocab=4a8654cb
-/
theorem SolMain.slash {n : ℕ} {f : ℍ → ℂ} {F : ℍ → ↥(BinaryForm ℂ n)}
    (hF : IsEichlerIntegral n f F) (δ : SL(2, ℤ)) :
    IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] δ) (fun τ => binaryFormRepSL ℂ n δ⁻¹ (F (δ • τ))) := by
  intro d τ

  set c : ℂ := f (δ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ δ) ↑τ ^ (-2 : ℤ) with hc
  have hH : ∀ e : Fin 2 →₀ ℕ, HasDerivAt
      (fun z : ℂ => coeff e ((F (δ • ofComplex z) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      (coeff e (((c • linePow n ((δ • τ : ℍ) : ℂ)) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ)) ↑τ := by
    intro e
    have h1 := hasDerivAt_comp_smul
      (G := fun w : ℍ => coeff e ((F w : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      (g := fun w : ℍ => f w * coeff e ((linePow n (w : ℂ) : ↥(BinaryForm ℂ n)) : MvPolynomial (Fin 2) ℂ))
      (fun w => hF e w) δ τ
    refine h1.congr_deriv ?_
    rw [Submodule.coe_smul, coeff_smul, smul_eq_mul, hc]
    ring
  have h2 := hasDerivAt_coeff_binaryFormRepSL hH δ⁻¹ d
  refine h2.congr_deriv ?_

  have hJ : denom (Matrix.SpecialLinearGroup.mapGL ℝ δ) (τ : ℂ) ≠ 0 := denom_ne_zero _ _
  have hinv : binaryFormRepSL ℂ n δ⁻¹ (linePow n ((δ • τ : ℍ) : ℂ))
      = (jFactor δ τ ^ n)⁻¹ • linePow n (τ : ℂ) := by
    have h := congrArg (binaryFormRepSL ℂ n δ⁻¹) (binaryFormRepSL_linePow n δ τ)
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_smul] at h
    rw [h, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ (jFactor_ne_zero δ τ)), one_smul]
  have hslash : (f ∣[((n : ℤ) + 2)] δ) τ
      = f (δ • τ) * denom (Matrix.SpecialLinearGroup.mapGL ℝ δ) (τ : ℂ) ^ (-((n : ℤ) + 2)) :=
    SL_slash_apply _ _ _
  rw [map_smul, hinv, smul_smul, Submodule.coe_smul, coeff_smul, smul_eq_mul, hslash, jFactor_eq_denom, hc]
  congr 1
  rw [← zpow_natCast, ← zpow_neg, mul_assoc, ← zpow_add₀ hJ]
  congr 2
  ring

end HeckeEis

end

open scoped MatrixGroups ModularForm in
/--
@isnad1 id=iseichle.1h4v.s12.41c9a56667d9 from=translated src=- shape=caf969fb vocab=4a8654cb
-/
theorem solution {n : ℕ} {f : UpperHalfPlane → ℂ} {F : UpperHalfPlane → ↥(HeckeEis.BinaryForm ℂ n)}
    (hF : HeckeEis.IsEichlerIntegral n f F) (δ : SL(2, ℤ)) :
    HeckeEis.IsEichlerIntegral n (f ∣[((n : ℤ) + 2)] δ) (fun τ => HeckeEis.binaryFormRepSL ℂ n δ⁻¹ (F (δ • τ))) :=
  HeckeEis.SolMain.slash hF δ

