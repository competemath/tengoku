import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_ModThreeCyclotomic
import Tengoku.FltAnthropic.Definitions.Def_LanglandsTunnell_ExplicitLift
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_EisensteinChiNegThree
import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusTrace
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_IsFrobeniusAt_apply_eq_pow_of_pow_eq_one

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_det_lift_eq_chiNegThree_of_isFrobeniusAt.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_det_lift_eq_chiNegThree_of_isFrobeniusAt

set_option autoImplicit false

open WeierstrassCurve FLT.ExplicitLift EisensteinWeightOne
open scoped MatrixGroups

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace LanglandsTunnell
namespace DetLiftEngine

/--
@isnad1 id=or.0h1v.s7.2789ef27d62a from=translated src=- shape=99142880 vocab=5aeb07a0
-/
theorem units_coe_eq_one_or (u : (ℤ√(-2))ˣ) :
    (u : ℤ√(-2)) = 1 ∨ (u : ℤ√(-2)) = -1 := by
  have hn : (u : ℤ√(-2)).norm = 1 :=
    (Zsqrtd.norm_eq_one_iff' (by norm_num) _).mpr u.isUnit
  rw [Zsqrtd.norm_def] at hn
  have hb : (u : ℤ√(-2)).im = 0 := by
    nlinarith [mul_self_nonneg (u : ℤ√(-2)).re, mul_self_nonneg (u : ℤ√(-2)).im]
  rw [hb, mul_zero, sub_zero] at hn
  rcases Int.eq_one_or_neg_one_of_mul_eq_one hn with ha | ha
  · left
    exact Zsqrtd.ext ha hb
  · right
    exact Zsqrtd.ext ha hb

/--
@isnad1 id=eq.0h0v.s7.4391ba0cf1e4 from=translated src=- shape=3b2741e5 vocab=6c8b4505
-/
theorem red_one : red (1 : ℤ√(-2)) = 1 := map_one red

/--
@isnad1 id=eq.0h0v.s8.66a4db61bc45 from=translated src=- shape=3e469442 vocab=6c8b4505
-/
theorem red_neg_one : red (-1 : ℤ√(-2)) = -1 := by
  rw [map_neg, map_one]

/--
@isnad1 id=ne.0h0v.s7.3310f68601ff from=translated src=- shape=868742d0 vocab=4f12cd84
-/
theorem neg_one_ne_one_zmod_three : (-1 : ZMod 3) ≠ 1 := by decide

/--
@isnad1 id=eq.1h2v.s12.23bb7c8a20e0 from=translated src=- shape=5217c8c2 vocab=a7e72d20
-/
theorem red_det_apply
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (g : GL (Fin 2) (ZMod 3)) :
    red ((Matrix.GeneralLinearGroup.det (Ψ g) : (ℤ√(-2))ˣ) : ℤ√(-2)) =
      ((Matrix.GeneralLinearGroup.det g : (ZMod 3)ˣ) : ZMod 3) := by
  have h := Matrix.GeneralLinearGroup.map_det (f := red) (Ψ g)
  rw [hΨ g] at h
  have h' := congrArg (fun u : (ZMod 3)ˣ => (u : ZMod 3)) h
  simpa only [Units.coe_map, MonoidHom.coe_coe] using h'.symm

/--
@isnad1 id=eq.2h2v.s12.0cb9440a98c7 from=translated src=- shape=36eed5cd vocab=c2dfddde
-/
theorem det_apply_eq_of_det_eq_one
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (g : GL (Fin 2) (ZMod 3))
    (hg : ((Matrix.GeneralLinearGroup.det g : (ZMod 3)ˣ) : ZMod 3) = 1) :
    ((Matrix.GeneralLinearGroup.det (Ψ g) : (ℤ√(-2))ˣ) : ℤ√(-2)) = 1 := by
  rcases units_coe_eq_one_or (Matrix.GeneralLinearGroup.det (Ψ g)) with h | h
  · exact h
  · exfalso
    have hr := red_det_apply Ψ hΨ g
    rw [h, red_neg_one, hg] at hr
    exact neg_one_ne_one_zmod_three hr

/--
@isnad1 id=eq.2h2v.s12.10b9c296bdde from=translated src=- shape=46c004c4 vocab=c2dfddde
-/
theorem det_apply_eq_of_det_eq_neg_one
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g) (g : GL (Fin 2) (ZMod 3))
    (hg : ((Matrix.GeneralLinearGroup.det g : (ZMod 3)ˣ) : ZMod 3) = -1) :
    ((Matrix.GeneralLinearGroup.det (Ψ g) : (ℤ√(-2))ˣ) : ℤ√(-2)) = -1 := by
  rcases units_coe_eq_one_or (Matrix.GeneralLinearGroup.det (Ψ g)) with h | h
  · exfalso
    have hr := red_det_apply Ψ hΨ g
    rw [h, red_one, hg] at hr
    exact neg_one_ne_one_zmod_three hr.symm
  · exact h

/--
@isnad1 id=eq.3h3v.s10.67ee77e92b17 from=translated src=- shape=618ffb14 vocab=d5f8ee70
-/
theorem modThreeCyclotomicChar_eq_natCast (p : ℕ) (hp : Nat.Coprime 3 p)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ p) :
    ((modThreeCyclotomicChar σ : (ZMod 3)ˣ) : ZMod 3) = (p : ZMod 3) := by
  rw [modThreeCyclotomicChar_apply]
  symm
  apply modularCyclotomicCharacter.unique
  intro t ht
  have h3 : ((t : (AlgebraicClosure ℚ)ˣ) : AlgebraicClosure ℚ) ^ 3 = 1 := by
    have := (mem_rootsOfUnity 3 t).mp ht
    have := congrArg Units.val this
    simpa using this
  have key := ValuationSubring.IsFrobeniusAt.apply_eq_pow_of_pow_eq_one A σ p 3 hA hσ hp
    (t : AlgebraicClosure ℚ) h3
  rw [AlgEquiv.coe_ringEquiv, key, ZMod.val_natCast]
  conv_lhs => rw [← Nat.div_add_mod p 3]
  rw [pow_add, pow_mul, h3, one_pow, one_mul]

/--
@isnad1 id=eq.1h1v.s5.103c8e82e124 from=translated src=- shape=dc3440d1 vocab=c9252d50
-/
theorem chiNegThree_of_mod_eq_one {p : ℕ} (h : p % 3 = 1) : chiNegThree p = 1 := by
  simp [chiNegThree, h]

/--
@isnad1 id=eq.1h1v.s5.a5ee70a3811a from=translated src=- shape=ad015130 vocab=25ffb268
-/
theorem chiNegThree_of_mod_eq_two {p : ℕ} (h : p % 3 = 2) : chiNegThree p = -1 := by
  simp [chiNegThree, h]

/--
@isnad1 id=eq.6h5v.s13.b68ed604ba26 from=translated src=- shape=beea1b69 vocab=a1e6a537
-/
theorem det_lift_coe_eq_chiNegThree
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g)
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ p) :
    ((Matrix.GeneralLinearGroup.det (Ψ (ρ σ)) : (ℤ√(-2))ˣ) : ℤ√(-2)) =
      ((chiNegThree p : ℤ) : ℤ√(-2)) := by
  have hcop : Nat.Coprime 3 p := by
    rw [Nat.coprime_primes (by norm_num) hp]
    exact fun h => hp3 h.symm
  have hχ : ((Matrix.GeneralLinearGroup.det (ρ σ) : (ZMod 3)ˣ) : ZMod 3) = (p : ZMod 3) := by
    rw [hdet σ]
    exact modThreeCyclotomicChar_eq_natCast p hcop A hA σ hσ
  have hp0 : p % 3 ≠ 0 := by
    intro h
    have h3 : 3 ∣ p := Nat.dvd_of_mod_eq_zero h
    rcases (Nat.dvd_prime hp).mp h3 with h | h
    · norm_num at h
    · exact hp3 h.symm
  have hcases : p % 3 = 1 ∨ p % 3 = 2 := by
    have := Nat.mod_lt p (show 0 < 3 by norm_num)
    omega
  rcases hcases with h1 | h2
  ·
    have hg : ((Matrix.GeneralLinearGroup.det (ρ σ) : (ZMod 3)ˣ) : ZMod 3) = 1 := by
      rw [hχ]
      have : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
      rw [this, h1, Nat.cast_one]
    rw [det_apply_eq_of_det_eq_one Ψ hΨ (ρ σ) hg, chiNegThree_of_mod_eq_one h1]
    simp
  ·
    have hg : ((Matrix.GeneralLinearGroup.det (ρ σ) : (ZMod 3)ˣ) : ZMod 3) = -1 := by
      rw [hχ]
      have : (p : ZMod 3) = ((p % 3 : ℕ) : ZMod 3) := (ZMod.natCast_mod p 3).symm
      rw [this, h2]
      decide
    rw [det_apply_eq_of_det_eq_neg_one Ψ hΨ (ρ σ) hg, chiNegThree_of_mod_eq_two h2]
    simp

end LanglandsTunnell.DetLiftEngine

/--
@isnad1 id=eq.6h5v.s13.aa204c02b753 from=translated src=- shape=b41406b3 vocab=68968952
-/
theorem solution
    (ρ : Γℚ →* GL (Fin 2) (ZMod 3))
    (hdet : ∀ σ : Γℚ, Matrix.GeneralLinearGroup.det (ρ σ) = modThreeCyclotomicChar σ)
    (Ψ : GL (Fin 2) (ZMod 3) →* GL (Fin 2) (ℤ√(-2)))
    (hΨ : ∀ g, Matrix.GeneralLinearGroup.map red (Ψ g) = g)
    (p : ℕ) (hp : p.Prime) (hp3 : p ≠ 3)
    (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime p)
    (σ : Γℚ) (hσ : A.IsFrobeniusAt σ p) :
    ((Ψ (ρ σ) : GL (Fin 2) (ℤ√(-2))) : Matrix (Fin 2) (Fin 2) (ℤ√(-2))).det =
      ((chiNegThree p : ℤ) : ℤ√(-2)) := by
  rw [← Matrix.GeneralLinearGroup.val_det_apply]
  exact LanglandsTunnell.DetLiftEngine.det_lift_coe_eq_chiNegThree ρ hdet Ψ hΨ p hp hp3 A hA σ hσ
