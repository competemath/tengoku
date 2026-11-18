import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_KroneckerTransport
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PhiGen

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne
set_option autoImplicit false

open Polynomial ModularCurve

namespace KroneckerDeriv

variable (k : Type*) [Field k]

noncomputable def swapK : Polynomial (Polynomial k) →+* Polynomial (Polynomial k) :=
  Polynomial.eval₂RingHom (Polynomial.aeval (R := k) (Polynomial.X : Polynomial (Polynomial k))).toRingHom
    (Polynomial.C Polynomial.X)

variable {k}

/--
@isnad1 id=eq.0h1v.s9.3dd20cdea40f from=translated src=- shape=2f662699 vocab=3d5f34d7
-/
@[scoped simp] theorem swapK_X : swapK k Polynomial.X = Polynomial.C Polynomial.X := Polynomial.eval₂_X _ _

/--
@isnad1 id=eq.0h2v.s9.c5679ea5e214 from=translated src=- shape=2b5b7bda vocab=15283804
-/
@[scoped simp] theorem swapK_C (p : Polynomial k) : swapK k (Polynomial.C p) = Polynomial.aeval (R := k) (Polynomial.X : Polynomial (Polynomial k)) p := by
  simp [swapK]

/--
@isnad1 id=eq.0h2v.s9.8bb79bf82d47 from=translated src=- shape=a0176091 vocab=2ec59730
-/
theorem map_swapBivar (Φ : Polynomial (Polynomial ℤ)) :
    (swapBivar Φ).map (Polynomial.mapRingHom (Int.castRingHom k)) = swapK k (Φ.map (Polynomial.mapRingHom (Int.castRingHom k))) := by

  have h : (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom k))).comp swapBivar
      = (swapK k).comp (Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom k))) := by
    refine Polynomial.ringHom_ext' ?_ ?_
    · refine Polynomial.ringHom_ext' (RingHom.ext_int _ _) ?_
      simp [swapBivar_C_X]
    · simp [swapBivar_X]
  have := congrArg (fun f => f Φ) h
  simpa using this

/--
@isnad1 id=eq.1h3v.s10.d3dcf8b0b927 from=translated src=- shape=51e8e71b vocab=82f8fd92
-/
theorem reduce (ℓ : ℕ) [Fact ℓ.Prime] [CharP k ℓ] (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data) :
    data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k))
      = (Polynomial.C Polynomial.X ^ ℓ - Polynomial.X) * (Polynomial.C Polynomial.X - Polynomial.X ^ ℓ) := by
  have hfac : Int.castRingHom k = (ZMod.castHom (dvd_refl ℓ) k).comp (Int.castRingHom (ZMod ℓ)) :=
    RingHom.ext_int _ _
  rw [hfac, ← Polynomial.mapRingHom_comp, ← Polynomial.map_map,
    show data.Φ.map (Polynomial.mapRingHom (Int.castRingHom (ZMod ℓ))) = reduceModBivar ℓ data.Φ from rfl, hKr]
  simp [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow]

end KroneckerDeriv
open scoped _root_.P2MW.S_ModularCurve_derivative_evalEval_ne_zero_of_kroneckerCongruence_of_pow_sq_ne.KroneckerDeriv

open KroneckerDeriv in

/--
@isnad1 id=and.2h4v.s10.4276c229f0cf from=translated src=- shape=09855dc1 vocab=509a8bda
-/
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (data : ModularPolynomialData ℓ) (hKr : KroneckerCongruence ℓ data)
    (k : Type*) [Field k] [CharP k ℓ] (b : k) (hb : b ^ (ℓ ^ 2) ≠ b) :
    (Polynomial.derivative (data.Φ.map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval b (b ^ ℓ) ≠ 0 ∧
    (Polynomial.derivative ((swapBivar data.Φ).map (Polynomial.mapRingHom (Int.castRingHom k)))).evalEval b (b ^ ℓ) ≠ 0 := by
  have hred := KroneckerDeriv.reduce (k := k) ℓ data hKr
  have hbq : (b ^ ℓ) ^ ℓ = b ^ (ℓ ^ 2) := by rw [← pow_mul, sq]
  have hne : b ^ (ℓ ^ 2) - b ≠ 0 := sub_ne_zero.mpr hb
  have hℓ : ((ℓ : ℕ) : k) = 0 := CharP.cast_eq_zero k ℓ
  refine ⟨?_, ?_⟩
  · rw [hred]
    simp only [Polynomial.evalEval, Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_pow,
      Polynomial.derivative_C, Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_neg,
      Polynomial.eval_one, mul_zero, sub_zero, zero_sub, mul_one]
    rw [hbq]
    intro h
    apply hne
    linear_combination h
  · rw [map_swapBivar, hred]
    simp only [map_mul, map_sub, map_pow, swapK_X, swapK_C, Polynomial.aeval_X, Polynomial.evalEval,
      Polynomial.derivative_mul, Polynomial.derivative_sub, Polynomial.derivative_pow, Polynomial.derivative_C,
      Polynomial.derivative_X, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_sub, Polynomial.eval_pow,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_natCast, Polynomial.eval_neg, Polynomial.eval_one,
      mul_zero, sub_zero, zero_sub, mul_one, hℓ]
    rw [hbq]
    intro h
    apply hne
    linear_combination h
