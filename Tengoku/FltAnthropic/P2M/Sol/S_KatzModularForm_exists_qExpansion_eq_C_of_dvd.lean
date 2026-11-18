import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_KatzLevelOne

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_KatzModularForm_exists_qExpansion_eq_C_of_dvd.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_KatzModularForm_exists_qExpansion_eq_C_of_dvd

set_option autoImplicit false

noncomputable section

open WeierstrassCurve

universe u

namespace KatzModularForm
export _root_.Tengoku.FltAnthropic.KatzModularForm (qExpansion qExpansion_smul toFun toFun_variableChange map_toFun)
open _root_.Tengoku.FltAnthropic.KatzModularForm

variable (R : Type u) [CommRing R]

def b₂Scaled (d : R) (hd : (12 : R) * d = 0) : KatzModularForm R 2 where
  toFun A _ _ W _ := algebraMap R A d * W.b₂
  map_toFun := by
    intro A B _ _ _ _ f W hW hW'
    rw [W.map_b₂ (f : A →+* B), map_mul, AlgHom.commutes]
    rfl
  toFun_variableChange := by
    intro A _ _ C W hW hW'
    have h12 : (12 : A) * algebraMap R A d = 0 := by
      have h := congrArg (algebraMap R A) hd
      rwa [map_mul, map_ofNat, map_zero] at h
    rw [W.variableChange_b₂ C,
      show ((C.u⁻¹ ^ (2 : ℤ) : Aˣ) : A) = ((C.u⁻¹ : Aˣ) : A) ^ 2 by norm_cast]
    linear_combination ((C.u⁻¹ : Aˣ) : A) ^ 2 * C.r * h12

/--
@isnad1 id=eq.2h4v.s7.13ca8ad97792 from=translated src=- shape=110dc72d vocab=377d6810
-/
@[scoped simp] theorem b₂Scaled_toFun (d : R) (hd : (12 : R) * d = 0) {A : Type u} [CommRing A]
    [Algebra R A] (W : WeierstrassCurve A) (hW : IsUnit W.Δ) :
    (b₂Scaled R d hd).toFun W hW = algebraMap R A d * W.b₂ := rfl

/--
@isnad1 id=eq.0h1v.s6.fbf5057aae8b from=translated src=- shape=436751ca vocab=99f4bd25
-/
theorem b₂_tateLaurent : (ModularCurve.tateLaurent R).b₂ = 1 := by
  rw [ModularCurve.tateLaurent, WeierstrassCurve.map_b₂]
  simp [WeierstrassCurve.b₂, ModularCurve.tatePowerSeries]

/--
@isnad1 id=eq.1h2v.s7.43ed2f32b8d4 from=translated src=- shape=2ec0a65d vocab=233a0a0a
-/
theorem qExpansion_b₂Scaled (d : R) (hd : (12 : R) * d = 0) :
    (b₂Scaled R d hd).qExpansion = HahnSeries.C d := by
  rw [qExpansion, b₂Scaled_toFun, b₂_tateLaurent, mul_one, RingHom.algebraMap_toAlgebra]
  simp

/--
@isnad1 id=ex.1h2v.s8.a81cd1bd0b98 from=translated src=- shape=f0a97526 vocab=512ee27a
-/
theorem exists_qExpansion_eq_C_of_dvd (m : ℕ) (c : ℤ) (hc : ((m / Nat.gcd m 12 : ℕ) : ℤ) ∣ c) :
    ∃ F : KatzModularForm (ZMod m) 2, F.qExpansion = HahnSeries.C (c : ZMod m) := by
  obtain ⟨e, rfl⟩ := hc
  have key : 12 * (m / Nat.gcd m 12) = 12 / Nat.gcd m 12 * m := by
    rw [← Nat.mul_div_assoc 12 (Nat.gcd_dvd_left m 12),
      Nat.div_mul_right_comm (Nat.gcd_dvd_right m 12) m]
  have h12 : (12 : ZMod m) * ((m / Nat.gcd m 12 : ℕ) : ZMod m) = 0 := by
    have h := congrArg (Nat.cast : ℕ → ZMod m) key
    push_cast at h
    rw [h, ZMod.natCast_self, mul_zero]
  refine ⟨(e : ZMod m) • b₂Scaled (ZMod m) _ h12, ?_⟩
  rw [qExpansion_smul, qExpansion_b₂Scaled, ← HahnSeries.C_mul_eq_smul, ← map_mul]
  congr 1
  rw [Int.cast_mul, Int.cast_natCast, mul_comm]

end KatzModularForm
open scoped _root_.P2MW.S_KatzModularForm_exists_qExpansion_eq_C_of_dvd.KatzModularForm

end
open scoped _root_.P2MW.S_KatzModularForm_exists_qExpansion_eq_C_of_dvd.KatzModularForm

/--
@isnad1 id=ex.1h2v.s8.a81cd1bd0b98 from=translated src=- shape=f0a97526 vocab=512ee27a
-/
theorem solution (m : ℕ) (c : ℤ)
    (hc : ((m / Nat.gcd m 12 : ℕ) : ℤ) ∣ c) :
    ∃ F : KatzModularForm (ZMod m) 2, F.qExpansion = HahnSeries.C (c : ZMod m) :=
  KatzModularForm.exists_qExpansion_eq_C_of_dvd m c hc
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
