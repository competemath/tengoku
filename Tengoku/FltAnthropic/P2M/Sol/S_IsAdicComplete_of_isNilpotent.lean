import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsAdicComplete_of_isNilpotent.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsAdicComplete_of_isNilpotent

set_option autoImplicit false

universe u v

open IsLocalRing

/--
@isnad1 id=isadicco.1h2v.s6.b0847a08ba76 from=translated src=- shape=dc8fba2f vocab=83598597
-/
theorem solution {R : Type u} [CommRing R] {I : Ideal R} (hI : IsNilpotent I) :
    IsAdicComplete I R := by
  obtain ⟨N, hN⟩ := hI
  haveI : IsHausdorff I R := ⟨fun x hx => by
    have h := hx N
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, hN] at h
    exact h⟩
  haveI : IsPrecomplete I R := ⟨fun {f} hf => ⟨f N, fun n => by
    rcases le_or_gt n N with hn | hn
    · exact hf hn
    · have hzero : (I ^ n • ⊤ : Ideal R) = ⊥ := by
        rw [smul_eq_mul, Ideal.mul_top, eq_bot_iff, ← Ideal.zero_eq_bot, ← hN]
        exact Ideal.pow_le_pow_right hn.le
      rw [SModEq.sub_mem, hzero, Ideal.mem_bot, sub_eq_zero]
      have h := hf hn.le
      rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top, hN, Ideal.zero_eq_bot, Ideal.mem_bot,
        sub_eq_zero] at h
      exact h.symm⟩⟩
  exact ⟨⟩
