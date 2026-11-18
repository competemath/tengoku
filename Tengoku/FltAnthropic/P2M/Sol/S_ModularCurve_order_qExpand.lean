import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_X0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_order_qExpand.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_order_qExpand

open ModularCurve

/--
@isnad1 id=eq.0h3v.s7.84b84066a22a from=translated src=- shape=bf7865a7 vocab=776847ba
-/
theorem solution {R : Type*} [CommRing R] (N : ℕ) [NeZero N] (f : LaurentSeries R) : (qExpand R N f).order = N * f.order := by
  rcases eq_or_ne f 0 with rfl | hf
  · rw [map_zero, HahnSeries.order_zero, mul_zero]
  have hc : (qExpand R N f).coeff ((N : ℤ) * f.order) ≠ 0 := by
    rw [qExpand_coeff_mul]
    exact HahnSeries.coeff_order_eq_zero.not.mpr hf
  have hne : qExpand R N f ≠ 0 := fun h0 => hc (by rw [h0]; rfl)
  refine le_antisymm (HahnSeries.order_le_of_coeff_ne_zero hc) ?_
  by_contra! hlt
  have hk := HahnSeries.coeff_order_eq_zero.not.mpr hne
  by_cases hdvd : (N : ℤ) ∣ (qExpand R N f).order
  · obtain ⟨m, hm⟩ := hdvd
    rw [hm, qExpand_coeff_mul] at hk
    have hNpos : (0 : ℤ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    have hmlt : m < f.order := by
      rw [hm] at hlt
      exact lt_of_mul_lt_mul_left hlt hNpos.le
    exact hk (HahnSeries.coeff_eq_zero_of_lt_order hmlt)
  · exact hk (qExpand_coeff_of_not_dvd N f hdvd)
