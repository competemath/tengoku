import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_PhiGen
import Tengoku.Seed.RingTheory.RootsOfUnity.PrimitiveRoots

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_mem_range_qExpand_of_qTwist_eq.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_mem_range_qExpand_of_qTwist_eq

set_option autoImplicit false

namespace ModularCurve
export _root_.ModularCurve (qTwist qTwist_coeff qExpand qExpand_coeff_mul qExpand_coeff_of_not_dvd)
open _root_.ModularCurve

theorem coeff_eq_zero_of_qTwist_eq {K : Type*} [Field K] (n : ℕ) [NeZero n] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) n) (f : LaurentSeries K) (h : qTwist ζ f = f) {k : ℤ}
    (hk : ¬ (n : ℤ) ∣ k) : f.coeff k = 0 := by
  have hc := congrArg (fun g : LaurentSeries K => g.coeff k) h
  simp only [qTwist_coeff] at hc

  have hne : ((ζ ^ k : Kˣ) : K) ≠ 1 := by
    rw [Units.val_zpow_eq_zpow_val]
    exact fun h1 => hk ((hζ.zpow_eq_one_iff_dvd k).mp h1)
  have : (((ζ ^ k : Kˣ) : K) - 1) * f.coeff k = 0 := by rw [sub_mul, one_mul, hc, sub_self]
  rcases mul_eq_zero.mp this with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hne
  · exact h0

theorem mem_range_qExpand_of_qTwist_eq' {K : Type*} [Field K] (n : ℕ) [NeZero n] (ζ : Kˣ)
    (hζ : IsPrimitiveRoot (ζ : K) n) (f : LaurentSeries K) (h : qTwist ζ f = f) :
    f ∈ Set.range (qExpand K n) := by
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)

  have hbdd : BddBelow (Function.support fun m : ℤ => f.coeff ((n : ℤ) * m)) := by
    refine ⟨min f.order 0, fun m hm => ?_⟩
    have hm' : f.coeff ((n : ℤ) * m) ≠ 0 := hm
    have hord : f.order ≤ (n : ℤ) * m := HahnSeries.order_le_of_coeff_ne_zero hm'
    rcases le_or_gt 0 m with h0 | h0
    · exact (min_le_right _ _).trans h0
    · have : (n : ℤ) * m ≤ m := by nlinarith
      exact (min_le_left _ _).trans (hord.trans this)
  refine ⟨HahnSeries.ofSuppBddBelow _ hbdd, ?_⟩
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [qExpand_coeff_mul, HahnSeries.coeff_ofSuppBddBelow]
  · rw [qExpand_coeff_of_not_dvd n _ hk, coeff_eq_zero_of_qTwist_eq n ζ hζ f h hk]

end ModularCurve

theorem solution {K : Type*} [Field K] (n : ℕ) [NeZero n] (ζ : Kˣ) (hζ : IsPrimitiveRoot (ζ : K) n) (f : LaurentSeries K) (h : ModularCurve.qTwist ζ f = f) : f ∈ Set.range (ModularCurve.qExpand K n) :=
  ModularCurve.mem_range_qExpand_of_qTwist_eq' n ζ hζ f h
