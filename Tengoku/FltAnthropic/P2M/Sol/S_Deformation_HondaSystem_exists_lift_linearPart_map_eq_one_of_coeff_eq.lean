import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_HondaSystem_exists_lift_linearPart_map_eq_one_of_coeff_eq.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_HondaSystem_exists_lift_linearPart_map_eq_one_of_coeff_eq

set_option autoImplicit false

universe u

theorem solution
    {𝓞 : Type u} [CommRing 𝓞] (p : ℕ) [Fact p.Prime]
    [Algebra 𝓞 (ZMod p)] (hker : RingHom.ker (algebraMap 𝓞 (ZMod p)) = Ideal.span {(p : 𝓞)})
    {d : ℕ} (abar : Fin d → ℕ → MvPowerSeries (Fin d) (ZMod p))
    (habar : ∀ i n, MvPowerSeries.constantCoeff (abar i n) = 0)
    (h0 : ∀ i j : Fin d, MvPowerSeries.coeff (Finsupp.single j 1) (abar i 0) = if i = j then 1 else 0)
    (h1 : ∀ i j : Fin d, j ≤ i → MvPowerSeries.coeff (Finsupp.single j 1) (abar i 1) = 0) :
    ∃ a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞,
      (∀ i n, MvPowerSeries.map (algebraMap 𝓞 (ZMod p)) (a i n) = abar i n) ∧
      (∀ i n, MvPowerSeries.constantCoeff (a i n) = 0) ∧
      IsUnit ((MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}))) ∧
      ((MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) = 1 ∧
        ∀ i j : Fin d, j ≤ i → MvFormalGroup.linearPart (fun i => a i 1) i j ∈ Ideal.span {(p : 𝓞)}) := by
  classical

  have hsurj : Function.Surjective (algebraMap 𝓞 (ZMod p)) := ZMod.ringHom_surjective _
  let s : ZMod p → 𝓞 := fun t => if t = 0 then 0 else Classical.choose (hsurj t)
  have hs : ∀ t, algebraMap 𝓞 (ZMod p) (s t) = t := by
    intro t
    by_cases ht : t = 0
    · subst ht; simp only [s, ite_eq_left rfl, map_zero]
    · simp only [s, ite_eq_right ht]; exact Classical.choose_spec (hsurj t)
  have hs0 : s 0 = 0 := by simp only [s, ite_eq_left rfl]
  have hsmk : ∀ t : ZMod p, t = 0 → Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}) (s t) = 0 := by
    intro t ht; rw [ht, hs0, map_zero]
  have hs1 : Ideal.Quotient.mk (Ideal.span {(p : 𝓞)}) (s 1) = 1 := by
    rw [← map_one (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})), Ideal.Quotient.eq, ← hker, RingHom.mem_ker,
      map_sub, hs, map_one, sub_self]

  let a : Fin d → ℕ → MvPowerSeries (Fin d) 𝓞 := fun i n m => s (abar i n m)
  have hcoeff : ∀ i n m, MvPowerSeries.coeff m (a i n) = s (MvPowerSeries.coeff m (abar i n)) := fun _ _ _ => rfl
  refine ⟨a, fun i n => ?_, fun i n => ?_, ?_, ?_, fun i j hji => ?_⟩
  · ext m; rw [MvPowerSeries.coeff_map, hcoeff, hs]
  · rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hcoeff, MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      habar, hs0]
  · have h : (MvFormalGroup.linearPart fun i => a i 0).map (Ideal.Quotient.mk (Ideal.span {(p : 𝓞)})) = 1 := by
      ext i j
      rw [Matrix.map_apply, MvFormalGroup.linearPart, Matrix.of_apply, hcoeff, h0, Matrix.one_apply]
      split_ifs with hij
      · exact hs1
      · exact hsmk 0 rfl
    rw [h]; exact isUnit_one
  · ext i j
    rw [Matrix.map_apply, MvFormalGroup.linearPart, Matrix.of_apply, hcoeff, h0, Matrix.one_apply]
    split_ifs with hij
    · exact hs1
    · exact hsmk 0 rfl
  · rw [MvFormalGroup.linearPart, Matrix.of_apply, hcoeff, h1 i j hji, hs0]
    exact Ideal.zero_mem _
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
