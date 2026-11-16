import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorPushPull

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicCurve_Divisor_pushforward_pullback_of_finite.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicCurve_Divisor_pushforward_pullback_of_finite

open _root_.AlgebraicCurve

namespace AlgebraicCurve
export _root_.AlgebraicCurve (Divisor.pushforward Place.mem_fiber Divisor.pullback SumRamificationInertia SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg Place Divisor HasPrincipalDivisors)
namespace Divisor
export _root_.AlgebraicCurve.Divisor (pushforward pushforward_single pullback pullback_single degree smul_apply)
open _root_.AlgebraicCurve.Divisor open _root_.AlgebraicCurve
variable {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F']

private theorem pushforward_pullback_single (v : Place K F) (n : ℤ) :
    pushforward F (pullback F' (Finsupp.single v n))
      = Finsupp.single v
          (n * ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
  rw [pullback_single, map_sum]
  calc
    ∑ w ∈ v.fiber F', pushforward F (Finsupp.single w (n * (w.ramificationIndex F : ℤ)))
        = ∑ w ∈ v.fiber F',
            Finsupp.single v
              (n * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ))) := by
          refine Finset.sum_congr rfl fun w hw => ?_
          rw [pushforward_single, Place.mem_fiber.mp hw, mul_assoc]
    _ = Finsupp.single v
          (∑ w ∈ v.fiber F', n * ((w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ))) :=
          (Finsupp.single_finsetSum _ _ _).symm
    _ = Finsupp.single v
          (n * ∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) := by
          rw [← Finset.mul_sum]

private theorem pushforward_pullback_apply (D : Divisor K F) (v : Place K F) :
    pushforward F (pullback F' D) v
      = (∑ w ∈ v.fiber F', (w.ramificationIndex F : ℤ) * (w.inertiaDeg F : ℤ)) * D v := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add u n D _ _ ih =>
    rw [map_add, map_add, Finsupp.add_apply, Finsupp.add_apply, ih,
      pushforward_pullback_single, mul_add]
    congr 1
    by_cases huv : u = v
    · subst huv
      rw [Finsupp.single_eq_same, Finsupp.single_eq_same, mul_comm]
    · rw [Finsupp.single_eq_of_ne (Ne.symm huv), Finsupp.single_eq_of_ne (Ne.symm huv),
        mul_zero]

private theorem pushforward_pullback_of_sumRam [SumRamificationInertia K F F'] (D : Divisor K F) :
    pushforward F (pullback F' D) = (Module.finrank F F' : ℤ) • D := by
  ext v
  rw [pushforward_pullback_apply,
    SumRamificationInertia.sum_ramificationIndex_mul_inertiaDeg (F' := F') v,
    Finsupp.smul_apply, smul_eq_mul]

end AlgebraicCurve.Divisor

theorem solution {K F F' : Type*} [Field K] [Field F] [Field F'] [Algebra K F] [Algebra K F'] [Algebra F F'] [IsScalarTower K F F'] [Algebra.IsIntegral F F'] [HasPrincipalDivisors K F'] [Module.Finite F F'] [SumRamificationInertia K F F'] (D : Divisor K F) : Divisor.pushforward F (Divisor.pullback F' D) = (Module.finrank F F' : ℤ) • D :=
  AlgebraicCurve.Divisor.pushforward_pullback_of_sumRam D
