/-
PdtMahlerTheta — the exact constant: the degree-4 Mahler minimum IS the
second-smallest Pisot number.

  `mahler_fam_pisot` : M := M(x⁴−x−1) satisfies M⁴ = M³ + 1 and 1 < M —
  i.e. the minimal quartic Mahler measure is the root > 1 of x⁴−x³−1
  (θ₄, Siegel's second-smallest Pisot number; banked F:277).

Route: M(x⁴−x−1) = M(x⁴−x³−1) by reversal invariance (tie_revneg_eq);
x⁴−x³−1 is Pisot-shaped — its non-real roots lie strictly inside the
unit circle (the PdtPisotBoundary (σ,s)-reduction, flipped inequality),
its real roots lie in (−1,0) ∪ (69/50, 2) with the outside one unique —
so the measure equals that single outside root. Multiplicity is excluded
by the kernel-certified bracket 11/10 < M ≤ 139/100. No calculus, no
discriminants, no irreducibility.
-/
import Tengoku.PdtLean.PdtMahlerMain

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace PDT
namespace Mahler
open Polynomial Complex

noncomputable section

/-- Kernel bracket, lower side: `11/10 < M(x⁴−x−1)`.
@isnad1 id=lt.0h0v.s6.a746db4ea158 from=translated src=- shape=71a67939 vocab=1e2941a7
-/
lemma fam_lower_11 :
    (11 : ℝ) / 10
      < ((zq4 (0, 0, -1, -1)).map (Int.castRingHom ℂ)).mahlerMeasure := by
  have hs := lowerCert_sound (P := 11) (Q := 10) (by norm_num) 9 0 (0, 0, -1, -1)
  simp only [pow_zero, pow_one, Function.iterate_zero_apply] at hs
  have h' : lowerCert 9 ((11 : ℕ) : ℤ) ((10 : ℕ) : ℤ) (0, 0, -1, -1) = true := by
    exact_mod_cast (by decide : lowerCert 9 (11 : ℤ) (10 : ℤ) (0, 0, -1, -1) = true)
  exact_mod_cast hs h'

/-- Products of `max 1 ‖·‖` are at least one.
@isnad1 id=le.0h1v.s5.b628e0974fc7 from=translated src=- shape=634136a5 vocab=fcd570a2
-/
lemma one_le_prod_max (s : Multiset ℂ) :
    1 ≤ (s.map fun r => max 1 ‖r‖).prod := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons r s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      calc (1:ℝ) = 1 * 1 := by norm_num
        _ ≤ max 1 ‖r‖ * (s.map fun r => max 1 ‖r‖).prod :=
            mul_le_mul (le_max_left _ _) ih (by norm_num)
              (le_trans (by norm_num) (le_max_left _ _))

end

end Mahler
end PDT
