import Tengoku.EgzFormalProof.EGZ.Main.UpperBound
import Tengoku.EgzFormalProof.EGZ.Main.Parameters

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace EGZ

/-- A singleton is hollow, so the hollow constant is positive.
@isnad1 id=le.1h2v.s4.c9aab5e55364 from=translated src=- shape=e8a362dc vocab=e71f8465
-/
theorem one_le_hollowConstant {p d : ℕ} (hp : p.Prime) : 1 ≤ hollowConstant p d := by
  apply hollowConstant_max hp
  refine ⟨fun _ : Fin 1 ↦ 0, ?_⟩
  intro α hsum
  simp only [Fin.sum_univ_one] at hsum
  constructor
  · intro _
    exact ⟨0, hsum⟩
  · intro _
    simp

namespace MainProof

/-- A convenient prime-independent upper bound for the hollow constant.-/
def hollowBound (d : ℕ) : ℕ := (2 * d - 1).choose d + 1

/--
@isnad1 id=lt.0h1v.s3.e203124b4d7a from=translated src=- shape=8a62b088 vocab=cef91e0c
-/
theorem hollowBound_pos (d : ℕ) : 0 < hollowBound d := by unfold hollowBound; omega

/-- Restricting to the ceiling length gives a uniform bound for input mass
divided by the prime. This bound is needed before rounding the weights.
@isnad1 id=and.5h4v.s8.ae676789572a from=translated src=- shape=e76e2425 vocab=ae133fe9
-/
theorem normalized_input_bounds {p d : ℕ} [NeZero p] (hp : p.Prime) (hd : 0 < d)
    {ζ : ℝ} (hζ : 0 < ζ) (hζ1 : ζ ≤ 1)
    (f : FpCoord p d → ℕ)
    (hmass : natMass f = ⌈((hollowConstant p d : ℝ) + ζ) * (p : ℝ)⌉₊) :
    f ≠ 0 ∧ p ≤ natMass f ∧
      ((hollowConstant p d : ℝ) + ζ) * (p : ℝ) ≤ (natMass f : ℝ) ∧
      (natMass f : ℝ) ≤ ((hollowBound d : ℝ) + 2) * (p : ℝ) := by
  have hlow : ((hollowConstant p d : ℝ) + ζ) * (p : ℝ) ≤ (natMass f : ℝ) := by
    rw [hmass]
    exact Nat.le_ceil _
  have hw1 : (1 : ℝ) ≤ hollowConstant p d := by exact_mod_cast one_le_hollowConstant hp
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hplen : p ≤ natMass f := by
    have hreal : (p : ℝ) ≤ natMass f := by nlinarith
    exact_mod_cast hreal
  refine ⟨?_, hplen, hlow, ?_⟩
  · intro hf
    have hm0 : natMass f = 0 := by simp [hf, natMass]
    exact (not_le_of_gt hp.pos) (hm0 ▸ hplen)
  · have hwC : (hollowConstant p d : ℝ) ≤ hollowBound d := by
      exact_mod_cast hollowConstant_le_choose_add_one hp hd
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hceil := Nat.ceil_lt_add_one
      (show 0 ≤ ((hollowConstant p d : ℝ) + ζ) * (p : ℝ) by positivity)
    rw [← hmass] at hceil
    have hm := mul_le_mul_of_nonneg_right (add_le_add hwC hζ1) hp0.le
    nlinarith

end MainProof
end EGZ
