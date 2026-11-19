import Tengoku.Linearhadwiger.HadwigerLean.Coloring.LowCodegreeRounding
import Tengoku.Linearhadwiger.HadwigerLean.Quantitative.Constants
import Tengoku.Linearhadwiger.HadwigerLean.Quantitative.MatchingApplication
import Tengoku.Linearhadwiger.HadwigerLean.Quantitative.MatchingParameterBridge

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Quantitative low-codegree rounding bridge

The finite token/dummy sample is passed to the quantitative matching theorem.
-/

namespace HadwigerLean.LowCodegreeRounding

section MatchingOfPaperSample

variable {W E : Type*} [Fintype W] [Fintype E]
  [DecidableEq W] [DecidableEq E]

end MatchingOfPaperSample

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section TokenDummyMatchingBridge

variable {V : Type*} [Fintype V] [DecidableEq V]

end TokenDummyMatchingBridge

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.LowCodegreeRounding

section RoundedCounts

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- Choose the paper's token and dummy counts by natural ceilings.
The sample-size bound makes the dummy count large enough for every edge.
@isnad1 id=ex.7h5v.s8.9139609a5fa5 from=translated src=- shape=3c74798e vocab=744cb3e6
-/
theorem exists_rounded_token_dummy_counts (G : SimpleGraph V)
    (m : ℕ) (hm : 1 ≤ m)
    (x : StableSet G → ℝ) (hx : ∀ S, 0 ≤ x S)
    (hstable : ∀ S : StableSet G, S.1.card ≤ m)
    (hload : ∀ v, vertexLoad G x v = 1)
    (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
    (hscale : 1000000 * (((m + 2 : ℕ) : ℝ) ^ 4) ≤
      μ ^ 4 * (Fintype.card V : ℝ)) :
    ∃ p z : ℕ, 0 < p ∧ m + 1 ≤ z ∧
      fractionalCost G x ≤ (p : ℝ) ∧
      (p : ℝ) ≤ fractionalCost G x + 1 ∧
      ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
        (Fintype.card V : ℝ) ≤ (z : ℝ) ∧
      (z : ℝ) ≤
        ((m + 1 : ℕ) : ℝ) * fractionalCost G x -
          (Fintype.card V : ℝ) + 1 := by
  let n : ℝ := Fintype.card V
  let τ := fractionalCost G x
  let A := ((m + 1 : ℕ) : ℝ) * τ - n
  let p := ⌈τ⌉₊
  let z := ⌈A⌉₊
  have hscales := paper_scale_implies_rounding_scales m n μ hm hμ hμ1 hscale
  have hnpos : 0 < n := by linarith [hscales.2.2.1]
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hmn : n ≤ (m : ℝ) * τ :=
    card_le_m_mul_fractionalCost G m x hx hstable hload
  have hτpos : 0 < τ := by
    by_contra h
    have hτnonpos : τ ≤ 0 := le_of_not_gt h
    have hprod : (m : ℝ) * τ ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hmR.le hτnonpos
    linarith
  have hTA : τ ≤ A := by
    dsimp [A]
    push_cast
    nlinarith [hmn]
  have hApos : 0 < A := lt_of_lt_of_le hτpos hTA
  have hμn : μ * n ≤ n :=
    (mul_le_mul_of_nonneg_right hμ1 hnpos.le).trans_eq (one_mul n)
  have h4mn : 4 * (m : ℝ) ^ 2 ≤ n := hscales.1.trans hμn
  have hτ4 : 4 * (m : ℝ) ≤ τ := by
    apply (mul_le_mul_iff_of_pos_left hmR).mp
    calc
      (m : ℝ) * (4 * (m : ℝ)) = 4 * (m : ℝ) ^ 2 := by ring
      _ ≤ n := h4mn
      _ ≤ (m : ℝ) * τ := hmn
  have hAlarge : (((m + 1 : ℕ) : ℝ)) ≤ A := by
    have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
    dsimp [A]
    push_cast
    nlinarith [hTA, hτ4]
  have hTlower : τ ≤ (p : ℝ) := Nat.le_ceil τ
  have hTupper : (p : ℝ) ≤ τ + 1 :=
    (Nat.ceil_lt_add_one hτpos.le).le
  have hZlower : A ≤ (z : ℝ) := Nat.le_ceil A
  have hZupper : (z : ℝ) ≤ A + 1 :=
    (Nat.ceil_lt_add_one hApos.le).le
  have hp : 0 < p := by
    have hpr : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hτpos hTlower
    exact_mod_cast hpr
  have hz : m + 1 ≤ z := by
    have hzr : (((m + 1 : ℕ) : ℝ)) ≤ (z : ℝ) := hAlarge.trans hZlower
    exact_mod_cast hzr
  exact ⟨p, z, hp, hz, hTlower, hTupper, hZlower, hZupper⟩

end RoundedCounts

end HadwigerLean.LowCodegreeRounding

namespace HadwigerLean.Theorem2

section PaperRounding

variable {V : Type*} [Fintype V] [DecidableEq V]

end PaperRounding

end HadwigerLean.Theorem2
