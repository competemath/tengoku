import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvPolynomial_CrossingQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPolynomial_CrossingQuotient_ringKrullDim_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPolynomial_CrossingQuotient_ringKrullDim_le

set_option autoImplicit false

universe u

open CategoryTheory AlgebraicGeometry MvPolynomial

theorem solution
    (W : Type u) [CommRing W] [IsDomain W] [IsNoetherianRing W] (n : ℕ) (hW : ringKrullDim W = n)
    (t : W) (ht : t ≠ 0) :
    ringKrullDim (CrossingQuotient W t) ≤ n + 1 := by
  have hf : (X 0 * X 1 - C t : MvPolynomial (Fin 2) W) ≠ 0 := by
    intro h
    have h0 := congrArg MvPolynomial.constantCoeff h
    simp at h0
    exact ht h0
  have h1 := ringKrullDim_quotient_succ_le_of_nonZeroDivisor (mem_nonZeroDivisors_of_ne_zero hf)
  rw [MvPolynomial.ringKrullDim_of_isNoetherianRing, hW, Nat.card_eq_fintype_card, Fintype.card_fin,
    ← Nat.cast_add] at h1
  change ringKrullDim (CrossingQuotient W t) + 1 ≤ _ at h1
  suffices h : ringKrullDim (CrossingQuotient W t) ≤ ((n + 1 : ℕ) : WithBot ℕ∞) by
    refine h.trans (le_of_eq ?_); push_cast; rfl
  generalize ringKrullDim (CrossingQuotient W t) = q at h1 ⊢
  induction q using WithBot.recBotCoe with
  | bot => exact bot_le
  | coe q =>
    induction q using ENat.recTopCoe with
    | top =>
      exfalso
      have e : (((⊤ : ℕ∞) : WithBot ℕ∞) + 1) = ((⊤ : ℕ∞) : WithBot ℕ∞) := by
        rw [← WithBot.coe_one, ← WithBot.coe_add, top_add]
      rw [e] at h1
      exact absurd (WithBot.coe_le_coe.mp h1) (not_le_of_gt (ENat.natCast_lt_top (n + 2)))
    | coe d =>
      rw [← WithBot.coe_one, ← WithBot.coe_add] at h1
      have h2 : ((d : ℕ∞) + 1) ≤ ((n + 2 : ℕ) : ℕ∞) := WithBot.coe_le_coe.mp h1
      have h3 : d + 1 ≤ n + 2 := by exact_mod_cast h2
      exact WithBot.coe_le_coe.mpr (by exact_mod_cast (show d ≤ n + 1 by omega))
