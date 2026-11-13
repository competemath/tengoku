import Tengoku.Seed.Analysis.CStarAlgebra.Basic
import Tengoku.Seed.Analysis.Normed.Ring.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Norms of positive integer powers of self-adjoint elements

The native dyadic-power norm identity and submultiplicativity imply the
exact identity at every positive integer. Requiring positive degree retains
trivial normed rings, where the degree-zero formula would fail.
-/

noncomputable section
set_option autoImplicit false

variable {A : Type*} [NormedRing A] [StarRing A] [CStarRing A]

/-- Every positive integer power of a self-adjoint element has its exact
power norm, without a nontrivial-ring assumption.
@isnad1 id=eq.2h3v.s6.94e0254935a0 from=translated src=- shape=784ecf19 vocab=c0dbe6ab
-/
theorem IsSelfAdjoint.norm_pow_of_pos {a : A} (ha : IsSelfAdjoint a) {n : ℕ}
    (hn : 0 < n) : ‖a ^ n‖ = ‖a‖ ^ n := by
  by_cases hzero : a = 0
  · subst a
    simp [zero_pow hn.ne']
  have hpos : 0 < ‖a‖ := norm_pos_iff.mpr hzero
  have hN : n < 2 ^ n := n.lt_two_pow_self
  have hdiff : 0 < 2 ^ n - n := Nat.sub_pos_of_lt hN
  have hpow : ‖a‖ ^ (2 ^ n) = ‖a‖ ^ n * ‖a‖ ^ (2 ^ n - n) := by
    rw [← pow_add, Nat.add_sub_of_le hN.le]
  have hle : ‖a‖ ^ (2 ^ n) ≤ ‖a ^ n‖ * ‖a‖ ^ (2 ^ n - n) := by
    calc
      _ = ‖a ^ (2 ^ n)‖ := (ha.norm_pow_two_pow n).symm
      _ = ‖a ^ n * a ^ (2 ^ n - n)‖ := by rw [← pow_add, Nat.add_sub_of_le hN.le]
      _ ≤ ‖a ^ n‖ * ‖a ^ (2 ^ n - n)‖ := norm_mul_le _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left (norm_pow_le' a hdiff) (norm_nonneg _)
  rw [hpow] at hle
  exact le_antisymm (norm_pow_le' a hn)
    (le_of_mul_le_mul_right hle (pow_pos hpos _))
