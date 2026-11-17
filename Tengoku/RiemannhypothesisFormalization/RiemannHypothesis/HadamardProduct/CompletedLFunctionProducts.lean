/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.CompletedLFunction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Products of completed-L Hadamard packages

This file proves that the reusable completed-L-function Hadamard interface is
closed under pointwise products.  The occurrence divisor of `F * G` is the
disjoint sum of the occurrence divisors of `F` and `G`; hence common zeros are
retained with the sum of their analytic multiplicities.

The construction is useful for genuine product L-functions and, in
particular, gives a second unconditional instance from the square of the
completed Riemann zeta function.  It does not assert a real-zero theorem for
either factor.
-/

open Filter Metric Real Set Topology

namespace OverflowResidueRH

universe u v

/-- Disjoint-union occurrence map for the divisor of a product.-/
def completedLProductZeroLoc
    {ι : Type u} {κ : Type v} (zeroLocF : ι → ℂ) (zeroLocG : κ → ℂ) :
    ι ⊕ κ → ℂ :=
  Sum.elim zeroLocF zeroLocG

/-- A fiber of the disjoint-union occurrence map is the sum of the two
factor fibers.-/
noncomputable def completedLProductZeroLocFiberEquiv
    {ι : Type u} {κ : Type v} (zeroLocF : ι → ℂ) (zeroLocG : κ → ℂ)
    (z : ℂ) :
    {x : ι ⊕ κ // completedLProductZeroLoc zeroLocF zeroLocG x = z} ≃
      {i : ι // zeroLocF i = z} ⊕ {j : κ // zeroLocG j = z} where
  toFun x := by
    rcases x with ⟨x, hx⟩
    rcases x with i | j
    · exact Sum.inl ⟨i, by simpa [completedLProductZeroLoc] using hx⟩
    · exact Sum.inr ⟨j, by simpa [completedLProductZeroLoc] using hx⟩
  invFun x := by
    rcases x with i | j
    · exact ⟨Sum.inl i.1, by simpa [completedLProductZeroLoc] using i.2⟩
    · exact ⟨Sum.inr j.1, by simpa [completedLProductZeroLoc] using j.2⟩
  left_inv x := by
    rcases x with ⟨i | j, hi⟩ <;> apply Subtype.ext <;> rfl
  right_inv x := by rcases x with i | j <;> rfl

/-- The norm-ball subtype of a disjoint-union divisor splits into the two
factor norm-ball subtypes.-/
noncomputable def completedLProductZeroLocNormBallEquiv
    {ι : Type u} {κ : Type v} (zeroLocF : ι → ℂ) (zeroLocG : κ → ℂ)
    (R : ℝ) :
    {x : ι ⊕ κ // ‖completedLProductZeroLoc zeroLocF zeroLocG x‖ ≤ R} ≃
      {i : ι // ‖zeroLocF i‖ ≤ R} ⊕ {j : κ // ‖zeroLocG j‖ ≤ R} where
  toFun x := by
    rcases x with ⟨x, hx⟩
    rcases x with i | j
    · exact Sum.inl ⟨i, by simpa [completedLProductZeroLoc] using hx⟩
    · exact Sum.inr ⟨j, by simpa [completedLProductZeroLoc] using hx⟩
  invFun x := by
    rcases x with i | j
    · exact ⟨Sum.inl i.1, by simpa [completedLProductZeroLoc] using i.2⟩
    · exact ⟨Sum.inr j.1, by simpa [completedLProductZeroLoc] using j.2⟩
  left_inv x := by
    rcases x with ⟨i | j, hi⟩ <;> apply Subtype.ext <;> rfl
  right_inv x := by rcases x with i | j <;> rfl

/-- Norm properness is closed under disjoint union.-/
theorem HadamardZeroNormProper.sum
    {ι : Type u} {κ : Type v} {zeroLocF : ι → ℂ} {zeroLocG : κ → ℂ}
    (HF : HadamardZeroNormProper zeroLocF)
    (HG : HadamardZeroNormProper zeroLocG) :
    HadamardZeroNormProper
      (completedLProductZeroLoc zeroLocF zeroLocG) where
  finite_norm_le R := by
    let e := completedLProductZeroLocNormBallEquiv zeroLocF zeroLocG R
    letI : Fintype {i : ι // ‖zeroLocF i‖ ≤ R} :=
      (HF.finite_norm_le R).fintype
    letI : Fintype {j : κ // ‖zeroLocG j‖ ≤ R} :=
      (HG.finite_norm_le R).fintype
    rw [Set.finite_def]
    exact ⟨Fintype.ofEquiv
      ({i : ι // ‖zeroLocF i‖ ≤ R} ⊕ {j : κ // ‖zeroLocG j‖ ≤ R})
      e.symm⟩

/-- The cumulative dyadic count of a disjoint-union divisor is the sum of
the two cumulative counts.-/
theorem hadamardZeroDyadicBallCard_completedLProductZeroLoc
    {ι : Type u} {κ : Type v} (zeroLocF : ι → ℂ) (zeroLocG : κ → ℂ)
    (HF : HadamardZeroNormProper zeroLocF)
    (HG : HadamardZeroNormProper zeroLocG) (n : ℕ) :
    hadamardZeroDyadicBallCard
        (completedLProductZeroLoc zeroLocF zeroLocG) n =
      hadamardZeroDyadicBallCard zeroLocF n +
        hadamardZeroDyadicBallCard zeroLocG n := by
  let R : ℝ := (2 : ℝ) ^ n
  let e := completedLProductZeroLocNormBallEquiv zeroLocF zeroLocG R
  letI : Finite {i : ι // ‖zeroLocF i‖ ≤ R} :=
    (HF.finite_norm_le R).to_subtype
  letI : Finite {j : κ // ‖zeroLocG j‖ ≤ R} :=
    (HG.finite_norm_le R).to_subtype
  unfold hadamardZeroDyadicBallCard
  change Nat.card
      {x : ι ⊕ κ //
        ‖completedLProductZeroLoc zeroLocF zeroLocG x‖ ≤ R} =
    Nat.card {i : ι // ‖zeroLocF i‖ ≤ R} +
      Nat.card {j : κ // ‖zeroLocG j‖ ≤ R}
  rw [Nat.card_congr e, Nat.card_sum]

/-- Cumulative dyadic `O(R log R)` divisor data is closed under disjoint
union, with the constants added and the thresholds maximized.-/
noncomputable def HadamardZeroDyadicCumulativeCountData.sum
    {ι : Type u} {κ : Type v} {zeroLocF : ι → ℂ} {zeroLocG : κ → ℂ}
    (HF : HadamardZeroDyadicCumulativeCountData zeroLocF)
    (HG : HadamardZeroDyadicCumulativeCountData zeroLocG) :
    HadamardZeroDyadicCumulativeCountData
      (completedLProductZeroLoc zeroLocF zeroLocG) where
  zero_ne x := by
    rcases x with i | j
    · simpa [completedLProductZeroLoc] using HF.zero_ne i
    · simpa [completedLProductZeroLoc] using HG.zero_ne j
  normProper := HF.normProper.sum HG.normProper
  lower := max HF.lower HG.lower
  C := HF.C + HG.C
  C₀ := HF.C₀ + HG.C₀
  C_nonneg := add_nonneg HF.C_nonneg HG.C_nonneg
  C₀_nonneg := add_nonneg HF.C₀_nonneg HG.C₀_nonneg
  count_le n hn := by
    have hnF : HF.lower ≤ n := le_trans (Nat.le_max_left _ _) hn
    have hnG : HG.lower ≤ n := le_trans (Nat.le_max_right _ _) hn
    have hF := HF.count_le n hnF
    have hG := HG.count_le n hnG
    have hsum :
        (hadamardZeroDyadicBallCard
            (completedLProductZeroLoc zeroLocF zeroLocG) n : ℝ) ≤
          (HF.C + HG.C) * ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ n +
            (HF.C₀ + HG.C₀) := by
      rw [hadamardZeroDyadicBallCard_completedLProductZeroLoc
        zeroLocF zeroLocG HF.normProper HG.normProper n, Nat.cast_add]
      calc
        (hadamardZeroDyadicBallCard zeroLocF n : ℝ) +
            hadamardZeroDyadicBallCard zeroLocG n
            ≤ (HF.C * ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ n + HF.C₀) +
                (HG.C * ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ n + HG.C₀) :=
          add_le_add hF hG
        _ = (HF.C + HG.C) * ((n + 1 : ℕ) : ℝ) * (2 : ℝ) ^ n +
            (HF.C₀ + HG.C₀) := by ring
    simpa [Nat.cast_add, Nat.cast_one] using hsum

/-- The regularized logarithmic-derivative series of a disjoint-union
divisor is the sum of the two factor series.-/
theorem hadamardRegularizedLogDerivSeries_completedLProductZeroLoc
    {ι : Type u} {κ : Type v} {zeroLocF : ι → ℂ} {zeroLocG : κ → ℂ}
    (HF : HadamardZeroInvSqSummability zeroLocF)
    (HG : HadamardZeroInvSqSummability zeroLocG)
    (z : ℂ) (hzF : ∀ i : ι, z ≠ zeroLocF i)
    (hzG : ∀ j : κ, z ≠ zeroLocG j) :
    hadamardRegularizedLogDerivSeries
        (completedLProductZeroLoc zeroLocF zeroLocG) z =
      hadamardRegularizedLogDerivSeries zeroLocF z +
        hadamardRegularizedLogDerivSeries zeroLocG z := by
  let termF : ι → ℂ := fun i ↦
    1 / (z - zeroLocF i) + 1 / zeroLocF i
  let termG : κ → ℂ := fun j ↦
    1 / (z - zeroLocG j) + 1 / zeroLocG j
  let termSum : ι ⊕ κ → ℂ := Sum.elim termF termG
  have hF : Summable termF := by
    simpa only [termF] using HF.summable_regularized hzF
  have hG : Summable termG := by
    simpa only [termG] using HG.summable_regularized hzG
  have hsum : HasSum termSum ((∑' i, termF i) + ∑' j, termG j) :=
    hF.hasSum.sum hG.hasSum
  have heq :
      (fun x : ι ⊕ κ ↦
        1 / (z - completedLProductZeroLoc zeroLocF zeroLocG x) +
          1 / completedLProductZeroLoc zeroLocF zeroLocG x) = termSum := by
    funext x
    rcases x with i | j <;> rfl
  unfold hadamardRegularizedLogDerivSeries
  rw [heq]
  simpa only [termF, termG] using hsum.tsum_eq

/-- A point avoiding the occurrence divisor and the origin is nonzero for
the completed L-function.-/
theorem CompletedLFunctionHadamardData.ne_zero_of_ne_zeroLoc
    {F : ℂ → ℂ} {ι : Type u} (H : CompletedLFunctionHadamardData F ι)
    {z : ℂ} (hz0 : z ≠ 0) (hzloc : ∀ i : ι, z ≠ H.zeroLoc i) :
    F z ≠ 0 := by
  have hzorder : analyticOrderAt F z = 0 := by
    rw [H.analyticOrderAt_eq z, ite_eq_right hz0]
    letI : IsEmpty {i : ι // H.zeroLoc i = z} :=
      ⟨fun i ↦ hzloc i.1 i.2.symm⟩
    rw [Nat.card_of_isEmpty]
    simp
  exact (H.analytic z (Set.mem_univ z)).analyticOrderAt_eq_zero.mp hzorder

end OverflowResidueRH
