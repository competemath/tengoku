import Tengoku.PaperCLean.PaperCV282.SteinTestTotalVariation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Explicit scalar Stein-factor interface

The target mass is Mathlib's actual Poisson probability measure. The sole
literature premise below is existence of test-set Stein solutions with
their standard two norm bounds. It does not assume a dependency-graph
bound or any arithmetic conclusion from Paper C.

Primary source: K. Krokowski, arXiv:1505.01417v3, Section 2.5, (2.14)-(2.15),
https://arxiv.org/pdf/1505.01417 . The zeroth factor used here is the weaker
min(1,lambda^(-1/2)); sqrt(2/e) is at most one. No Lean axiom is introduced.
The positive-rate input is an explicit argument at every application.
-/

namespace PaperC.V282.ScalarSteinInput

open ProbabilityTheory
open scoped BigOperators NNReal

noncomputable section

local instance instDecidableProposition (P : Prop) : Decidable P := Classical.propDecidable P

/-- The real singleton mass of the actual Poisson measure.-/
def poissonMass (rate : ℝ≥0) (k : ℕ) : ℝ := (poissonMeasure rate).real {k}

/--
@isnad1 id=eq.0h2v.s5.543146cb7ec2 from=translated src=- shape=a7cf24b9 vocab=e30a7316
-/
theorem poissonMass_formula (rate : ℝ≥0) (k : ℕ) :
    poissonMass rate k = Real.exp (-(rate : ℝ)) * (rate : ℝ) ^ k / (k.factorial : ℝ) :=
  poissonMeasure_real_singleton rate k

/--
@isnad1 id=le.0h2v.s4.672105cb37eb from=translated src=- shape=0d4521f5 vocab=6114be6f
-/
theorem poissonMass_nonneg (rate : ℝ≥0) (k : ℕ) : 0 ≤ poissonMass rate k := by
  rw [poissonMass_formula]
  positivity

/--
@isnad1 id=hassum.0h1v.s4.c3775d206514 from=translated src=- shape=a98592d8 vocab=8a4eecc1
-/
theorem hasSum_poissonMass (rate : ℝ≥0) : HasSum (poissonMass rate) 1 := by
  change HasSum (fun k => poissonMass rate k) 1
  simp_rw [poissonMass_formula]
  exact hasSum_one_poissonMeasure rate

/--
@isnad1 id=eq.0h1v.s5.32d6f05a6e8a from=translated src=- shape=d6bdd762 vocab=a1b15143
-/
theorem poissonMass_zero (k : ℕ) : poissonMass 0 k = if k = 0 then 1 else 0 := by
  cases k <;> simp [poissonMass_formula]

/-- Probability of an arbitrary natural-valued test set under the target law.-/
def poissonSetMass (rate : ℝ≥0) (A : Set ℕ) : ℝ :=
  ∑' k, if k ∈ A then poissonMass rate k else 0

/--
@isnad1 id=eq.0h1v.s5.9a2d18f37d7f from=translated src=- shape=540969d3 vocab=e045bd4f
-/
theorem poissonSetMass_zero (A : Set ℕ) : poissonSetMass 0 A = if 0 ∈ A then 1 else 0 := by
  unfold poissonSetMass
  simp_rw [poissonMass_zero]
  have heq (k : ℕ) : (if k ∈ A then (if k = 0 then (1 : ℝ) else 0) else 0) =
      if k = 0 then (if 0 ∈ A then 1 else 0) else 0 := by
    by_cases hk : k = 0 <;> simp [hk]
  simp_rw [heq]
  simp

/-- First-difference factor, with the manuscript convention at zero intensity.-/
def firstSteinFactor (rate : ℝ≥0) : ℝ :=
  if rate = 0 then 1 else min 1 (rate : ℝ)⁻¹

/-- Zeroth-order factor, with the manuscript convention at zero intensity.-/
def zeroSteinFactor (rate : ℝ≥0) : ℝ :=
  if rate = 0 then 1 else min 1 (Real.sqrt (rate : ℝ))⁻¹

/--
@isnad1 id=le.0h1v.s3.f7ab85f58d50 from=translated src=- shape=b9369acb vocab=a9ff0ffc
-/
theorem firstSteinFactor_nonneg (rate : ℝ≥0) : 0 ≤ firstSteinFactor rate := by
  unfold firstSteinFactor
  split_ifs <;> positivity

/--
@isnad1 id=le.0h1v.s3.e9e68ddffa5a from=translated src=- shape=a311c14d vocab=a9ff0ffc
-/
theorem firstSteinFactor_le_one (rate : ℝ≥0) : firstSteinFactor rate ≤ 1 := by
  unfold firstSteinFactor
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/--
@isnad1 id=le.0h1v.s3.b372ebfd566a from=translated src=- shape=b9369acb vocab=a29921f7
-/
theorem zeroSteinFactor_nonneg (rate : ℝ≥0) : 0 ≤ zeroSteinFactor rate := by
  unfold zeroSteinFactor
  split_ifs <;> positivity

/--
@isnad1 id=le.0h1v.s3.4d4104872b0c from=translated src=- shape=a311c14d vocab=a29921f7
-/
theorem zeroSteinFactor_le_one (rate : ℝ≥0) : zeroSteinFactor rate ≤ 1 := by
  unfold zeroSteinFactor
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- The Stein equation and the two norm bounds, uniform in the test set.-/
def SteinSolutionBounds (rate : ℝ≥0) (c d : ℝ) : Prop :=
  ∀ A : Set ℕ, ∃ f : ℕ → ℝ,
    (∀ k : ℕ, (rate : ℝ) * f (k + 1) - (k : ℝ) * f k =
      (if k ∈ A then 1 else 0) - poissonSetMass rate A) ∧
    (∀ k : ℕ, |f k| ≤ c) ∧ (∀ k : ℕ, |f (k + 1) - f k| ≤ d)

/-- Published scalar solution bounds, recorded as an explicit positive-rate premise.-/
def ScalarSteinFactorsStatement : Prop :=
  ∀ rate : ℝ≥0, 0 < rate →
    SteinSolutionBounds rate (zeroSteinFactor rate) (firstSteinFactor rate)

/-- The zero-rate equation has an elementary bounded solution.
@isnad1 id=steinsol.0h0v.s4.9f2eea7a632b from=translated src=- shape=12666b46 vocab=df374c0f
-/
theorem steinSolutionBounds_zero : SteinSolutionBounds 0 1 1 := by
  intro A
  let f : ℕ → ℝ := fun k =>
    ((if 0 ∈ A then (1 : ℝ) else 0) - (if k ∈ A then 1 else 0)) / k
  have hrange (k : ℕ) :
      if 0 ∈ A then (0 ≤ f k ∧ f k ≤ 1) else (-1 ≤ f k ∧ f k ≤ 0) := by
    by_cases hk : k = 0
    · subst k
      simp [f]
    · have hkpos : (0 : ℝ) < k := by exact_mod_cast (Nat.pos_of_ne_zero hk)
      have hkone : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hk)
      have hdiv : (1 : ℝ) / k ≤ 1 := (div_le_one hkpos).mpr hkone
      by_cases hA : 0 ∈ A <;> by_cases hkA : k ∈ A <;>
        simp [f, hA, hkA, neg_div] <;> simpa only [one_div] using hdiv
  refine ⟨f, ?_, ?_, ?_⟩
  · intro k
    rw [poissonSetMass_zero]
    by_cases hk : k = 0
    · subst k
      simp
    · have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
      dsimp [f]
      push_cast
      field_simp
      ring
  · intro k
    have h := hrange k
    by_cases hA : 0 ∈ A <;> simp only [hA, ite_true, ite_false] at h <;>
      exact abs_le.mpr ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro k
    have h := hrange k
    have hnext := hrange (k + 1)
    by_cases hA : 0 ∈ A <;> simp only [hA, ite_true, ite_false] at h hnext <;>
      exact abs_le.mpr ⟨by linarith [h.1, hnext.2], by linarith [h.2, hnext.1]⟩

/-- The explicit literature input is needed only at positive rate; zero is proved internally.
@isnad1 id=steinsol.1h1v.s3.082855d4ea8c from=translated src=- shape=fd9a14d9 vocab=70423f07
-/
theorem steinSolutionBounds_all (hStein : ScalarSteinFactorsStatement) (rate : ℝ≥0) :
    SteinSolutionBounds rate (zeroSteinFactor rate) (firstSteinFactor rate) := by
  by_cases h : rate = 0
  · subst rate
    simpa [zeroSteinFactor, firstSteinFactor] using steinSolutionBounds_zero
  · exact hStein rate (lt_of_le_of_ne (show 0 ≤ rate from rate.2) (Ne.symm h))

end
end PaperC.V282.ScalarSteinInput
