import Tengoku.Rankamplificationtotient.RankAmplification.PrimeRankinFull
import Tengoku.Rankamplificationtotient.RankAmplification.LargeCofactor
import Tengoku.Rankamplificationtotient.RankAmplification.SquareSources
import Tengoku.Rankamplificationtotient.RankAmplification.Saddle

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Assembly of the Section 5 smooth-multiplier estimate This file formalizes the finite sum in Proposition 5.1, its split at `p = y^2`, the unconditional large-`p` estimate, and the exact saddle substitutions. -/

namespace RankAmplification

open Finset
open scoped BigOperators Nat.Prime

noncomputable section

/-! ## The exact finite `B₄` sum -/

/-- The numerator `2xy` in the divisor-weighted transfer sum.-/
def section5Ambient (x y : ℕ) : ℕ := 2 * x * y

/-- The prime interval `y < p ≤ √(2xy)` from Proposition 5.1.-/
def section5PrimeRange (x y : ℕ) : Finset ℕ :=
  squareSourcePrimeRange y (section5Ambient x y).sqrt

/-- The intermediate range `y < p ≤ y²`.-/
def section5IntermediatePrimeRange (x y : ℕ) : Finset ℕ :=
  (section5PrimeRange x y).filter fun p ↦ p ≤ y ^ 2

/-- The range above the square cutoff, `y² < p ≤ √(2xy)`.-/
def section5UpperPrimeRange (x y : ℕ) : Finset ℕ :=
  (section5PrimeRange x y).filter fun p ↦ y ^ 2 < p

/-- The local divisor-weighted cutoff `X_p = ⌊2xy/p²⌋`.-/
def section5LocalCutoff (x y p : ℕ) : ℕ := section5Ambient x y / p ^ 2

/-- The exact finite smooth-multiplier `B₄` sum in (5.2).-/
def smoothMultiplierB4Sum (x y : ℕ) : ℝ :=
  ∑ p ∈ section5PrimeRange x y,
    finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p)

/-- Portion of the `B₄` sum over `y < p ≤ y²`.-/
def smoothMultiplierB4Intermediate (x y : ℕ) : ℝ :=
  ∑ p ∈ section5IntermediatePrimeRange x y,
    finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p)

/-- Portion of the `B₄` sum over primes above `y²`.-/
def smoothMultiplierB4Upper (x y : ℕ) : ℝ :=
  ∑ p ∈ section5UpperPrimeRange x y,
    finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p)

@[simp]
theorem mem_section5PrimeRange {x y p : ℕ} :
    p ∈ section5PrimeRange x y ↔
      y < p ∧ p ≤ (section5Ambient x y).sqrt ∧ p.Prime := by
  simp [section5PrimeRange, squareSourcePrimeRange, and_assoc]

@[simp]
theorem mem_section5IntermediatePrimeRange {x y p : ℕ} :
    p ∈ section5IntermediatePrimeRange x y ↔
      p ∈ section5PrimeRange x y ∧ p ≤ y ^ 2 := by
  simp [section5IntermediatePrimeRange]

@[simp]
theorem mem_section5UpperPrimeRange {x y p : ℕ} :
    p ∈ section5UpperPrimeRange x y ↔
      p ∈ section5PrimeRange x y ∧ y ^ 2 < p := by
  simp [section5UpperPrimeRange]

/-- Exact decomposition at `p = y²`.-/
theorem smoothMultiplierB4Sum_eq_intermediate_add_upper (x y : ℕ) :
    smoothMultiplierB4Sum x y =
      smoothMultiplierB4Intermediate x y + smoothMultiplierB4Upper x y := by
  simpa only [smoothMultiplierB4Sum, smoothMultiplierB4Intermediate,
    smoothMultiplierB4Upper, section5IntermediatePrimeRange,
    section5UpperPrimeRange, not_le] using
      (Finset.sum_filter_add_sum_filter_not (section5PrimeRange x y)
        (fun p ↦ p ≤ y ^ 2)
        (fun p ↦ finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p))).symm

/-- The smooth divisor census is bounded by the elementary divisor hyperbola estimate.-/
theorem finiteDivisorWeightedSmoothCount_le_hyperbola (R X : ℕ) :
    finiteDivisorWeightedSmoothCount R X ≤ (X : ℝ) * (1 + Real.log X) := by
  classical
  calc
    finiteDivisorWeightedSmoothCount R X = ((smoothFactorPairSet R X).card : ℝ) :=
      (card_smoothFactorPairSet_cast_eq R X).symm
    _ ≤ ((cofactorPairSet X).card : ℝ) := by
      exact_mod_cast Finset.card_filter_le (cofactorPairSet X) fun k : ℕ × ℕ ↦
        IsSmooth R (k.1 * k.2)
    _ ≤ (X : ℝ) * (1 + Real.log X) := card_cofactorPairSet_cast_le X

/-- The `B₄` sum is exactly the cardinality branch in the summed large-cofactor majorant.-/
theorem sum_smoothProviderPairMajorant_eq_reciprocal_add_B4 (x y : ℕ) :
    (∑ p ∈ section5PrimeRange x y,
      smoothProviderPairMajorant x p (section5LocalCutoff x y p)) =
      (x : ℝ) * ∑ p ∈ section5PrimeRange x y,
        smoothProviderPairReciprocalSum p (section5LocalCutoff x y p) +
      smoothMultiplierB4Sum x y := by
  simp_rw [smoothProviderPairMajorant_eq]
  rw [Finset.sum_add_distrib, Finset.mul_sum]
  rfl

/-! ## The intermediate Rankin range -/

/-- The exact finite input required on the intermediate range in Proposition 5.1.-/
def HasSection5IntermediateRankinSaving (x y : ℕ) (saving : ℝ) : Prop :=
  ∀ p ∈ section5IntermediatePrimeRange x y,
    0 < section5LocalCutoff x y p ∧
      1 < rankinU (section5LocalCutoff x y p) p ∧
      rankinU (section5LocalCutoff x y p) p ≤ Real.sqrt p ∧
      fullPaperDivisorError p (section5LocalCutoff x y p) ≤
        rankinU (section5LocalCutoff x y p) p *
          Real.log (rankinU (section5LocalCutoff x y p) p) / 2 ∧
      saving ≤ rankinU (section5LocalCutoff x y p) p *
        Real.log (rankinU (section5LocalCutoff x y p) p) / 2

/-- Pointwise consequence of the intermediate-range Rankin input.-/
theorem finiteDivisorWeightedSmoothCount_section5Intermediate_le
    {x y p : ℕ} {saving : ℝ}
    (hinput : HasSection5IntermediateRankinSaving x y saving)
    (hp : p ∈ section5IntermediatePrimeRange x y) :
    finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p) ≤
      (section5LocalCutoff x y p : ℝ) * Real.exp (-saving) := by
  rcases hinput p hp with ⟨hX, hu, huSqrt, herror, hsaving⟩
  have hpPrime : p.Prime := (mem_section5PrimeRange.mp
    (mem_section5IntermediatePrimeRange.mp hp).1).2.2
  calc
    finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p) ≤
        (section5LocalCutoff x y p : ℝ) * Real.exp
          (-(rankinU (section5LocalCutoff x y p) p *
            Real.log (rankinU (section5LocalCutoff x y p) p)) / 2) :=
      finiteDivisorWeightedSmoothCount_le_full_half_u_log_u
        hX hpPrime.two_le hu huSqrt herror
    _ ≤ (section5LocalCutoff x y p : ℝ) * Real.exp (-saving) := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply Real.exp_le_exp.mpr
      linarith

/-- Casting the local floor can only increase it to the corresponding real quotient.-/
theorem section5LocalCutoff_cast_le (x y p : ℕ) :
    (section5LocalCutoff x y p : ℝ) ≤
      (section5Ambient x y : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
  calc
    (section5LocalCutoff x y p : ℝ) ≤
        (section5Ambient x y : ℝ) / (p ^ 2 : ℕ) := by
      exact Nat.cast_div_le
    _ = (section5Ambient x y : ℝ) * ((p : ℝ) ^ 2)⁻¹ := by
      norm_num [div_eq_mul_inv]

/-- The lower endpoint is below the square-root endpoint whenever `y ≤ x`.-/
theorem section5_y_le_sqrt_ambient {x y : ℕ} (hxy : y ≤ x) :
    y ≤ (section5Ambient x y).sqrt := by
  apply Nat.le_sqrt'.2
  calc
    y ^ 2 = y * y := pow_two y
    _ ≤ x * y := Nat.mul_le_mul_right y hxy
    _ ≤ 2 * (x * y) := Nat.le_mul_of_pos_left _ (by omega)
    _ = section5Ambient x y := by simp [section5Ambient, mul_assoc]

/-- The reciprocal-square mass of the intermediate range has the elementary `1/y` bound.-/
theorem sum_section5IntermediatePrimeRange_inv_sq_le {x y : ℕ}
    (hy : 0 < y) (hxy : y ≤ x) :
    (∑ p ∈ section5IntermediatePrimeRange x y, (((p : ℝ) ^ 2)⁻¹)) ≤
      (y : ℝ)⁻¹ := by
  calc
    (∑ p ∈ section5IntermediatePrimeRange x y, (((p : ℝ) ^ 2)⁻¹)) ≤
        ∑ p ∈ section5PrimeRange x y, (((p : ℝ) ^ 2)⁻¹) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        exact (mem_section5IntermediatePrimeRange.mp hp).1
      · intro p _ _
        positivity
    _ ≤ (y : ℝ)⁻¹ :=
      sum_squareSourcePrimeRange_inv_sq_le_inv hy (section5_y_le_sqrt_ambient hxy)

/-- Uniform intermediate-range contribution after the full Rankin estimate.-/
theorem smoothMultiplierB4Intermediate_le {x y : ℕ} {saving : ℝ}
    (hy : 0 < y) (hxy : y ≤ x)
    (hinput : HasSection5IntermediateRankinSaving x y saving) :
    smoothMultiplierB4Intermediate x y ≤ 2 * (x : ℝ) * Real.exp (-saving) := by
  calc
    smoothMultiplierB4Intermediate x y ≤
        ∑ p ∈ section5IntermediatePrimeRange x y,
          ((section5Ambient x y : ℝ) * Real.exp (-saving)) *
            ((p : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p hp
      calc
        finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p) ≤
            (section5LocalCutoff x y p : ℝ) * Real.exp (-saving) :=
          finiteDivisorWeightedSmoothCount_section5Intermediate_le hinput hp
        _ ≤ ((section5Ambient x y : ℝ) * ((p : ℝ) ^ 2)⁻¹) *
            Real.exp (-saving) :=
          mul_le_mul_of_nonneg_right (section5LocalCutoff_cast_le x y p)
            (Real.exp_pos _).le
        _ = ((section5Ambient x y : ℝ) * Real.exp (-saving)) *
            ((p : ℝ) ^ 2)⁻¹ := by ring
    _ = ((section5Ambient x y : ℝ) * Real.exp (-saving)) *
        ∑ p ∈ section5IntermediatePrimeRange x y, (((p : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ ((section5Ambient x y : ℝ) * Real.exp (-saving)) * (y : ℝ)⁻¹ := by
      apply mul_le_mul_of_nonneg_left
        (sum_section5IntermediatePrimeRange_inv_sq_le hy hxy)
      positivity
    _ = 2 * (x : ℝ) * Real.exp (-saving) := by
      have hyReal : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
      simp only [section5Ambient, Nat.cast_mul, Nat.cast_ofNat]
      field_simp

/-! ## The unconditional range above `y²` -/

/-- A local hyperbola bound with its floor replaced by the real quotient.-/
theorem finiteDivisorWeightedSmoothCount_section5LocalCutoff_le
    {x y p : ℕ} (hambient : 0 < section5Ambient x y) :
    finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p) ≤
      (section5Ambient x y : ℝ) * (1 + Real.log (section5Ambient x y)) *
        ((p : ℝ) ^ 2)⁻¹ := by
  have hambientOne : (1 : ℝ) ≤ section5Ambient x y := by
    exact_mod_cast hambient
  have hfactor : 0 ≤ 1 + Real.log (section5Ambient x y) := by
    have := Real.log_nonneg hambientOne
    linarith
  by_cases hcutoff : section5LocalCutoff x y p = 0
  · calc
      finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p) ≤
          (section5LocalCutoff x y p : ℝ) *
            (1 + Real.log (section5LocalCutoff x y p)) :=
        finiteDivisorWeightedSmoothCount_le_hyperbola p (section5LocalCutoff x y p)
      _ = 0 := by simp [hcutoff]
      _ ≤ (section5Ambient x y : ℝ) * (1 + Real.log (section5Ambient x y)) *
          ((p : ℝ) ^ 2)⁻¹ := by positivity
  · have hcutoffPos : 0 < section5LocalCutoff x y p := Nat.pos_of_ne_zero hcutoff
    have hcutoffLe : section5LocalCutoff x y p ≤ section5Ambient x y :=
      (Nat.div_le_self _ _)
    have hlogLe : Real.log (section5LocalCutoff x y p) ≤
        Real.log (section5Ambient x y) := by
      apply Real.log_le_log
      · exact_mod_cast hcutoffPos
      · exact_mod_cast hcutoffLe
    calc
      finiteDivisorWeightedSmoothCount p (section5LocalCutoff x y p) ≤
          (section5LocalCutoff x y p : ℝ) *
            (1 + Real.log (section5LocalCutoff x y p)) :=
        finiteDivisorWeightedSmoothCount_le_hyperbola p (section5LocalCutoff x y p)
      _ ≤ (section5LocalCutoff x y p : ℝ) *
          (1 + Real.log (section5Ambient x y)) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        linarith
      _ ≤ ((section5Ambient x y : ℝ) * ((p : ℝ) ^ 2)⁻¹) *
          (1 + Real.log (section5Ambient x y)) :=
        mul_le_mul_of_nonneg_right (section5LocalCutoff_cast_le x y p) hfactor
      _ = (section5Ambient x y : ℝ) * (1 + Real.log (section5Ambient x y)) *
          ((p : ℝ) ^ 2)⁻¹ := by ring

/-- Reciprocal-square mass above the split point `y²`.-/
theorem sum_section5UpperPrimeRange_inv_sq_le {x y : ℕ} (hy : 0 < y) :
    (∑ p ∈ section5UpperPrimeRange x y, (((p : ℝ) ^ 2)⁻¹)) ≤
      ((y : ℝ) ^ 2)⁻¹ := by
  by_cases hyP : y ^ 2 ≤ (section5Ambient x y).sqrt
  · calc
      (∑ p ∈ section5UpperPrimeRange x y, (((p : ℝ) ^ 2)⁻¹)) ≤
          ∑ p ∈ squareSourcePrimeRange (y ^ 2) (section5Ambient x y).sqrt,
            (((p : ℝ) ^ 2)⁻¹) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro p hp
          have hpData := mem_section5PrimeRange.mp
            (mem_section5UpperPrimeRange.mp hp).1
          have hpUpper := (mem_section5UpperPrimeRange.mp hp).2
          exact (Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨hpUpper, hpData.2.1⟩,
            hpData.2.2⟩)
        · intro p _ _
          positivity
      _ ≤ ((y ^ 2 : ℕ) : ℝ)⁻¹ :=
        sum_squareSourcePrimeRange_inv_sq_le_inv (pow_pos hy 2) hyP
      _ = ((y : ℝ) ^ 2)⁻¹ := by norm_num
  · have hempty : section5UpperPrimeRange x y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro p hp
      have hpData := mem_section5PrimeRange.mp
        (mem_section5UpperPrimeRange.mp hp).1
      have hpUpper := (mem_section5UpperPrimeRange.mp hp).2
      omega
    rw [hempty]
    simp

/-- The `p > y²` portion of Proposition 5.1, with explicit constants.-/
theorem smoothMultiplierB4Upper_le {x y : ℕ}
    (hy : 0 < y) (hxy : y ≤ x) :
    smoothMultiplierB4Upper x y ≤
      2 * (x : ℝ) * (1 + Real.log (section5Ambient x y)) * (y : ℝ)⁻¹ := by
  have hx : 0 < x := hy.trans_le hxy
  have hambient : 0 < section5Ambient x y := by
    simp only [section5Ambient]
    positivity
  have hambientOne : (1 : ℝ) ≤ section5Ambient x y := by
    exact_mod_cast hambient
  have hfactor : 0 ≤
      (section5Ambient x y : ℝ) * (1 + Real.log (section5Ambient x y)) := by
    have hlog : 0 ≤ Real.log (section5Ambient x y) := Real.log_nonneg hambientOne
    positivity
  calc
    smoothMultiplierB4Upper x y ≤
        ∑ p ∈ section5UpperPrimeRange x y,
          ((section5Ambient x y : ℝ) * (1 + Real.log (section5Ambient x y))) *
            ((p : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro p _
      exact finiteDivisorWeightedSmoothCount_section5LocalCutoff_le hambient
    _ = ((section5Ambient x y : ℝ) * (1 + Real.log (section5Ambient x y))) *
        ∑ p ∈ section5UpperPrimeRange x y, (((p : ℝ) ^ 2)⁻¹) := by
      rw [Finset.mul_sum]
    _ ≤ ((section5Ambient x y : ℝ) * (1 + Real.log (section5Ambient x y))) *
        ((y : ℝ) ^ 2)⁻¹ := by
      exact mul_le_mul_of_nonneg_left (sum_section5UpperPrimeRange_inv_sq_le hy) hfactor
    _ = 2 * (x : ℝ) * (1 + Real.log (section5Ambient x y)) * (y : ℝ)⁻¹ := by
      have hyReal : (y : ℝ) ≠ 0 := by exact_mod_cast hy.ne'
      simp only [section5Ambient, Nat.cast_mul, Nat.cast_ofNat]
      field_simp

/-! ## Finite and uniform forms of Proposition 5.1 -/

/-- The completely explicit two-range estimate before absorbing the elementary upper tail.-/
theorem smoothMultiplierB4Sum_le_exp_add_upper {x y : ℕ} {saving : ℝ}
    (hy : 0 < y) (hxy : y ≤ x)
    (hinput : HasSection5IntermediateRankinSaving x y saving) :
    smoothMultiplierB4Sum x y ≤
      2 * (x : ℝ) * Real.exp (-saving) +
        2 * (x : ℝ) * (1 + Real.log (section5Ambient x y)) * (y : ℝ)⁻¹ := by
  rw [smoothMultiplierB4Sum_eq_intermediate_add_upper]
  exact add_le_add (smoothMultiplierB4Intermediate_le hy hxy hinput)
    (smoothMultiplierB4Upper_le hy hxy)

/-- Exact numerical absorption needed to turn the two explicit pieces into `x exp (-T + error)`.-/
def HasSection5B4Absorption (x y : ℕ) (T saving error : ℝ) : Prop :=
  2 * Real.exp (-saving) +
      2 * (1 + Real.log (section5Ambient x y)) * (y : ℝ)⁻¹ ≤
    Real.exp (-T + error)

/-- Finite Proposition 5.1 under its two explicitly named analytic inputs.-/
theorem proposition5_1_finite {x y : ℕ} {T saving error : ℝ}
    (hy : 0 < y) (hxy : y ≤ x)
    (hRankin : HasSection5IntermediateRankinSaving x y saving)
    (hAbsorb : HasSection5B4Absorption x y T saving error) :
    smoothMultiplierB4Sum x y ≤ (x : ℝ) * Real.exp (-T + error) := by
  calc
    smoothMultiplierB4Sum x y ≤
        2 * (x : ℝ) * Real.exp (-saving) +
          2 * (x : ℝ) * (1 + Real.log (section5Ambient x y)) * (y : ℝ)⁻¹ :=
      smoothMultiplierB4Sum_le_exp_add_upper hy hxy hRankin
    _ = (x : ℝ) *
        (2 * Real.exp (-saving) +
          2 * (1 + Real.log (section5Ambient x y)) * (y : ℝ)⁻¹) := by ring
    _ ≤ (x : ℝ) * Real.exp (-T + error) :=
      mul_le_mul_of_nonneg_left hAbsorb (Nat.cast_nonneg x)

/-- The fixed multiplicative window `c₀G ≤ T ≤ C₀G`.-/
def IsSection5SaddleWindow (c₀ C₀ X T : ℝ) : Prop :=
  c₀ * scaleG X ≤ T ∧ T ≤ C₀ * scaleG X

/-- A natural cutoff representing `y = exp T` up to flooring.-/
def IsSection5ExponentialCutoff (y : ℕ) (T : ℝ) : Prop :=
  (y : ℝ) ≤ Real.exp T ∧ Real.exp T < y + 1

/-- The missing moving-uniformity proposition in a form exactly sufficient for Proposition 5.1.-/
@[nolint defsWithUnderscore]
def HasProposition5_1Uniformity (c₀ C₀ : ℝ) (error : ℕ → ℝ → ℝ) : Prop :=
  ∀ x y T,
    0 < y → y ≤ x →
      IsSection5ExponentialCutoff y T →
      IsSection5SaddleWindow c₀ C₀ x T →
      ∃ saving,
        HasSection5IntermediateRankinSaving x y saving ∧
          HasSection5B4Absorption x y T saving (error x T)

/-- Uniform Proposition 5.1, reduced to the single named moving-uniformity proposition above.-/
theorem proposition5_1_uniform {c₀ C₀ : ℝ} {error : ℕ → ℝ → ℝ}
    (huniform : HasProposition5_1Uniformity c₀ C₀ error) :
    ∀ x y T,
      0 < y → y ≤ x →
        IsSection5ExponentialCutoff y T →
        IsSection5SaddleWindow c₀ C₀ x T →
        smoothMultiplierB4Sum x y ≤ (x : ℝ) * Real.exp (-T + error x T) := by
  intro x y T hy hxy hcutoff hwindow
  obtain ⟨saving, hRankin, hAbsorb⟩ :=
    huniform x y T hy hxy hcutoff hwindow
  exact proposition5_1_finite hy hxy hRankin hAbsorb

/-- Uniform `o(V)` written directly in epsilon form over the Section 5 saddle window.-/
def IsSection5UniformLittleOScaleV (c₀ C₀ : ℝ) (error : ℕ → ℝ → ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε →
    ∀ᶠ x : ℕ in Filter.atTop,
      ∀ T : ℝ, IsSection5SaddleWindow c₀ C₀ x T →
        |error x T| ≤ ε * scaleV x

/-! ## Exact Section 5 saddle substitutions -/

/-- The two competing exponents `T` and `G²/T` from Sections 5--7.-/
def section5SaddleExponent (X T : ℝ) : ℝ :=
  min T (scaleG X ^ 2 / T)

/-- Replacing `G²` by its defining product `LA`.-/
theorem section5SaddleExponent_eq_min_LA {X T : ℝ}
    (hL : 0 ≤ scaleL X) (hA : 0 ≤ scaleA X) :
    section5SaddleExponent X T = min T (scaleL X * scaleA X / T) := by
  rw [section5SaddleExponent, scaleG_sq hL hA]

/-- Exact balance at `T = G`.-/
@[simp, nolint simpNF]
theorem section5SaddleExponent_at_scaleG {X : ℝ} (hG : scaleG X ≠ 0) :
    section5SaddleExponent X (scaleG X) = scaleG X := by
  unfold section5SaddleExponent
  have hquotient : scaleG X ^ 2 / scaleG X = scaleG X := by
    field_simp
  rw [hquotient, min_self]

/-- The balanced choice is globally optimal among positive cutoffs.-/
theorem section5SaddleExponent_le_scaleG {X T : ℝ}
    (hG : 0 ≤ scaleG X) (hT : 0 < T) :
    section5SaddleExponent X T ≤ scaleG X := by
  unfold section5SaddleExponent
  by_cases hTG : T ≤ scaleG X
  · exact (min_le_left _ _).trans hTG
  · have hGT : scaleG X ≤ T := le_of_not_ge hTG
    have hquotient : scaleG X ^ 2 / T ≤ scaleG X := by
      apply (div_le_iff₀ hT).2
      nlinarith
    exact (min_le_right _ _).trans hquotient

/-- The positive saddle is the unique maximizer.-/
theorem section5SaddleExponent_eq_scaleG_iff {X T : ℝ}
    (hG : 0 < scaleG X) (hT : 0 < T) :
    section5SaddleExponent X T = scaleG X ↔ T = scaleG X := by
  constructor
  · intro heq
    have hGleT : scaleG X ≤ T := by
      calc
        scaleG X = section5SaddleExponent X T := heq.symm
        _ ≤ T := min_le_left _ _
    have hGleQuotient : scaleG X ≤ scaleG X ^ 2 / T := by
      calc
        scaleG X = section5SaddleExponent X T := heq.symm
        _ ≤ scaleG X ^ 2 / T := min_le_right _ _
    have hmul : scaleG X * T ≤ scaleG X ^ 2 :=
      (le_div_iff₀ hT).mp hGleQuotient
    have hTleG : T ≤ scaleG X := by nlinarith
    exact le_antisymm hTleG hGleT
  · rintro rfl
    exact section5SaddleExponent_at_scaleG hG.ne'

/-- Fixed-ratio substitution: at `T = λG` the exponent is `G min(λ, λ⁻¹)`.-/
theorem section5SaddleExponent_at_mul_scaleG {X lam : ℝ}
    (hG : scaleG X ≠ 0) (hlam : lam ≠ 0) :
    section5SaddleExponent X (lam * scaleG X) =
      scaleG X * min lam lam⁻¹ := by
  have hquotient : scaleG X ^ 2 / (lam * scaleG X) = scaleG X * lam⁻¹ := by
    field_simp
  rw [section5SaddleExponent, hquotient, mul_comm lam (scaleG X)]
  exact (mul_min_of_nonneg lam lam⁻¹ (scaleG_nonneg X)).symm

/-- The local Rankin parameter `L/(2T)` becomes exactly `V/2` at the saddle.-/
theorem scaleL_div_two_scaleG_eq_scaleV_div_two {X : ℝ}
    (hG : scaleG X ≠ 0) :
    scaleL X / (2 * scaleG X) = scaleV X / 2 := by
  rw [scaleV_eq]
  field_simp

/-- More generally, at `T = λG` the local parameter is `V/(2λ)`.-/
theorem scaleL_div_two_mul_scaleG_eq {X lam : ℝ}
    (hG : scaleG X ≠ 0) (hlam : lam ≠ 0) :
    scaleL X / (2 * (lam * scaleG X)) = scaleV X / (2 * lam) := by
  rw [scaleV_eq]
  field_simp

/-- The exact saddle belongs to every fixed window containing the ratio `1`.-/
theorem scaleG_mem_section5SaddleWindow {c₀ C₀ X : ℝ}
    (hc₀ : c₀ ≤ 1) (hC₀ : 1 ≤ C₀) :
    IsSection5SaddleWindow c₀ C₀ X (scaleG X) := by
  constructor
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hc₀ (scaleG_nonneg X)
  · simpa only [one_mul] using mul_le_mul_of_nonneg_right hC₀ (scaleG_nonneg X)

/-- Proposition 5.1 at the exact Section 5 saddle `T = G`.-/
theorem proposition5_1_uniform_at_scaleG {c₀ C₀ : ℝ} {error : ℕ → ℝ → ℝ}
    (huniform : HasProposition5_1Uniformity c₀ C₀ error)
    (hc₀ : c₀ ≤ 1) (hC₀ : 1 ≤ C₀)
    {x y : ℕ} (hy : 0 < y) (hxy : y ≤ x)
    (hcutoff : IsSection5ExponentialCutoff y (scaleG x)) :
    smoothMultiplierB4Sum x y ≤
      (x : ℝ) * Real.exp (-scaleG x + error x (scaleG x)) := by
  exact proposition5_1_uniform huniform x y (scaleG x) hy hxy hcutoff
    (scaleG_mem_section5SaddleWindow hc₀ hC₀)

end

end RankAmplification
