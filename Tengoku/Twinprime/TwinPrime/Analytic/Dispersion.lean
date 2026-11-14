import Tengoku.Twinprime.TwinPrime.Analytic.FactorRanges
import Tengoku.Twinprime.TwinPrime.Analytic.DispersionGrowth

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The first dispersion step, with the signed off-diagonal retained

The exact hyperbolic support and shift two are retained in every matrix entry.
Weighted Cauchy--Schwarz splits the second moment into a diagonal and a signed
off-diagonal. Only the diagonal is bounded here; no estimate for the full
bilinear term follows by discarding the off-diagonal.
-/

noncomputable section

open Finset ArithmeticFunction Filter
open scoped ArithmeticFunction.Moebius

namespace TwinPrime.Analytic

/-- A finite weighted Cauchy--Schwarz inequality, allowing zero weights.-/
theorem weighted_sum_sq_le {ι : Type*} (s : Finset ι) (w a : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) :
    (∑ i ∈ s, w i * a i) ^ 2 ≤
      (∑ i ∈ s, w i) * ∑ i ∈ s, w i * a i ^ 2 := by
  apply sum_sq_le_sum_mul_sum_of_sq_le_mul s hw
    (fun i hi => mul_nonneg (hw i hi) (sq_nonneg _))
  intro i _
  exact le_of_eq (by ring)

/-- Both orientations of every distinct pair occur in the off-diagonal.-/
theorem sum_sq_eq_diagonal_add_offDiagonal {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (a : ι → ℝ) :
    (∑ i ∈ s, a i) ^ 2 =
      (∑ i ∈ s, a i ^ 2) + ∑ i ∈ s, ∑ j ∈ s.erase i, a i * a j := by
  rw [sq, sum_mul_sum, ← sum_add_distrib]
  apply sum_congr rfl
  intro i hi
  rw [← sum_erase_add _ _ hi]
  ring

def dispersionLeft (U M : ℕ) : Finset ℕ := (Ioc M (2 * M)).filter (U < ·)

def dispersionRight (V N : ℕ) : Finset ℕ := (Ioc N (2 * N)).filter (V < ·)

/-- The characteristic function of the true product interval is inside the entry.-/
def dispersionEntry (X d r : ℕ) : ℝ :=
  if X < d * r ∧ d * r ≤ 2 * X then (μ d : ℝ) * vonMangoldt (d * r + 2) else 0

def bilinearBox (U V X M N : ℕ) : ℝ :=
  ∑ r ∈ dispersionRight V N, vaughanBeta V r *
    ∑ d ∈ dispersionLeft U M, dispersionEntry X d r

/-- The box really is the corresponding restriction of the original factor domain.-/
theorem dispersion_boxPairs_eq (U V X M N : ℕ) :
    ((dispersionLeft U M).product (dispersionRight V N)).filter
        (fun dr => X < dr.1 * dr.2 ∧ dr.1 * dr.2 ≤ 2 * X) =
      (bilinearPairs U V X).filter
        (fun dr => M < dr.1 ∧ dr.1 ≤ 2 * M ∧ N < dr.2 ∧ dr.2 ≤ 2 * N) := by
  ext dr
  unfold dispersionLeft dispersionRight bilinearPairs
  simp only [Finset.product_eq_sprod, Finset.mem_filter, Finset.mem_product,
    Finset.mem_Ioc, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨⟨⟨hMd, hdM⟩, hUd⟩, ⟨⟨hNr, hrN⟩, hVr⟩⟩, hlow, hupp⟩
    have hdpos : 0 < dr.1 := by omega
    have hrpos : 0 < dr.2 := by omega
    have hdle : dr.1 ≤ 2 * X := (Nat.le_mul_of_pos_right dr.1 hrpos).trans hupp
    have hrle : dr.2 ≤ 2 * X := (Nat.le_mul_of_pos_left dr.2 hdpos).trans hupp
    exact ⟨⟨⟨⟨hdpos, hdle⟩, ⟨hrpos, hrle⟩⟩, hUd, hVr, hlow, hupp⟩,
      hMd, hdM, hNr, hrN⟩
  · rintro ⟨⟨_, hUd, hVr, hlow, hupp⟩, hMd, hdM, hNr, hrN⟩
    exact ⟨⟨⟨⟨hMd, hdM⟩, hUd⟩, ⟨⟨hNr, hrN⟩, hVr⟩⟩, hlow, hupp⟩

theorem bilinearBox_eq_filtered_pair_sum (U V X M N : ℕ) :
    bilinearBox U V X M N =
      ∑ dr ∈ (bilinearPairs U V X).filter
          (fun dr => M < dr.1 ∧ dr.1 ≤ 2 * M ∧ N < dr.2 ∧ dr.2 ≤ 2 * N),
        (μ dr.1 : ℝ) * vaughanBeta V dr.2 * vonMangoldt (dr.1 * dr.2 + 2) := by
  rw [← dispersion_boxPairs_eq]
  simp only [bilinearBox, Finset.mul_sum, Finset.sum_filter, Finset.product_eq_sprod]
  rw [Finset.sum_product]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro r _
  simp only [dispersionEntry]
  split_ifs <;> ring

def dispersionMass (V N : ℕ) : ℝ :=
  ∑ r ∈ dispersionRight V N, vaughanBeta V r

def dispersionDiagonal (U V X M N : ℕ) : ℝ :=
  ∑ r ∈ dispersionRight V N, vaughanBeta V r *
    ∑ d ∈ dispersionLeft U M, dispersionEntry X d r ^ 2

def dispersionOffDiagonal (U V X M N : ℕ) : ℝ :=
  ∑ r ∈ dispersionRight V N, vaughanBeta V r *
    ∑ d ∈ dispersionLeft U M, ∑ e ∈ (dispersionLeft U M).erase d,
      dispersionEntry X d r * dispersionEntry X e r

theorem dispersionMass_nonneg (V N : ℕ) : 0 ≤ dispersionMass V N :=
  sum_nonneg fun r _ => vaughanBeta_nonneg V r

theorem dispersionDiagonal_nonneg (U V X M N : ℕ) :
    0 ≤ dispersionDiagonal U V X M N :=
  sum_nonneg fun r _ => mul_nonneg (vaughanBeta_nonneg V r)
    (sum_nonneg fun _ _ => sq_nonneg _)

theorem dispersion_secondMoment_eq (U V X M N : ℕ) :
    (∑ r ∈ dispersionRight V N, vaughanBeta V r *
      (∑ d ∈ dispersionLeft U M, dispersionEntry X d r) ^ 2) =
        dispersionDiagonal U V X M N + dispersionOffDiagonal U V X M N := by
  simp_rw [sum_sq_eq_diagonal_add_offDiagonal, mul_add, sum_add_distrib]
  rfl

/-- This is the complete Cauchy--Schwarz bound, not a diagonal-only bound.-/
theorem bilinearBox_sq_le_dispersion (U V X M N : ℕ) :
    bilinearBox U V X M N ^ 2 ≤ dispersionMass V N *
      (dispersionDiagonal U V X M N + dispersionOffDiagonal U V X M N) := by
  have h := weighted_sum_sq_le (dispersionRight V N) (vaughanBeta V)
    (fun r => ∑ d ∈ dispersionLeft U M, dispersionEntry X d r)
    (fun r _ => vaughanBeta_nonneg V r)
  rw [dispersion_secondMoment_eq] at h
  exact h

theorem dispersionLeft_card_le (U M : ℕ) : (dispersionLeft U M).card ≤ M := by
  calc
    _ ≤ (Ioc M (2 * M)).card := card_filter_le _ _
    _ = M := by simp; omega

theorem dispersionRight_card_le (V N : ℕ) : (dispersionRight V N).card ≤ N := by
  exact dispersionLeft_card_le V N

theorem abs_dispersionEntry_le_log (X d r : ℕ) :
    |dispersionEntry X d r| ≤ Real.log (2 * X + 2) := by
  have hL : 0 ≤ Real.log (2 * (X : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  unfold dispersionEntry
  split_ifs with h
  · rw [abs_mul, abs_of_nonneg vonMangoldt_nonneg]
    calc
      _ ≤ 1 * vonMangoldt (d * r + 2) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast abs_moebius_le_one (n := d))
          vonMangoldt_nonneg
      _ ≤ Real.log (2 * X + 2) := by
        rw [one_mul]
        exact vonMangoldt_le_log.trans (Real.log_le_log (by positivity)
          (by exact_mod_cast (show d * r + 2 ≤ 2 * X + 2 by omega)))
  · simpa using hL

theorem dispersionEntry_sq_le (X d r : ℕ) :
    dispersionEntry X d r ^ 2 ≤ (Real.log (2 * X + 2)) ^ 2 := by
  have h := abs_dispersionEntry_le_log X d r
  nlinarith [sq_abs (dispersionEntry X d r), abs_nonneg (dispersionEntry X d r)]

/-- The weight mass bound uses only beta <= log, not prime distribution.-/
theorem dispersionMass_le (V N : ℕ) (hN : 1 ≤ N) :
    dispersionMass V N ≤ N * Real.log (2 * N) := by
  have hL : 0 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * N by omega))
  calc
    _ ≤ ∑ _r ∈ dispersionRight V N, Real.log (2 * N) := by
      apply sum_le_sum
      intro r hr
      have hrI := mem_Ioc.mp (mem_filter.mp hr).1
      exact (vaughanBeta_le_log V r).trans (Real.log_le_log
        (by exact_mod_cast (show 0 < r by omega)) (by exact_mod_cast hrI.2))
    _ = (dispersionRight V N).card * Real.log (2 * N) := by simp
    _ ≤ N * Real.log (2 * N) := mul_le_mul_of_nonneg_right
      (by exact_mod_cast dispersionRight_card_le V N) hL

theorem dispersionDiagonal_le_mass (U V X M N : ℕ) :
    dispersionDiagonal U V X M N ≤
      M * (Real.log (2 * X + 2)) ^ 2 * dispersionMass V N := by
  calc
    _ ≤ ∑ r ∈ dispersionRight V N, vaughanBeta V r *
        (M * (Real.log (2 * X + 2)) ^ 2) := by
      apply sum_le_sum
      intro r _
      apply mul_le_mul_of_nonneg_left _ (vaughanBeta_nonneg V r)
      calc
        _ ≤ ∑ _d ∈ dispersionLeft U M, (Real.log (2 * X + 2)) ^ 2 :=
          sum_le_sum fun d _ => dispersionEntry_sq_le X d r
        _ = (dispersionLeft U M).card * (Real.log (2 * X + 2)) ^ 2 := by simp
        _ ≤ M * (Real.log (2 * X + 2)) ^ 2 := mul_le_mul_of_nonneg_right
          (by exact_mod_cast dispersionLeft_card_le U M) (sq_nonneg _)
    _ = _ := by rw [← sum_mul]; unfold dispersionMass; ring

/-- A finite diagonal estimate with no admissibility condition on the box.-/
theorem dispersion_mass_mul_diagonal_le (U V X M N : ℕ) (hN : 1 ≤ N) :
    dispersionMass V N * dispersionDiagonal U V X M N ≤
      M * (N : ℝ) ^ 2 * (Real.log (2 * N)) ^ 2 * (Real.log (2 * X + 2)) ^ 2 := by
  have hmass := dispersionMass_le V N hN
  have hmass0 := dispersionMass_nonneg V N
  calc
    _ ≤ dispersionMass V N *
        (M * (Real.log (2 * X + 2)) ^ 2 * dispersionMass V N) :=
      mul_le_mul_of_nonneg_left (dispersionDiagonal_le_mass U V X M N) hmass0
    _ = M * (Real.log (2 * X + 2)) ^ 2 * (dispersionMass V N) ^ 2 := by ring
    _ ≤ M * (Real.log (2 * X + 2)) ^ 2 * (N * Real.log (2 * N)) ^ 2 := by
      gcongr
    _ = _ := by ring

/-- On a nonempty dyadic product range, the diagonal saves one factor M.-/
theorem dispersion_diagonal_saving (U V X M N : ℕ) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hMN : M * N ≤ 2 * X) :
    M * (dispersionMass V N * dispersionDiagonal U V X M N) ≤
      (2 * (X : ℝ)) ^ 2 * (Real.log (4 * X + 4)) ^ 4 := by
  have hNbound : N ≤ 2 * X :=
    (Nat.le_mul_of_pos_left N hM).trans hMN
  have hlogN : Real.log (2 * (N : ℝ)) ≤ Real.log (4 * X + 4) :=
    Real.log_le_log (by positivity)
      (by have : (N : ℝ) ≤ 2 * X := by exact_mod_cast hNbound
          linarith)
  have hlogX : Real.log (2 * (X : ℝ) + 2) ≤ Real.log (4 * X + 4) :=
    Real.log_le_log (by positivity)
      (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  have hlogN0 : 0 ≤ Real.log (2 * (N : ℝ)) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ 2 * N by omega))
  have hlogX0 : 0 ≤ Real.log (2 * (X : ℝ) + 2) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  have hprod : (M : ℝ) * N ≤ 2 * X := by exact_mod_cast hMN
  calc
    _ ≤ (M : ℝ) * (M * (N : ℝ) ^ 2 * (Real.log (2 * N)) ^ 2 *
        (Real.log (2 * X + 2)) ^ 2) :=
      mul_le_mul_of_nonneg_left (dispersion_mass_mul_diagonal_le U V X M N hN)
        (Nat.cast_nonneg M)
    _ = ((M : ℝ) * N) ^ 2 * (Real.log (2 * N)) ^ 2 *
        (Real.log (2 * X + 2)) ^ 2 := by ring
    _ ≤ (2 * (X : ℝ)) ^ 2 * (Real.log (4 * X + 4)) ^ 2 *
        (Real.log (4 * X + 4)) ^ 2 := by gcongr
    _ = _ := by ring

/-- Uniform normalized diagonal saving when the first dyadic range starts
at least halfway to the cutoff. This does not control the off-diagonal.-/
theorem dispersion_diagonal_div_sq_le (U V X M N : ℕ)
    (hU : 1 ≤ U) (hX : 1 ≤ X) (hM : 1 ≤ M) (hN : 1 ≤ N)
    (hUM : U ≤ 2 * M) (hMN : M * N ≤ 2 * X) :
    dispersionMass V N * dispersionDiagonal U V X M N / (X : ℝ) ^ 2 ≤
      8 * (Real.log (4 * X + 4)) ^ 4 / U := by
  have hsave := dispersion_diagonal_saving U V X M N hM hN hMN
  have hprod0 := mul_nonneg (dispersionMass_nonneg V N)
    (dispersionDiagonal_nonneg U V X M N)
  have hUr : (0 : ℝ) < U := by exact_mod_cast (show 0 < U by omega)
  have hXr : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hUMr : (U : ℝ) ≤ 2 * M := by exact_mod_cast hUM
  apply (div_le_div_iff₀ (sq_pos_of_pos hXr) hUr).mpr
  nlinarith [mul_le_mul_of_nonneg_right hUMr hprod0]

/-- The normalized diagonal tends to zero even after any fixed logarithmic
loss. The only hypotheses specify the dyadic factor ranges.-/
theorem tendsto_primary_dispersion_diagonal (M N : ℕ → ℕ) (k : ℕ)
    (hrange : ∀ᶠ X : ℕ in atTop,
      1 ≤ M X ∧ 1 ≤ N X ∧ primaryCutoff X ≤ 2 * M X ∧ M X * N X ≤ 2 * X) :
    Tendsto (fun X : ℕ =>
      (dispersionMass (primaryCutoff X) (N X) *
        dispersionDiagonal (primaryCutoff X) (primaryCutoff X) X (M X) (N X) /
          (X : ℝ) ^ 2) * (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  apply tendsto_mul_dispersion_log_pow_of_primaryCutoff_bound _ 8 4 k
  filter_upwards [hrange, eventually_ge_atTop 1] with X h hX
  rw [abs_of_nonneg (div_nonneg
    (mul_nonneg (dispersionMass_nonneg _ _) (dispersionDiagonal_nonneg _ _ _ _ _))
    (sq_nonneg _))]
  exact dispersion_diagonal_div_sq_le _ _ _ _ _ (primaryCutoff_pos hX) hX
    h.1 h.2.1 h.2.2.1 h.2.2.2

/-- The square-root diagonal contribution is o(X), even after any fixed
logarithmic loss. This still says nothing about the off-diagonal.-/
theorem tendsto_primary_dispersion_diagonal_sqrt (M N : ℕ → ℕ) (k : ℕ)
    (hrange : ∀ᶠ X : ℕ in atTop,
      1 ≤ M X ∧ 1 ≤ N X ∧ primaryCutoff X ≤ 2 * M X ∧ M X * N X ≤ 2 * X) :
    Tendsto (fun X : ℕ =>
      Real.sqrt (dispersionMass (primaryCutoff X) (N X) *
        dispersionDiagonal (primaryCutoff X) (primaryCutoff X) X (M X) (N X)) /
          X * (Real.log (4 * X + 4)) ^ k) atTop (nhds 0) := by
  have h := (Real.continuous_sqrt.tendsto 0).comp
    (tendsto_primary_dispersion_diagonal M N (2 * k) hrange)
  simp only [Real.sqrt_zero] at h
  apply h.congr'
  filter_upwards with X
  have hD0 := mul_nonneg (dispersionMass_nonneg (primaryCutoff X) (N X))
    (dispersionDiagonal_nonneg (primaryCutoff X) (primaryCutoff X) X (M X) (N X))
  have hL0 : 0 ≤ Real.log (4 * (X : ℝ) + 4) :=
    Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) X; linarith)
  dsimp only [Function.comp_def]
  rw [Real.sqrt_mul (div_nonneg hD0 (sq_nonneg _)), Real.sqrt_div hD0,
    Real.sqrt_sq (Nat.cast_nonneg X),
    show (Real.log (4 * (X : ℝ) + 4)) ^ (2 * k) =
      ((Real.log (4 * (X : ℝ) + 4)) ^ k) ^ 2 by rw [← pow_mul, Nat.mul_comm],
    Real.sqrt_sq (pow_nonneg hL0 k)]

end TwinPrime.Analytic
