import Tengoku.PaperCLean.PaperCV282.ClosureCRTMass
import Tengoku.Seed.Analysis.SpecialFunctions.Exponential

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The complete factorial series of unordered certificates

The left series is finite by the actual cardinality of the cell family.
The right exponential series is summable for every real weight. Constants
are explicit and uniform even when the nonnegative moment weight grows.
-/

namespace PaperC.V282.ClosureCRTSeries

open CRT Finset ClosureCRTMass
open scoped BigOperators

noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- There is no unordered certificate larger than the available cell family.
@isnad1 id=eq.1h7v.s5.0fff2e98ac2d from=translated src=- shape=5f743430 vocab=86a6c3d6
-/
theorem certificateMass_eq_zero_of_card_lt
    (s : Finset ι) (r : ℕ) (modulus : ι → ℕ)
    (count : UnorderedCertificate s r → ℕ) (M : ℕ) (u : ℝ) (hr : s.card < r) :
    certificateMass s r modulus count M u = 0 := by
  unfold certificateMass
  apply Finset.sum_eq_zero
  intro T hT
  have hcard := Finset.card_le_card (unorderedCertificate_subset T)
  rw [unorderedCertificate_card] at hcard
  omega

/-- The full mass sums every certificate, including the empty one, exactly once.
@isnad1 id=eq.0h6v.s6.a8c5d10d6825 from=translated src=- shape=c6449219 vocab=5b6e4161
-/
theorem certificateMass_tsum_eq_sum
    (s : Finset ι) (modulus : ι → ℕ)
    (count : (r : ℕ) → UnorderedCertificate s r → ℕ) (M : ℕ) (u : ℝ) :
    (∑' r, certificateMass s r modulus (count r) M u) =
      ∑ r ∈ Finset.range (s.card + 1), certificateMass s r modulus (count r) M u := by
  apply tsum_eq_sum
  intro r hr
  apply certificateMass_eq_zero_of_card_lt
  simpa only [Finset.mem_range, not_lt, Nat.add_one_le_iff] using hr

/-- Summing individual factorial bounds introduces no weight-dependent constant.
@isnad1 id=le.3h8v.s7.51b408df4c13 from=translated src=- shape=bdf16f3a vocab=65711beb
-/
theorem certificateMass_tsum_le_of_count
    (s : Finset ι) (modulus : ι → ℕ)
    (count : (r : ℕ) → UnorderedCertificate s r → ℕ) (M D : ℕ) (u V : ℝ)
    (hu : 0 ≤ u) (hV : 0 ≤ V)
    (hcount : ∀ r T, CertificateAdmissible modulus M T →
      (count r T : ℝ) ≤ V / (certificateModulusProduct modulus T : ℝ) ^ D) :
    (∑' r, certificateMass s r modulus (count r) M u) ≤
      V * ∑' r : ℕ, (∑ i ∈ s, u / (modulus i : ℝ) ^ D) ^ r / r.factorial := by
  let x : ℝ := ∑ i ∈ s, u / (modulus i : ℝ) ^ D
  have hx : 0 ≤ x := Finset.sum_nonneg (fun i hi => by positivity)
  have hseries : Summable (fun r : ℕ => x ^ r / (r.factorial : ℝ)) :=
    (NormedSpace.expSeries_div_hasSum_exp x).summable
  rw [certificateMass_tsum_eq_sum]
  calc
    _ ≤ ∑ r ∈ Finset.range (s.card + 1), V * (x ^ r / r.factorial) := by
      apply Finset.sum_le_sum
      intro r hr
      exact certificateMass_le_of_count s r modulus (count r) M D u V hu hV (hcount r)
    _ = V * ∑ r ∈ Finset.range (s.card + 1), x ^ r / r.factorial := by rw [Finset.mul_sum]
    _ ≤ V * ∑' r : ℕ, x ^ r / r.factorial := by
      apply mul_le_mul_of_nonneg_left _ hV
      exact Summable.sum_le_tsum _ (fun r hr => div_nonneg (pow_nonneg hx r) (by positivity)) hseries

/-- Complete one-coordinate CRT series on arbitrary integer intervals of length `C₀*M`.
@isnad1 id=le.5h9v.s7.bc1c3fe1b3f8 from=translated src=- shape=f7a713b8 vocab=7d5afc69
-/
theorem intervalMass_tsum_le (s : Finset ι) (residue : ι → ℤ) (modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime) (a b : ℤ) (C₀ : ℝ) (M : ℕ)
    (hC : 0 ≤ C₀) (hab : a ≤ b) (hlen : (b - a : ℝ) ≤ C₀ * M)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑' r, intervalMass s r residue modulus a b M u) ≤
      ((C₀ + 1) * M) * ∑' r : ℕ, (∑ i ∈ s, u / (modulus i : ℝ)) ^ r / r.factorial := by
  simpa only [intervalMass, pow_one] using certificateMass_tsum_le_of_count
    s modulus (fun _ T => (ClosureCRTIntervals.integerSolutions residue modulus a b T).card)
    M 1 u ((C₀ + 1) * M) hu (by positivity)
    (fun r T hT => by simpa only [pow_one] using
      ClosureCRTIntervals.integerSolutions_card_le residue modulus hprime a b C₀ M hC hab hlen T hT)

/-- Complete two-coordinate CRT series with the square of the same uniform constant.
@isnad1 id=le.7h12v.s8.786c31b3b56c from=translated src=- shape=237b39a7 vocab=2fe5f1e6
-/
theorem rectangleMass_tsum_le (s : Finset ι) (residue₁ residue₂ : ι → ℤ) (modulus : ι → ℕ)
    (hprime : ∀ i, (modulus i).Prime) (a₁ b₁ a₂ b₂ : ℤ) (C₀ : ℝ) (M : ℕ)
    (hC : 0 ≤ C₀) (h₁ : a₁ ≤ b₁) (h₂ : a₂ ≤ b₂)
    (hlen₁ : (b₁ - a₁ : ℝ) ≤ C₀ * M) (hlen₂ : (b₂ - a₂ : ℝ) ≤ C₀ * M)
    (u : ℝ) (hu : 0 ≤ u) :
    (∑' r, rectangleMass s r residue₁ residue₂ modulus a₁ b₁ a₂ b₂ M u) ≤
      ((C₀ + 1) * M) ^ 2 * ∑' r : ℕ, (∑ i ∈ s, u / (modulus i : ℝ) ^ 2) ^ r / r.factorial := by
  apply certificateMass_tsum_le_of_count s modulus _ M 2 u (((C₀ + 1) * M) ^ 2) hu (sq_nonneg _)
  intro r T hT
  simpa only [div_pow] using
    ClosureCRTIntervals.rectangleSolutions_card_le residue₁ residue₂ modulus hprime a₁ b₁ a₂ b₂
      C₀ M hC h₁ h₂ hlen₁ hlen₂ T hT

end
end PaperC.V282.ClosureCRTSeries
