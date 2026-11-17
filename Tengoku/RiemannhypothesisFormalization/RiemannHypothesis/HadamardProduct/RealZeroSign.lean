/-
Copyright (c) 2026 Tristen Harr. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tristen Harr
-/
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.ComplexAnalysis.AntiHerglotz
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.HadamardProduct.NatZeroData
import Tengoku.RiemannhypothesisFormalization.RiemannHypothesis.RealZeros.EntireFunctions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Genus-one products with real zeros

This module gives the paper-facing sign theorem for a genus-one canonical
product indexed by `ℕ`. Its minimal public assumption bundle records nonzero
zero locations and inverse-square summability; eventual escape is derived in
`NatZeroData`. From these data the development derives product convergence,
locally uniform differentiability, and the regularized logarithmic-derivative
series. When every zero location is real, each nonconstant term has
nonpositive imaginary part in the upper half-plane.
-/

namespace OverflowResidueRH

open Filter Topology

/-- The standard monotone exhaustion of a sequence by `Finset.range`.-/
private theorem natRange_exhaustive (i : ℕ) :
    ∃ n : ℕ, i ∈ Finset.range n :=
  ⟨i + 1, Finset.mem_range.mpr (Nat.lt_succ_self i)⟩

/-- Finite-exhaustion data for a genus-one product indexed by `ℕ`.-/
noncomputable def natHadamardFiniteExhaustion
    {zeroLoc : ℕ → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc) :
    HadamardFiniteExhaustion zeroLoc :=
  HadamardFiniteExhaustion.of_invSq_mono_exhaustive
    H Finset.range Finset.range_mono natRange_exhaustive

/-- Locally uniform convergence on the full plane for the standard sequential
exhaustion under `HadamardZeroInvSqSummability`.-/
noncomputable def natHadamardProductLocallyUniformLimitData
    {zeroLoc : ℕ → ℂ}
    (H : HadamardZeroInvSqSummability zeroLoc) :
    HadamardProductLocallyUniformLimitData zeroLoc
      (natHadamardFiniteExhaustion H) :=
  HadamardProductLocallyUniformLimitData.of_invSq_univ
    H (natHadamardFiniteExhaustion H) natRange_exhaustive

/-- Every finite regularized sum over real zero locations has nonpositive
imaginary part in the upper half-plane. The regularizing terms `1 / ρ` are
real and therefore do not affect the sign.-/
theorem finiteHadamardRegularizedSum_real_im_nonpos
    (zeroLoc : ℕ → ℝ) (F : Finset ℕ)
    {s : ℂ} (hs : 0 < s.im) :
    (finiteHadamardRegularizedSum
      (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) F s).im ≤ 0 := by
  classical
  unfold finiteHadamardRegularizedSum
  rw [Complex.im_sum]
  apply Finset.sum_nonpos
  intro i _hi
  rw [Complex.add_im]
  have hregularizer : (1 / (((zeroLoc i : ℝ) : ℂ))).im = 0 := by
    simp
  rw [hregularizer, add_zero]
  exact complex_real_root_residue_imag_nonpos s (zeroLoc i) hs

/-- A finite regularized sum containing the index `i` is bounded above by
the strictly negative imaginary contribution of that one residue. The
remaining residues are nonpositive and the genus-one regularizers are real.-/
theorem finiteHadamardRegularizedSum_real_im_le_residue
    (zeroLoc : ℕ → ℝ) (F : Finset ℕ) {i : ℕ} (hi : i ∈ F)
    {s : ℂ} (hs : 0 < s.im) :
    (finiteHadamardRegularizedSum
      (fun j : ℕ => ((zeroLoc j : ℝ) : ℂ)) F s).im ≤
        ((1 : ℂ) / (s - ((zeroLoc i : ℝ) : ℂ))).im := by
  classical
  have hsplit :
      finiteHadamardRegularizedSum
          (fun j : ℕ => ((zeroLoc j : ℝ) : ℂ)) F s =
        finiteHadamardRegularizedSum
            (fun j : ℕ => ((zeroLoc j : ℝ) : ℂ)) (F.erase i) s +
          (1 / (s - ((zeroLoc i : ℝ) : ℂ)) +
            1 / ((zeroLoc i : ℝ) : ℂ)) := by
    unfold finiteHadamardRegularizedSum
    exact (F.sum_erase_add _ hi).symm
  have hrest := finiteHadamardRegularizedSum_real_im_nonpos
    zeroLoc (F.erase i) hs
  have hregularizer : (1 / ((zeroLoc i : ℝ) : ℂ)).im = 0 := by simp
  rw [hsplit, Complex.add_im, Complex.add_im, hregularizer, add_zero]
  linarith

/-- Every nonempty finite regularized sum over real zero locations is
strictly anti-Herglotz.-/
theorem finiteHadamardRegularizedSum_real_im_neg
    (zeroLoc : ℕ → ℝ) (F : Finset ℕ) (hF : F.Nonempty)
    {s : ℂ} (hs : 0 < s.im) :
    (finiteHadamardRegularizedSum
      (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) F s).im < 0 := by
  obtain ⟨i, hi⟩ := hF
  have hle := finiteHadamardRegularizedSum_real_im_le_residue
    zeroLoc F hi hs
  have hstrict := complex_real_root_residue_imag_neg s (zeroLoc i) hs
  exact lt_of_le_of_lt hle hstrict

/-- The regularized logarithmic-derivative series for real zero locations has
nonpositive imaginary part in the upper half-plane. This is obtained by
passing the finite residue-cloud inequality through the convergent partial
sums.-/
theorem hadamardRegularizedLogDerivSeries_real_im_nonpos
    (zeroLoc : ℕ → ℝ)
    (H : HadamardZeroInvSqSummability
      (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)))
    {s : ℂ} (hs : 0 < s.im) :
    (hadamardRegularizedLogDerivSeries
      (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) s).im ≤ 0 := by
  have hsum_tendsto :
      Tendsto
        (fun n : ℕ =>
          finiteHadamardRegularizedSum
            (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) (Finset.range n) s)
        Filter.atTop
        (𝓝 (hadamardRegularizedLogDerivSeries
          (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) s)) :=
    H.finiteRegularizedSum_tendsto_at_exhaustion_totalized
      Finset.range_mono natRange_exhaustive s
  have him_tendsto :
      Tendsto
        (fun n : ℕ =>
          (finiteHadamardRegularizedSum
            (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) (Finset.range n) s).im)
        Filter.atTop
        (𝓝 (hadamardRegularizedLogDerivSeries
          (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) s).im) :=
    (Complex.continuous_im.tendsto _).comp hsum_tendsto
  exact le_of_tendsto him_tendsto
    (Filter.Eventually.of_forall fun n =>
      finiteHadamardRegularizedSum_real_im_nonpos zeroLoc (Finset.range n) hs)

/-- The regularized logarithmic-derivative series of a natural-number-indexed
real zero sequence has strictly negative imaginary part in the upper
half-plane. Strictness is retained in the limit by keeping the zeroth residue
as a uniform negative upper bound.-/
theorem hadamardRegularizedLogDerivSeries_real_im_neg
    (zeroLoc : ℕ → ℝ)
    (H : HadamardZeroInvSqSummability
      (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)))
    {s : ℂ} (hs : 0 < s.im) :
    (hadamardRegularizedLogDerivSeries
      (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) s).im < 0 := by
  have hsum_tendsto :
      Tendsto
        (fun n : ℕ =>
          finiteHadamardRegularizedSum
            (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) (Finset.range n) s)
        Filter.atTop
        (𝓝 (hadamardRegularizedLogDerivSeries
          (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) s)) :=
    H.finiteRegularizedSum_tendsto_at_exhaustion_totalized
      Finset.range_mono natRange_exhaustive s
  have him_tendsto :
      Tendsto
        (fun n : ℕ =>
          (finiteHadamardRegularizedSum
            (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) (Finset.range n) s).im)
        Filter.atTop
        (𝓝 (hadamardRegularizedLogDerivSeries
          (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) s).im) :=
    (Complex.continuous_im.tendsto _).comp hsum_tendsto
  have hbound :
      ∀ᶠ n : ℕ in Filter.atTop,
        (finiteHadamardRegularizedSum
          (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) (Finset.range n) s).im ≤
            ((1 : ℂ) / (s - ((zeroLoc 0 : ℝ) : ℂ))).im := by
    filter_upwards [Filter.eventually_ge_atTop (1 : ℕ)] with n hn
    exact finiteHadamardRegularizedSum_real_im_le_residue
      zeroLoc (Finset.range n) (Finset.mem_range.mpr hn) hs
  have hlimit_le :
      (hadamardRegularizedLogDerivSeries
        (fun i : ℕ => ((zeroLoc i : ℝ) : ℂ)) s).im ≤
          ((1 : ℂ) / (s - ((zeroLoc 0 : ℝ) : ℂ))).im :=
    le_of_tendsto him_tendsto hbound
  exact lt_of_le_of_lt hlimit_le
    (complex_real_root_residue_imag_neg s (zeroLoc 0) hs)

end OverflowResidueRH
