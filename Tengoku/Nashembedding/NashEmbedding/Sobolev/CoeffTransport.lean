/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Tengoku
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Periodization
import Tengoku.Nashembedding.NashEmbedding.Sobolev.SynthesisRegularity
import Tengoku.Nashembedding.NashEmbedding.Sobolev.ConvolutionAlgebra
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Limits
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Resolvent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport between position space and momentum space

Dictionary between smooth `2πℤⁿ`-periodic functions `f : ℝⁿ → ℂ` and their coefficient
sequences `stdFourierCoeff n f : ℤⁿ → ℂ`, used to move Günther's fixed-point equation
from the momentum side (where it is solved) back to position space (where Theorem B is
stated):

* coefficients of smooth periodic functions are rapidly decaying (`IsRapidDecay`);
* `stdFourierCoeff` is linear (sums, differences, scalar multiples) and turns products
  into `seqConv`, `∂ⱼ` into `partialCoeff j`, and `L = ∑ₖ ∂ₖ²` into `-laplacianCoeff`;
* real-valued functions have `conjReflect`-fixed coefficients;
* `fourierSynthesis` is linear on absolutely summable sequences;
* `IsRapidDecay` is closed under all the momentum-side operations of the Günther operator.
-/

open scoped BigOperators ComplexConjugate ContDiff
open Complex

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Rapid decay of coefficients -/

/-- Coefficients of smooth periodic functions are rapidly decaying
(`stdFourierCoeff_rapid_decay` + `memSobolev_of_rapid_decay`).
@isnad1 id=israpidd.3h2v.s6.c2671bb033ec from=translated src=- shape=96602185 vocab=86f448eb
-/
theorem isRapidDecay_stdFourierCoeff (hn : 0 < n) {f : (Fin n → ℝ) → ℂ}
    (hsmooth : ContDiff ℝ ∞ f) (hper : IsPeriodic2Pi f) :
    IsRapidDecay n (stdFourierCoeff n f) := fun s =>
  memSobolev_of_rapid_decay hn (fun N => stdFourierCoeff_rapid_decay hn hsmooth hper N) s

/-! ## Linearity of coefficients (continuous integrands) -/

/-! ## Products, derivatives, the Laplacian -/

/-- `stdFourierCoeff_partialDeriv` as an equality of sequences.
@isnad1 id=eq.3h3v.s7.f28d4973b6dc from=translated src=- shape=26b87992 vocab=449fb527
-/
theorem stdFourierCoeff_partialDeriv' (hn : 0 < n) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hper : IsPeriodic2Pi f) (j : Fin n) :
    stdFourierCoeff n (partialDeriv j f) = partialCoeff j (stdFourierCoeff n f) := by
  funext m
  exact stdFourierCoeff_partialDeriv hn hf hper j m

/-- `∂ⱼ∂ⱼ` on coefficients is multiplication by `-mⱼ²`; summing over `j`,
`L = ∑ⱼ ∂ⱼ²` corresponds to `-laplacianCoeff`.
@isnad1 id=eq.3h2v.s7.cd1a1ab3c1c8 from=translated src=- shape=c62f564d vocab=6a947cc3
-/
theorem stdFourierCoeff_sumSqDeriv (hn : 0 < n) {f : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ ∞ f) (hper : IsPeriodic2Pi f) :
    stdFourierCoeff n (fun x => ∑ k, partialDeriv k (partialDeriv k f) x)
      = fun m => -laplacianCoeff (stdFourierCoeff n f) m := by
  funext m
  have h : stdFourierCoeff n (fun x => ∑ k, partialDeriv k (partialDeriv k f) x) m
      = stdFourierCoeff n (laplacian f) m := rfl
  rw [h, stdFourierCoeff_laplacian hn hf hper m, laplacianCoeff]
  push_cast
  ring

/-- Real-valued functions have `conjReflect`-fixed coefficients.
@isnad1 id=eq.2h2v.s6.bc81becfba39 from=translated src=- shape=5782edd6 vocab=833d8bb4
-/
theorem conjReflect_stdFourierCoeff_of_real {f : (Fin n → ℝ) → ℂ} (hf : Continuous f)
    (hreal : ∀ x, (f x).im = 0) : conjReflect (stdFourierCoeff n f) = stdFourierCoeff n f := by
  funext m
  have hc : ∀ θ : Fin n → ℝ, (starRingEnd ℂ) (f θ * fourierExp n m θ)
      = f θ * fourierExp n (-m) θ := by
    intro θ
    rw [map_mul, starRingEnd_fourierExp, Complex.conj_eq_iff_im.2 (hreal θ)]
  simp only [conjReflect, stdFourierCoeff, neg_neg]
  rw [map_mul, ← integral_conj]
  simp_rw [hc]
  congr 1
  simp [map_inv₀, map_ofNat]

/-! ## Linearity of synthesis -/

/--
@isnad1 id=eq.2h3v.s6.c83c138455c7 from=translated src=- shape=b8d36fdd vocab=c9230448
-/
lemma fourierSynthesis_add' {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖)) (hb : Summable (fun m => ‖b m‖)) :
    fourierSynthesis n (fun m => a m + b m) = fun θ => fourierSynthesis n a θ + fourierSynthesis n b θ := by
  funext θ
  exact fourierSynthesis_add ha hb θ

/--
@isnad1 id=eq.2h3v.s6.8a71f9fe3578 from=translated src=- shape=b8d36fdd vocab=c44ccacd
-/
lemma fourierSynthesis_sub {a b : (Fin n → ℤ) → ℂ}
    (ha : Summable (fun m => ‖a m‖)) (hb : Summable (fun m => ‖b m‖)) :
    fourierSynthesis n (fun m => a m - b m) = fun θ => fourierSynthesis n a θ - fourierSynthesis n b θ := by
  funext θ
  unfold fourierSynthesis
  rw [← Summable.tsum_sub]
  · exact tsum_congr fun m => sub_mul _ _ _
  · exact .of_norm <| by simpa [norm_fourierExp] using ha
  · exact .of_norm <| by simpa [norm_fourierExp] using hb

/--
@isnad1 id=eq.0h3v.s5.019010529f45 from=translated src=- shape=b96cf9d1 vocab=e5667a68
-/
lemma fourierSynthesis_const_mul (c : ℂ) (a : (Fin n → ℤ) → ℂ) :
    fourierSynthesis n (fun m => c * a m) = fun θ => c * fourierSynthesis n a θ := by
  funext θ
  unfold fourierSynthesis
  rw [← tsum_mul_left]
  exact tsum_congr fun m => by ring

/--
@isnad1 id=eq.0h2v.s5.02ad64de22f6 from=translated src=- shape=1166e1ae vocab=02c00b83
-/
lemma fourierSynthesis_neg (a : (Fin n → ℤ) → ℂ) :
    fourierSynthesis n (fun m => -a m) = fun θ => -fourierSynthesis n a θ := by
  funext θ
  unfold fourierSynthesis
  rw [← tsum_neg]
  exact tsum_congr fun m => by ring

/--
@isnad1 id=eq.1h4v.s6.8081237c130f from=translated src=- shape=ca033db1 vocab=d8560d23
-/
lemma fourierSynthesis_finset_sum {ι : Type*} (S : Finset ι) {a : ι → (Fin n → ℤ) → ℂ}
    (ha : ∀ i ∈ S, Summable (fun m => ‖a i m‖)) :
    fourierSynthesis n (fun m => ∑ i ∈ S, a i m) = fun θ => ∑ i ∈ S, fourierSynthesis n (a i) θ := by
  funext θ
  unfold fourierSynthesis
  rw [show (fun m : Fin n → ℤ => (∑ i ∈ S, a i m) * fourierExp n m θ)
      = fun m => ∑ i ∈ S, a i m * fourierExp n m θ from
    funext fun m => by rw [Finset.sum_mul]]
  exact Summable.tsum_finsetSum fun i hi =>
    .of_norm <| by simpa [norm_fourierExp] using ha i hi

/-! ## Closure of rapid decay -/

/--
@isnad1 id=israpidd.0h1v.s3.321e3847c0af from=translated src=- shape=edfd68f7 vocab=00b7b8c7
-/
lemma isRapidDecay_zero : IsRapidDecay n (fun _ => (0 : ℂ)) := fun s => memSobolev_zero s

/--
@isnad1 id=israpidd.2h3v.s5.9593520c41b8 from=translated src=- shape=6c043433 vocab=d2e471ae
-/
lemma IsRapidDecay.add {a b : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) (hb : IsRapidDecay n b) :
    IsRapidDecay n (fun m => a m + b m) := fun s => (ha s).add (hb s)

/--
@isnad1 id=israpidd.2h3v.s5.d484e1cab4e5 from=translated src=- shape=6c043433 vocab=e169ccfe
-/
lemma IsRapidDecay.sub {a b : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) (hb : IsRapidDecay n b) :
    IsRapidDecay n (fun m => a m - b m) := fun s => (ha s).sub (hb s)

/--
@isnad1 id=israpidd.1h2v.s4.a50216133bff from=translated src=- shape=463fb8d7 vocab=340c9cb5
-/
lemma IsRapidDecay.neg {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) :
    IsRapidDecay n (fun m => -a m) := fun s => (ha s).neg

/--
@isnad1 id=israpidd.1h3v.s5.71e2470efad0 from=translated src=- shape=dc5e3649 vocab=65025b7b
-/
lemma IsRapidDecay.const_mul {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) (c : ℂ) :
    IsRapidDecay n (fun m => c * a m) := fun s => (ha s).smul c

/--
@isnad1 id=israpidd.1h4v.s5.9ab21818c170 from=translated src=- shape=5e4d3a64 vocab=1d733d5a
-/
lemma IsRapidDecay.finset_sum {ι : Type*} (S : Finset ι) {a : ι → (Fin n → ℤ) → ℂ}
    (ha : ∀ i ∈ S, IsRapidDecay n (a i)) : IsRapidDecay n (fun m => ∑ i ∈ S, a i m) :=
  fun s => MemSobolev.finset_sum S fun i hi => ha i hi s

/--
@isnad1 id=israpidd.1h2v.s4.cbad3f4b5505 from=translated src=- shape=1883ffc1 vocab=b1c38b67
-/
lemma IsRapidDecay.resolventCoeff {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) :
    IsRapidDecay n (resolventCoeff a) := by
  intro s
  have := memSobolev_resolventCoeff (ha (s - 2))
  simpa using this

/--
@isnad1 id=israpidd.1h2v.s4.c0df6f23100a from=translated src=- shape=1883ffc1 vocab=5f1a9539
-/
lemma IsRapidDecay.laplacianCoeff {a : (Fin n → ℤ) → ℂ} (ha : IsRapidDecay n a) :
    IsRapidDecay n (laplacianCoeff a) := fun s => memSobolev_laplacianCoeff (ha (s + 2))

/-- Convolution of rapidly decaying sequences is rapidly decaying (MT2 at every level
`s > n/2`, then monotonicity).
@isnad1 id=israpidd.3h3v.s5.c9d57cff8342 from=translated src=- shape=70adf2c2 vocab=27ef1625
-/
lemma IsRapidDecay.seqConv (hn : 0 < n) {a b : (Fin n → ℤ) → ℂ}
    (ha : IsRapidDecay n a) (hb : IsRapidDecay n b) : IsRapidDecay n (seqConv a b) := by
  intro s
  set t : ℝ := max s (n : ℝ) + 1 with ht
  have hst : s ≤ t := by
    have := le_max_left s (n : ℝ)
    simp only [ht]; linarith
  have hnt : (n : ℝ) < 2 * t := by
    have := le_max_right s (n : ℝ)
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    simp only [ht]; linarith
  exact ((second_multiplication_theorem_seq hn hnt (ha t) (hb t)).1).mono hst

end NashEmbedding.Sobolev

end
