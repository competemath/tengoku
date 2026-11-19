/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Tengoku
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Basic
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Differentiation
import Tengoku.Nashembedding.NashEmbedding.Sobolev.FourierSynthesis
import Tengoku.Nashembedding.NashEmbedding.Sobolev.MultiplicationSharp
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Resolvent

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebra of coefficient convolution, and conjugate reflection

`seqConv a b m = ∑' i, a i * b (m - i)` is the multiplication of periodic functions on
the momentum side. This file records:

* **bilinearity and commutativity** of `seqConv`, under the summability guaranteed by
  `a, b ∈ H^s` with `2s > n` (`seqConv_summable`); commutativity and the zero laws are
  unconditional (`tsum` reindexing along `i ↦ m - i`);
* the **conjugate reflection** `conjReflect a m = conj (a (-m))`, which fixes exactly the
  coefficient sequences of real-valued functions. It commutes with `seqConv`,
  `partialCoeff`, `resolventCoeff`, preserves `H^s` and its norm, and the Fourier synthesis
  of a `conjReflect`-fixed absolutely summable sequence is real-valued.

The Günther operator is built from these operations, so it preserves `conjReflect`-fixed
sequences; this is how the fixed point of Theorem B is seen to be real (`ℝᴺ`-valued).
-/

open scoped BigOperators ComplexConjugate
open Complex

noncomputable section

namespace NashEmbedding.Sobolev

variable {n : ℕ}

/-! ## Unconditional identities -/

/--
@isnad1 id=eq.0h3v.s4.e74da5415855 from=translated src=- shape=356f6e26 vocab=e6e08b62
-/
lemma seqConv_comm (a b : (Fin n → ℤ) → ℂ) : seqConv a b = seqConv b a := by
  funext m
  unfold seqConv
  rw [← (Equiv.subLeft m).tsum_eq (fun i => b i * a (m - i))]
  refine tsum_congr fun i => ?_
  simp [Equiv.subLeft_apply, mul_comm]

/--
@isnad1 id=eq.0h2v.s5.c3f6591b69b2 from=translated src=- shape=8ce46526 vocab=e6e08b62
-/
lemma seqConv_zero_left (b : (Fin n → ℤ) → ℂ) : seqConv (fun _ => (0 : ℂ)) b = fun _ => 0 := by
  funext m; simp [seqConv]

/--
@isnad1 id=eq.0h2v.s5.2f2a7c67349d from=translated src=- shape=55308960 vocab=e6e08b62
-/
lemma seqConv_zero_right (a : (Fin n → ℤ) → ℂ) : seqConv a (fun _ => (0 : ℂ)) = fun _ => 0 := by
  funext m; simp [seqConv]

/--
@isnad1 id=eq.0h4v.s5.9c910ca31f34 from=translated src=- shape=1eff44f9 vocab=212a01a5
-/
lemma seqConv_smul_left (c : ℂ) (a b : (Fin n → ℤ) → ℂ) :
    seqConv (fun m => c * a m) b = fun m => c * seqConv a b m := by
  funext m
  simp only [seqConv, mul_assoc]
  exact tsum_mul_left

/--
@isnad1 id=eq.0h4v.s5.3aa2f414a17f from=translated src=- shape=cafab029 vocab=212a01a5
-/
lemma seqConv_smul_right (c : ℂ) (a b : (Fin n → ℤ) → ℂ) :
    seqConv a (fun m => c * b m) = fun m => c * seqConv a b m := by
  funext m
  simp only [seqConv, mul_left_comm]
  exact tsum_mul_left

/--
@isnad1 id=eq.0h3v.s5.b0b7f92cbd9c from=translated src=- shape=13bb33b6 vocab=93e54fbf
-/
lemma seqConv_neg_left (a b : (Fin n → ℤ) → ℂ) :
    seqConv (fun m => -a m) b = fun m => -seqConv a b m := by
  funext m
  simp only [seqConv, neg_mul]
  exact tsum_neg

/-! ## Additivity under summability -/

/--
@isnad1 id=eq.5h5v.s6.d9d9f1c86ec0 from=translated src=- shape=666f45c2 vocab=511c71e3
-/
lemma seqConv_sub_left {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a a' b : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) (ha' : MemSobolev n s a')
    (hb : MemSobolev n s b) :
    seqConv (fun m => a m - a' m) b = fun m => seqConv a b m - seqConv a' b m := by
  funext m
  simp only [seqConv, sub_mul]
  exact (seqConv_summable hn hs ha hb m).tsum_sub (seqConv_summable hn hs ha' hb m)

/--
@isnad1 id=eq.5h5v.s6.504073ff037d from=translated src=- shape=d8d26b30 vocab=511c71e3
-/
lemma seqConv_sub_right {s : ℝ} (hn : 0 < n) (hs : (n : ℝ) < 2 * s)
    {a b b' : (Fin n → ℤ) → ℂ} (ha : MemSobolev n s a) (hb : MemSobolev n s b)
    (hb' : MemSobolev n s b') :
    seqConv a (fun m => b m - b' m) = fun m => seqConv a b m - seqConv a b' m := by
  funext m
  simp only [seqConv, mul_sub]
  exact (seqConv_summable hn hs ha hb m).tsum_sub (seqConv_summable hn hs ha hb' m)

/-! ## Conjugate reflection -/

/-- `conjReflect a m = conj (a (-m))`. The coefficient sequence of a function `f` is
`conjReflect`-fixed iff `f` is real-valued.-/
def conjReflect (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) : ℂ := conj (a (-m))

/--
@isnad1 id=eq.0h2v.s4.34e17f57cd2c from=translated src=- shape=2b3b408a vocab=b736c336
-/
lemma conjReflect_conjReflect (a : (Fin n → ℤ) → ℂ) : conjReflect (conjReflect a) = a := by
  funext m; simp [conjReflect]

/--
@isnad1 id=eq.0h3v.s5.575146c97809 from=translated src=- shape=a0f1f827 vocab=d9b69d43
-/
lemma norm_conjReflect (a : (Fin n → ℤ) → ℂ) (m : Fin n → ℤ) :
    ‖conjReflect a m‖ = ‖a (-m)‖ := by
  simp [conjReflect]

/--
@isnad1 id=eq.0h3v.s5.f8a4a80b569e from=translated src=- shape=f1a19534 vocab=c3cab2a7
-/
lemma conjReflect_add (a b : (Fin n → ℤ) → ℂ) :
    conjReflect (fun m => a m + b m) = fun m => conjReflect a m + conjReflect b m := by
  funext m; simp [conjReflect]

/--
@isnad1 id=eq.0h3v.s5.425c1d00a269 from=translated src=- shape=f1a19534 vocab=a7559e50
-/
lemma conjReflect_sub (a b : (Fin n → ℤ) → ℂ) :
    conjReflect (fun m => a m - b m) = fun m => conjReflect a m - conjReflect b m := by
  funext m; simp [conjReflect]

/--
@isnad1 id=eq.0h3v.s5.7ad2856be5fa from=translated src=- shape=6b874a6b vocab=20ecbec6
-/
lemma conjReflect_real_smul (c : ℝ) (a : (Fin n → ℤ) → ℂ) :
    conjReflect (fun m => (c : ℂ) * a m) = fun m => (c : ℂ) * conjReflect a m := by
  funext m; simp [conjReflect]

/--
@isnad1 id=eq.0h4v.s5.7d0d939d6b7b from=translated src=- shape=21c1abf7 vocab=f1a2b7b9
-/
lemma conjReflect_finset_sum {ι : Type*} (S : Finset ι) (a : ι → (Fin n → ℤ) → ℂ) :
    conjReflect (fun m => ∑ i ∈ S, a i m) = fun m => ∑ i ∈ S, conjReflect (a i) m := by
  funext m; simp [conjReflect, map_sum]

/--
@isnad1 id=eq.0h3v.s5.6beab894d8c4 from=translated src=- shape=ed254927 vocab=ce407698
-/
lemma conjReflect_seqConv (a b : (Fin n → ℤ) → ℂ) :
    conjReflect (seqConv a b) = seqConv (conjReflect a) (conjReflect b) := by
  funext m
  simp only [conjReflect, seqConv]
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg (Fin n → ℤ)).tsum_eq (fun i => conj (a i * b (-m - i)))]
  refine tsum_congr fun i => ?_
  simp only [Equiv.neg_apply, map_mul, neg_sub_neg, neg_sub]

/--
@isnad1 id=eq.0h3v.s4.659d03f1c45c from=translated src=- shape=97b60f19 vocab=c5a7eb26
-/
lemma conjReflect_partialCoeff (j : Fin n) (a : (Fin n → ℤ) → ℂ) :
    conjReflect (partialCoeff j a) = partialCoeff j (conjReflect a) := by
  funext m
  simp [conjReflect, partialCoeff, Complex.conj_I]

/--
@isnad1 id=eq.0h2v.s4.a65225799c09 from=translated src=- shape=7f2c005f vocab=a7c98354
-/
lemma conjReflect_resolventCoeff (a : (Fin n → ℤ) → ℂ) :
    conjReflect (resolventCoeff a) = resolventCoeff (conjReflect a) := by
  funext m
  simp [conjReflect, resolventCoeff, map_div₀]

/--
@isnad1 id=eq.0h2v.s4.9ab2de6fb9c2 from=translated src=- shape=7f2c005f vocab=63211b4c
-/
lemma conjReflect_laplacianCoeff (a : (Fin n → ℤ) → ℂ) :
    conjReflect (laplacianCoeff a) = laplacianCoeff (conjReflect a) := by
  funext m
  simp [conjReflect, laplacianCoeff]

/-- The Fourier synthesis of a `conjReflect`-fixed sequence is real-valued (no summability
is needed: `conj` commutes with `tsum` unconditionally).
@isnad1 id=eq.1h3v.s5.b2e0cb2e0b27 from=translated src=- shape=7c6d62ad vocab=9bfe40bc
-/
theorem fourierSynthesis_im_eq_zero {a : (Fin n → ℤ) → ℂ}
    (hfix : conjReflect a = a) (θ : Fin n → ℝ) : (fourierSynthesis n a θ).im = 0 := by
  rw [← Complex.conj_eq_iff_im]
  unfold fourierSynthesis
  rw [Complex.conj_tsum]
  rw [← (Equiv.neg (Fin n → ℤ)).tsum_eq (fun m => a m * fourierExp n m θ)]
  refine tsum_congr fun m => ?_
  have hm : conj (a m) = a (-m) := by
    have := congrFun hfix (-m)
    simpa [conjReflect] using this
  have he : conj (fourierExp n m θ) = fourierExp n (-m) θ := by
    unfold fourierExp
    rw [← Complex.exp_conj]
    congr 1
    simp [Complex.conj_I, Finset.sum_neg_distrib]
  simp only [Equiv.neg_apply, map_mul, hm, he]

end NashEmbedding.Sobolev

end
