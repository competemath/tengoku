/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Tengoku
import Tengoku.Nashembedding.NashEmbedding.Sobolev.Limits

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Vector-valued coefficient sequences

A map `ℝⁿ → ℝᴺ` (or `ℂᴺ`) is encoded on the momentum side as `N` scalar coefficient
sequences: `VecSeq n N := Fin N → (Fin n → ℤ) → ℂ`. Membership in `H^s` and the squared
norm are taken componentwise (`VMem`, `vecNormSq`); addition and scalar multiplication
are the pointwise `Pi` instances, so `(v + w) α m = v α m + w α m` definitionally.

This file lifts the scalar facts of `SobolevLimits` (quasi-triangle inequalities, Fatou,
Cauchy limits) to vector sequences. They are consumed by the abstract Günther iteration.
-/

open scoped BigOperators
open Filter Topology NashEmbedding.Sobolev

noncomputable section

namespace NashEmbedding

/-- Vector-valued coefficient sequences: `N` scalar sequences on `ℤⁿ`.-/
abbrev VecSeq (n N : ℕ) := Fin N → (Fin n → ℤ) → ℂ

variable {n N : ℕ}

/-- Componentwise membership in `H^s`.-/
def VMem (n N : ℕ) (s : ℝ) (v : VecSeq n N) : Prop := ∀ α, MemSobolev n s (v α)

/-- Componentwise squared `H^s` norm: `∑ α, ‖v α‖²_(s)`.-/
def vecNormSq (n N : ℕ) (s : ℝ) (v : VecSeq n N) : ℝ := ∑ α, sobolevNormSq n s (v α)

/--
@isnad1 id=le.0h4v.s4.7f234788392f from=translated src=- shape=12e4cb0f vocab=67875acd
-/
lemma vecNormSq_nonneg (s : ℝ) (v : VecSeq n N) : 0 ≤ vecNormSq n N s v :=
  Finset.sum_nonneg fun α _ => sobolevNormSq_nonneg s (v α)

/--
@isnad1 id=le.0h5v.s4.ca076595d8f4 from=translated src=- shape=ce10801d vocab=d75af79e
-/
lemma sobolevNormSq_le_vecNormSq (s : ℝ) (v : VecSeq n N) (α : Fin N) :
    sobolevNormSq n s (v α) ≤ vecNormSq n N s v :=
  Finset.single_le_sum (fun β _ => sobolevNormSq_nonneg s (v β)) (Finset.mem_univ α)

/--
@isnad1 id=vmem.2h5v.s4.9152299c1003 from=translated src=- shape=f44acd80 vocab=cb817489
-/
lemma VMem.mono {s t : ℝ} {v : VecSeq n N} (hv : VMem n N t v) (hst : s ≤ t) : VMem n N s v :=
  fun α => (hv α).mono hst

/--
@isnad1 id=le.2h5v.s5.a4157805d995 from=translated src=- shape=4c0778d7 vocab=1ff0f154
-/
lemma vecNormSq_mono {s t : ℝ} {v : VecSeq n N} (hv : VMem n N t v) (hst : s ≤ t) :
    vecNormSq n N s v ≤ vecNormSq n N t v :=
  Finset.sum_le_sum fun α _ => sobolevNormSq_mono (hv α) hst

/--
@isnad1 id=vmem.0h3v.s5.f42b41d6e091 from=translated src=- shape=e5b172f8 vocab=a26c127f
-/
lemma vmem_zero (s : ℝ) : VMem n N s (0 : VecSeq n N) := fun _ => memSobolev_zero s

/--
@isnad1 id=eq.0h3v.s5.f4ead3fa6731 from=translated src=- shape=95d0859e vocab=2f568971
-/
lemma vecNormSq_zero (s : ℝ) : vecNormSq n N s (0 : VecSeq n N) = 0 := by
  unfold vecNormSq
  exact Finset.sum_eq_zero fun α _ => sobolevNormSq_zero s

/--
@isnad1 id=vmem.2h5v.s6.dca73226dc18 from=translated src=- shape=6bba0cd4 vocab=4ce00e2b
-/
lemma VMem.add {s : ℝ} {v w : VecSeq n N} (hv : VMem n N s v) (hw : VMem n N s w) :
    VMem n N s (v + w) :=
  fun α => (hv α).add (hw α)

/--
@isnad1 id=vmem.2h5v.s6.66c59bded462 from=translated src=- shape=6bba0cd4 vocab=c33b922a
-/
lemma VMem.sub {s : ℝ} {v w : VecSeq n N} (hv : VMem n N s v) (hw : VMem n N s w) :
    VMem n N s (v - w) :=
  fun α => (hv α).sub (hw α)

/--
@isnad1 id=vmem.1h4v.s5.1e45f30d203c from=translated src=- shape=b73df823 vocab=304895e8
-/
lemma VMem.neg {s : ℝ} {v : VecSeq n N} (hv : VMem n N s v) : VMem n N s (-v) :=
  fun α => (hv α).neg

/--
@isnad1 id=vmem.1h5v.s5.dad15b199932 from=translated src=- shape=d02848aa vocab=a0c047b1
-/
lemma VMem.smul {s : ℝ} {v : VecSeq n N} (hv : VMem n N s v) (c : ℂ) : VMem n N s (c • v) :=
  fun α => (hv α).smul c

/--
@isnad1 id=vmem.1h6v.s6.ff6c761640dc from=translated src=- shape=67b5e799 vocab=736cba3c
-/
lemma VMem.finset_sum {ι : Type*} {s : ℝ} (S : Finset ι) {v : ι → VecSeq n N}
    (hv : ∀ i ∈ S, VMem n N s (v i)) : VMem n N s (∑ i ∈ S, v i) := by
  intro α
  have := MemSobolev.finset_sum (n := n) (s := s) S (a := fun i => v i α) (fun i hi => hv i hi α)
  have h : ((∑ i ∈ S, v i) α) = fun m => ∑ i ∈ S, v i α m := by
    funext m; simp [Finset.sum_apply]
  rw [h]; exact this

/--
@isnad1 id=le.2h5v.s7.2e71f0078a72 from=translated src=- shape=3436312b vocab=621ceb63
-/
lemma vecNormSq_add_le {s : ℝ} {v w : VecSeq n N} (hv : VMem n N s v) (hw : VMem n N s w) :
    vecNormSq n N s (v + w) ≤ 2 * vecNormSq n N s v + 2 * vecNormSq n N s w := by
  unfold vecNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun α _ => sobolevNormSq_add_le (hv α) (hw α)

/--
@isnad1 id=le.2h5v.s7.59feaebf8ed2 from=translated src=- shape=acfd9f8b vocab=1520759d
-/
lemma vecNormSq_sub_le {s : ℝ} {v w : VecSeq n N} (hv : VMem n N s v) (hw : VMem n N s w) :
    vecNormSq n N s (v - w) ≤ 2 * vecNormSq n N s v + 2 * vecNormSq n N s w := by
  unfold vecNormSq
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun α _ => sobolevNormSq_sub_le (hv α) (hw α)

/--
@isnad1 id=eq.0h4v.s5.e8a6ea48e7a7 from=translated src=- shape=560d5582 vocab=cb18e2c7
-/
lemma vecNormSq_neg (s : ℝ) (v : VecSeq n N) : vecNormSq n N s (-v) = vecNormSq n N s v := by
  unfold vecNormSq
  exact Finset.sum_congr rfl fun α _ => sobolevNormSq_neg s (v α)

/--
@isnad1 id=le.1h6v.s6.90026da32ce1 from=translated src=- shape=39b17303 vocab=87bfbaa1
-/
lemma vecNormSq_finset_sum_le {ι : Type*} {s : ℝ} (S : Finset ι) {v : ι → VecSeq n N}
    (hv : ∀ i ∈ S, VMem n N s (v i)) :
    vecNormSq n N s (∑ i ∈ S, v i) ≤ S.card * ∑ i ∈ S, vecNormSq n N s (v i) := by
  unfold vecNormSq
  rw [Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_le_sum fun α _ => ?_
  have := sobolevNormSq_finset_sum_le (n := n) (s := s) S (a := fun i => v i α)
    (fun i hi => hv i hi α)
  rw [Finset.mul_sum] at this
  have h : ((∑ i ∈ S, v i) α) = fun m => ∑ i ∈ S, v i α m := by
    funext m; simp [Finset.sum_apply]
  rw [h]; exact this

/-- A vector sequence with vanishing norm is zero.-/
lemma eq_zero_of_vecNormSq_eq_zero {s : ℝ} {v : VecSeq n N} (hv : VMem n N s v)
    (h : vecNormSq n N s v = 0) : v = 0 := by
  have hall : ∀ α, sobolevNormSq n s (v α) = 0 := by
    intro α
    exact le_antisymm (h ▸ sobolevNormSq_le_vecNormSq s v α) (sobolevNormSq_nonneg s (v α))
  funext α m
  exact eq_zero_of_sobolevNormSq_eq_zero (hv α) (hall α) m

/-- Convergence in `‖·‖²_(s)` implies coefficientwise convergence.
@isnad1 id=tendsto.3h7v.s7.d1b100e374cb from=translated src=- shape=eddc4b21 vocab=73ac91ba
-/
lemma tendsto_coeff_of_tendsto_vecNormSq {s : ℝ} {u : ℕ → VecSeq n N} {a : VecSeq n N}
    (hu : ∀ p, VMem n N s (u p)) (ha : VMem n N s a)
    (h : Tendsto (fun p => vecNormSq n N s (u p - a)) atTop (𝓝 0)) (α : Fin N) (m : Fin n → ℤ) :
    Tendsto (fun p => u p α m) atTop (𝓝 (a α m)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hw := weight_pos (n := n) s m
  -- `‖u p α m - a α m‖² ≤ vecNormSq / weight`
  have hle : ∀ p, ‖u p α m - a α m‖ ^ 2 ≤ vecNormSq n N s (u p - a) / weight n s m := by
    intro p
    rw [le_div_iff₀ hw, mul_comm]
    exact le_trans (weight_mul_norm_sq_le_sobolevNormSq ((hu p α).sub (ha α)) m)
      (sobolevNormSq_le_vecNormSq s (u p - a) α)
  have h2 : Tendsto (fun p => ‖u p α m - a α m‖ ^ 2) atTop (𝓝 0) := by
    refine squeeze_zero (fun p => sq_nonneg _) hle ?_
    simpa using h.div_const (weight n s m)
  have h3 : Tendsto (fun p => Real.sqrt (‖u p α m - a α m‖ ^ 2)) atTop (𝓝 (Real.sqrt 0)) :=
    (Real.continuous_sqrt.tendsto 0).comp h2
  simpa [Real.sqrt_sq (norm_nonneg _)] using h3

/-- **Fatou** for vector sequences: a coefficientwise limit of a sequence with
`vecNormSq ≤ M` lies in `H^s` with `vecNormSq ≤ M`.
@isnad1 id=and.3h6v.s6.dd4202185ede from=translated src=- shape=f50c1665 vocab=21852fa4
-/
theorem vmem_of_tendsto_coeff {s : ℝ} {u : ℕ → VecSeq n N} {a : VecSeq n N} {M : ℝ}
    (hu : ∀ p, VMem n N s (u p)) (hM : ∀ p, vecNormSq n N s (u p) ≤ M)
    (hlim : ∀ α m, Tendsto (fun p => u p α m) atTop (𝓝 (a α m))) :
    VMem n N s a ∧ vecNormSq n N s a ≤ M := by
  have hα : ∀ α, MemSobolev n s (a α) ∧ sobolevNormSq n s (a α) ≤ M := fun α =>
    memSobolev_of_tendsto_coeff (fun p => hu p α)
      (fun p => le_trans (sobolevNormSq_le_vecNormSq s (u p) α) (hM p)) (hlim α)
  refine ⟨fun α => (hα α).1, ?_⟩
  -- combine the components into one nonnegative series and use Fatou on partial sums
  set g : (Fin n → ℤ) → ℝ := fun m => ∑ α, weight n s m * ‖a α m‖ ^ 2 with hg
  have hg0 : 0 ≤ g := fun m => Finset.sum_nonneg fun α _ =>
    mul_nonneg (weight_nonneg s m) (sq_nonneg _)
  have hsum : ∀ F : Finset (Fin n → ℤ), ∑ m ∈ F, g m ≤ M := by
    intro F
    -- the finite partial sum is the limit of the corresponding partial sums of `u p`
    have hpt : Tendsto (fun p => ∑ m ∈ F, ∑ α, weight n s m * ‖u p α m‖ ^ 2) atTop
        (𝓝 (∑ m ∈ F, g m)) := by
      refine tendsto_finsetSum _ fun m _ => tendsto_finsetSum _ fun α _ => ?_
      exact ((hlim α m).norm.pow 2).const_mul _
    refine le_of_tendsto hpt (Filter.Eventually.of_forall fun p => ?_)
    rw [Finset.sum_comm]
    refine le_trans (Finset.sum_le_sum fun α _ => ?_) (hM p)
    exact (hu p α).sum_le_tsum F (fun m _ => mul_nonneg (weight_nonneg s m) (sq_nonneg _))
  have hgs : Summable g := summable_of_sum_le hg0 hsum
  have : vecNormSq n N s a = ∑' m, g m := by
    unfold vecNormSq sobolevNormSq
    rw [hg, Summable.tsum_finsetSum fun α _ => (hα α).1]
  rw [this]
  exact hgs.tsum_le_of_sum_le hsum

/-- **Cauchy sequences converge**, vector version.
@isnad1 id=ex.2h4v.s7.f03fa8febf7b from=translated src=- shape=c2730d15 vocab=d52f7b63
-/
theorem exists_limit_of_cauchy_vec {s : ℝ} {u : ℕ → VecSeq n N}
    (hu : ∀ p, VMem n N s (u p))
    (hc : ∀ ε > 0, ∃ P, ∀ p ≥ P, ∀ q ≥ P, vecNormSq n N s (u p - u q) ≤ ε) :
    ∃ a : VecSeq n N, VMem n N s a ∧
      (∀ α m, Tendsto (fun p => u p α m) atTop (𝓝 (a α m))) ∧
      Tendsto (fun p => vecNormSq n N s (u p - a)) atTop (𝓝 0) := by
  have hα : ∀ α, ∃ b : (Fin n → ℤ) → ℂ, MemSobolev n s b ∧
      (∀ m, Tendsto (fun p => u p α m) atTop (𝓝 (b m))) ∧
      Tendsto (fun p => sobolevNormSq n s (fun m => u p α m - b m)) atTop (𝓝 0) := by
    intro α
    refine exists_limit_of_cauchy (fun p => hu p α) fun ε hε => ?_
    obtain ⟨P, hP⟩ := hc ε hε
    exact ⟨P, fun p hp q hq => le_trans (sobolevNormSq_le_vecNormSq s (u p - u q) α) (hP p hp q hq)⟩
  choose b hb using hα
  refine ⟨b, fun α => (hb α).1, fun α => (hb α).2.1, ?_⟩
  unfold vecNormSq
  have := tendsto_finsetSum (Finset.univ : Finset (Fin N)) fun α _ => (hb α).2.2
  simpa [← Pi.sub_apply] using this

end NashEmbedding

end
