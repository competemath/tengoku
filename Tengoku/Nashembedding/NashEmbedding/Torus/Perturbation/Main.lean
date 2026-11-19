/-
Copyright (c) 2026 David Wiygul. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aristotle (Harmonic), Claude Fable 5 (Anthropic), Claude Opus 4.7 (Anthropic)
  — at the request of David Wiygul
-/
import Tengoku
import Tengoku.Nashembedding.NashEmbedding.Torus.Perturbation.DualFrame
import Tengoku.Nashembedding.NashEmbedding.Torus.Perturbation.GuntherIdentitySeq

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Theorem B (Günther's perturbation theorem) for the flat torus

Let `u₀ : ℝⁿ → ℝᴺ` be smooth, `2πℤⁿ`-periodic and *free*: at every point the
`n + n(n+1)/2` vectors `∂ᵢu₀`, `∂ₚ∂_q u₀` (`p ≤ q`) are linearly independent. Then there is
`ε > 0` such that for every smooth periodic symmetric `h` with `H^r` size `< ε`
(`r = ⌊n/2⌋ + 4`) there is a smooth periodic `v : ℝⁿ → ℝᴺ` with

  `∂ᵢ(u₀ + v) · ∂ⱼ(u₀ + v) = ∂ᵢu₀ · ∂ⱼu₀ + hᵢⱼ`.

Proof shape:
1. the dual frame `D` of `{∂ᵢu₀} ∪ {∂ₚ∂_q u₀}` (`DualFrame.lean`);
2. the Günther operator `T v = c + B v v` on coefficient sequences, built from the
   coefficients of `D` and `h` (`GuntherOperator.lean`), satisfies `IterHyp`;
3. the abstract iteration (`GuntherIteration.lean`) gives a fixed point `v∞` in every `H^k`,
   with `conjReflect`-fixed (real) components, when `4 ‖c‖²_(r) ≤ ρ`, i.e. when `h` is small;
4. the synthesis `V = vsynth v∞` is smooth periodic, and taking coefficients of the
   position-space expression `-∑ᵢ F̃ᵢ Dᵢ + ∑_{p≤q} ½(Ũ_{pq} - h_{pq}) D_{pq}` shows `V` equals it;
5. the dual-frame relations turn this into the ansatz `V·∂ᵢu₀ = -F̃ᵢ`,
   `V·∂ᵢ∂ⱼu₀ = ½(Ũᵢⱼ - hᵢⱼ)`; the transported Günther identity gives
   `∂ᵢV·∂ⱼV = ∂ᵢF̃ⱼ + ∂ⱼF̃ᵢ + Ũᵢⱼ`; the product rule finishes.

## Main statements

* `gunther_perturbation` — Günther's perturbation theorem (Wassermann's Theorem B).
-/

open scoped BigOperators ContDiff
open Filter Topology NashEmbedding.Sobolev Matrix

noncomputable section

namespace NashEmbedding

variable {n N : ℕ}

/-! ## Free maps and their dual frame -/

/-- Index set of the frame: first derivatives, and second derivatives `∂ₚ∂_q` with `p ≤ q`.-/
abbrev FrameIdx (n : ℕ) := Fin n ⊕ {pq : Fin n × Fin n // pq.1 ≤ pq.2}

/-- The frame `{∂ᵢu} ∪ {∂ₚ∂_q u}_{p ≤ q}` of a map `u`.-/
def frame (u : (Fin n → ℝ) → (Fin N → ℝ)) : FrameIdx n → (Fin n → ℝ) → (Fin N → ℝ)
  | Sum.inl i => pderiv i u
  | Sum.inr pq => pderiv pq.1.1 (pderiv pq.1.2 u)

/-- A map is *free* if its frame is linearly independent at every point.-/
def IsFree (u : (Fin n → ℝ) → (Fin N → ℝ)) : Prop := IsPointwiseLinIndep (frame u)

/--
@isnad1 id=smoothpe.1h4v.s7.3661117abb01 from=translated src=- shape=61e38272 vocab=ed53aa37
-/
lemma frame_smoothPeriodic {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u) :
    ∀ k, SmoothPeriodic (frame u k)
  | Sum.inl i => hu.pderiv i
  | Sum.inr pq => (hu.pderiv pq.1.2).pderiv pq.1.1

/-- The second-derivative part of the dual frame, extended by `0` to pairs `p > q`.-/
def dualB (u : (Fin n → ℝ) → (Fin N → ℝ)) (p q : Fin n) : (Fin n → ℝ) → (Fin N → ℝ) :=
  if hpq : p ≤ q then dualFrame (frame u) (Sum.inr ⟨(p, q), hpq⟩) else 0

/-- The first-derivative part of the dual frame.-/
def dualA (u : (Fin n → ℝ) → (Fin N → ℝ)) (i : Fin n) : (Fin n → ℝ) → (Fin N → ℝ) :=
  dualFrame (frame u) (Sum.inl i)

/-! ## The base level and the size of a perturbation -/

/-- Base Sobolev level `r = ⌊n/2⌋ + 4`, so that `n/2 + 3 < r`.-/
def bLevel (n : ℕ) : ℕ := n / 2 + 4

/--
@isnad1 id=lt.0h1v.s5.8667db1496ab from=translated src=- shape=2018cbd7 vocab=dab5e4d1
-/
lemma bLevel_gt (n : ℕ) : 1 + (n : ℝ) / 2 < (bLevel n : ℝ) - 2 := by
  unfold bLevel
  have h : ((n / 2 : ℕ) : ℝ) ≥ (n : ℝ) / 2 - 1 / 2 := by
    have := Nat.div_add_mod n 2
    have hmod : (n % 2 : ℕ) ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt n (by norm_num))
    have h1 : (2 : ℝ) * ((n / 2 : ℕ) : ℝ) + ((n % 2 : ℕ) : ℝ) = n := by exact_mod_cast this
    have h2 : ((n % 2 : ℕ) : ℝ) ≤ 1 := by exact_mod_cast hmod
    linarith
  push_cast
  linarith

-- `bLevel n = n / 2 + 4` must not be unfolded by `whnf` (symbolic `Nat.div` is expensive).
attribute [irreducible] bLevel

/-- The `H^r` size of a matrix-valued perturbation: the sum over entries of the squared
`H^r` norms of the coefficient sequences.-/
def hSize (n : ℕ) (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : ℝ :=
  ∑ i, ∑ j, sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x i j : ℝ) : ℂ)))

/-! ## The momentum-side data -/

/-- The Günther data of `u₀` and `h`: coefficients of the dual frame and of `h`.-/
def bData (n : ℕ) (u₀ : (Fin n → ℝ) → (Fin N → ℝ))
    (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : GuntherData n N where
  a i := vcoeff n (dualA u₀ i)
  b p q := vcoeff n (dualB u₀ p q)
  h p q := stdFourierCoeff n (fun x => ((h x p q : ℝ) : ℂ))

/-- Realness of the data: all sequences are `conjReflect`-fixed.-/
structure GuntherData.Real (d : GuntherData n N) : Prop where
  a_real : ∀ i, VReal (d.a i)
  b_real : ∀ p q, VReal (d.b p q)
  h_real : ∀ p q, conjReflect (d.h p q) = d.h p q

/--
@isnad1 id=smoothpe.2h4v.s7.25337e12f7ce from=translated src=- shape=44916b15 vocab=6ef424d1
-/
lemma dualA_smoothPeriodic {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u)
    (hfree : IsFree u) (i : Fin n) : SmoothPeriodic (dualA u i) :=
  dualFrame_smoothPeriodic hfree (frame_smoothPeriodic hu) _

/--
@isnad1 id=smoothpe.2h5v.s7.24b622310c1a from=translated src=- shape=4003a687 vocab=53a7fbe0
-/
lemma dualB_smoothPeriodic {u : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u)
    (hfree : IsFree u) (p q : Fin n) : SmoothPeriodic (dualB u p q) := by
  unfold dualB
  split_ifs with hpq
  · exact dualFrame_smoothPeriodic hfree (frame_smoothPeriodic hu) _
  · exact ⟨contDiff_const, fun _ _ => rfl⟩

/--
@isnad1 id=smooth.4h4v.s6.dbf9c27afc18 from=translated src=- shape=5cc86345 vocab=b4043a2f
-/
lemma bData_smooth (hn : 0 < n) {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u₀)
    (hfree : IsFree u₀) {h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hh : SmoothPeriodic h) :
    (bData n u₀ h).Smooth where
  a_mem i k := (vcoeff_vrapid hn (dualA_smoothPeriodic hu hfree i)).vmem k
  b_mem p q k := (vcoeff_vrapid hn (dualB_smoothPeriodic hu hfree p q)).vmem k
  h_mem p q k := by
    have hs : ContDiff ℝ ∞ (fun x => ((h x p q : ℝ) : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp (contDiff_pi.mp (contDiff_pi.mp hh.smooth p) q)
    have hp : IsPeriodic2Pi (fun x => ((h x p q : ℝ) : ℂ)) := fun x k => by
      simp [hh.periodic x k]
    exact isRapidDecay_stdFourierCoeff hn hs hp k

/--
@isnad1 id=real.3h4v.s6.e43ee9641486 from=translated src=- shape=5251d7c1 vocab=894f5bb3
-/
lemma bData_real {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u₀)
    (hfree : IsFree u₀) {h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hh : SmoothPeriodic h) :
    (bData n u₀ h).Real where
  a_real i := vcoeff_vreal (dualA_smoothPeriodic hu hfree i)
  b_real p q := vcoeff_vreal (dualB_smoothPeriodic hu hfree p q)
  h_real p q := by
    have hc : Continuous (fun x => ((h x p q : ℝ) : ℂ)) :=
      Complex.continuous_ofReal.comp
        ((continuous_apply q).comp ((continuous_apply p).comp hh.smooth.continuous))
    exact conjReflect_stdFourierCoeff_of_real hc (fun x => by simp)

/-! ## Smallness: the constant term -/

/-- Multiplication by a scalar sequence, at level `s` with `2s > n` (MT2 componentwise).
@isnad1 id=le.4h5v.s6.f0ebad7ba555 from=translated src=- shape=c6ed56ef vocab=2f60f4e2
-/
lemma vecNormSq_smulSeq_le (hn : 0 < n) {s : ℝ} (hs : (n : ℝ) < 2 * s) {f : Seq n}
    (hf : MemSobolev n s f) {a : VecSeq n N} (ha : VMem n N s a) :
    vecNormSq n N s (smulSeq f a) ≤ mt2Const n s * sobolevNormSq n s f * vecNormSq n N s a := by
  unfold vecNormSq smulSeq
  calc ∑ α, sobolevNormSq n s (seqConv f (a α))
      ≤ ∑ α, mt2Const n s * sobolevNormSq n s f * sobolevNormSq n s (a α) :=
        Finset.sum_le_sum fun α _ => (second_multiplication_theorem_seq hn hs hf (ha α)).2
    _ = mt2Const n s * sobolevNormSq n s f * ∑ α, sobolevNormSq n s (a α) := by
        rw [Finset.mul_sum]

/--
@isnad1 id=vmem.4h5v.s6.f47de54cb0a2 from=translated src=- shape=eb36cd1f vocab=99ca8757
-/
lemma vmem_smulSeq (hn : 0 < n) {s : ℝ} (hs : (n : ℝ) < 2 * s) {f : Seq n}
    (hf : MemSobolev n s f) {a : VecSeq n N} (ha : VMem n N s a) : VMem n N s (smulSeq f a) :=
  fun α => (second_multiplication_theorem_seq hn hs hf (ha α)).1

/--
@isnad1 id=le.0h2v.s4.21fe2541f53d from=translated src=- shape=787c1379 vocab=d9fc819f
-/
lemma mt2Const_nonneg (n : ℕ) (s : ℝ) : 0 ≤ mt2Const n s := by
  unfold mt2Const sobolevEmbedConstSq
  exact mul_nonneg (mul_nonneg (by norm_num) (by positivity)) (tsum_nonneg fun _ => weight_nonneg _ _)

/-- The constant controlling `‖c‖²_(r)` in terms of `hSize`: depends on `u₀` only.-/
def cConst (n N : ℕ) (u₀ : (Fin n → ℝ) → (Fin N → ℝ)) : ℝ :=
  (pairs n).card * (mt2Const n (bLevel n) / 4)
    * ∑ pq ∈ pairs n, vecNormSq n N (bLevel n) (vcoeff n (dualB u₀ pq.1 pq.2))

/--
@isnad1 id=le.0h3v.s4.7c5a068142cf from=translated src=- shape=aaabd1d5 vocab=fa743820
-/
lemma cConst_nonneg (u₀ : (Fin n → ℝ) → (Fin N → ℝ)) : 0 ≤ cConst n N u₀ := by
  unfold cConst
  have h1 : 0 ≤ mt2Const n (bLevel n) := mt2Const_nonneg n _
  have h2 : 0 ≤ ∑ pq ∈ pairs n, vecNormSq n N (bLevel n) (vcoeff n (dualB u₀ pq.1 pq.2)) :=
    Finset.sum_nonneg fun _ _ => vecNormSq_nonneg _ _
  positivity

/-- `‖c‖²_(r) ≤ cConst · hSize h`.
@isnad1 id=le.4h4v.s7.a47f3804a7cf from=translated src=- shape=bcb90403 vocab=68c83a35
-/
lemma gC_bound (hn : 0 < n) {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u₀)
    (hfree : IsFree u₀) {h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hh : SmoothPeriodic h) :
    vecNormSq n N (bLevel n) (gC (bData n u₀ h)) ≤ cConst n N u₀ * hSize n h := by
  have hr : (n : ℝ) < 2 * ((bLevel n : ℕ) : ℝ) := by have := bLevel_gt n; linarith
  have hds := bData_smooth hn hu hfree hh
  have hK := mt2Const_nonneg n (bLevel n)
  -- each summand
  have hterm : ∀ pq ∈ pairs n,
      vecNormSq n N (bLevel n) (smulSeq (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m)
        ((bData n u₀ h).b pq.1 pq.2))
      ≤ (mt2Const n (bLevel n) / 4) * hSize n h * vecNormSq n N (bLevel n) ((bData n u₀ h).b pq.1 pq.2) := by
    intro pq _
    have hf : MemSobolev n (bLevel n) (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m) :=
      (hds.h_mem pq.1 pq.2 (bLevel n)).smul _
    have h1 := vecNormSq_smulSeq_le hn hr hf (hds.b_mem pq.1 pq.2 (bLevel n))
    rw [sobolevNormSq_smul] at h1
    have hh2 : (bData n u₀ h).h pq.1 pq.2 = stdFourierCoeff n (fun x => ((h x pq.1 pq.2 : ℝ) : ℂ)) := rfl
    rw [hh2] at h1
    have h2 : sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x pq.1 pq.2 : ℝ) : ℂ))) ≤ hSize n h := by
      unfold hSize
      obtain ⟨p, q⟩ := pq
      calc sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x p q : ℝ) : ℂ)))
          ≤ ∑ j, sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x p j : ℝ) : ℂ))) :=
            Finset.single_le_sum
              (f := fun j => sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x p j : ℝ) : ℂ))))
              (fun j _ => sobolevNormSq_nonneg _ _) (Finset.mem_univ q)
        _ ≤ ∑ i, ∑ j, sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x i j : ℝ) : ℂ))) :=
            Finset.single_le_sum
              (f := fun i => ∑ j, sobolevNormSq n (bLevel n) (stdFourierCoeff n (fun x => ((h x i j : ℝ) : ℂ))))
              (fun i _ => Finset.sum_nonneg fun j _ => sobolevNormSq_nonneg _ _) (Finset.mem_univ p)
    have hnorm : ‖(1 / 2 : ℂ)‖ ^ 2 = 1 / 4 := by norm_num
    rw [hnorm] at h1
    have hb0 := vecNormSq_nonneg ((bLevel n : ℕ) : ℝ) ((bData n u₀ h).b pq.1 pq.2)
    have h3 : mt2Const n (bLevel n) * (1 / 4 * sobolevNormSq n (bLevel n)
          (stdFourierCoeff n (fun x => ((h x pq.1 pq.2 : ℝ) : ℂ))))
        ≤ mt2Const n (bLevel n) / 4 * hSize n h := by nlinarith
    exact le_trans h1 (mul_le_mul_of_nonneg_right h3 hb0)
  have hmem : ∀ pq ∈ pairs n, VMem n N (bLevel n)
      (smulSeq (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m) ((bData n u₀ h).b pq.1 pq.2)) :=
    fun pq _ => vmem_smulSeq hn hr ((hds.h_mem pq.1 pq.2 (bLevel n)).smul _) (hds.b_mem pq.1 pq.2 (bLevel n))
  unfold gC
  rw [vecNormSq_neg]
  calc vecNormSq n N (bLevel n) (∑ pq ∈ pairs n, smulSeq (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m)
          ((bData n u₀ h).b pq.1 pq.2))
      ≤ (pairs n).card * ∑ pq ∈ pairs n, vecNormSq n N (bLevel n)
          (smulSeq (fun m => (1 / 2 : ℂ) * (bData n u₀ h).h pq.1 pq.2 m) ((bData n u₀ h).b pq.1 pq.2)) :=
        vecNormSq_finset_sum_le _ hmem
    _ ≤ (pairs n).card * ∑ pq ∈ pairs n,
          (mt2Const n (bLevel n) / 4) * hSize n h * vecNormSq n N (bLevel n) ((bData n u₀ h).b pq.1 pq.2) := by
        gcongr with pq hpq
        exact hterm pq hpq
    _ = cConst n N u₀ * hSize n h := by
        unfold cConst
        simp only [bData]
        rw [← Finset.mul_sum]
        ring

/--
@isnad1 id=le.0h2v.s4.031a3c728d00 from=translated src=- shape=9d3be7fe vocab=8ec60003
-/
lemma hSize_nonneg (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) : 0 ≤ hSize n h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sobolevNormSq_nonneg _ _

/-! ## Closure of rapid decay and of realness under the Günther operations -/

private lemma vrapid_vpartial {v : VecSeq n N} (hv : VRapid n N v) (i : Fin n) :
    VRapid n N (vpartial i v) := fun α => (hv α).partialCoeff i

private lemma vrapid_vlap {v : VecSeq n N} (hv : VRapid n N v) : VRapid n N (vlap v) :=
  fun α => ((hv α).laplacianCoeff).neg

private lemma isRapidDecay_dotConv (hn : 0 < n) {v w : VecSeq n N} (hv : VRapid n N v)
    (hw : VRapid n N w) : IsRapidDecay n (dotConv v w) :=
  IsRapidDecay.finset_sum Finset.univ (fun α _ => IsRapidDecay.seqConv hn (hv α) (hw α))

private lemma isRapidDecay_Fb (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (i : Fin n) :
    IsRapidDecay n (Fb i v v) :=
  (isRapidDecay_dotConv hn (vrapid_vlap hv) (vrapid_vpartial hv i)).resolventCoeff.neg

private lemma isRapidDecay_Ub (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (i j : Fin n) :
    IsRapidDecay n (Ub i j v v) := by
  have h1 : IsRapidDecay n (resolventCoeff (dotConv (vpartial i v) (vpartial j v))) :=
    (isRapidDecay_dotConv hn (vrapid_vpartial hv i) (vrapid_vpartial hv j)).resolventCoeff
  have h2 : IsRapidDecay n (fun m => (2 : ℂ) *
      resolventCoeff (dotConv (vlap v) (vpartial i (vpartial j v))) m) :=
    ((isRapidDecay_dotConv hn (vrapid_vlap hv)
      (vrapid_vpartial (vrapid_vpartial hv j) i)).resolventCoeff).const_mul 2
  have h3 : IsRapidDecay n (fun m => (2 : ℂ) * ∑ k, resolventCoeff
      (dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))) m) :=
    (IsRapidDecay.finset_sum Finset.univ (fun k _ =>
      (isRapidDecay_dotConv hn (vrapid_vpartial (vrapid_vpartial hv k) i)
        (vrapid_vpartial (vrapid_vpartial hv k) j)).resolventCoeff)).const_mul 2
  exact (h1.add h2).sub h3

private lemma conjReflect_neg' (a : Seq n) :
    conjReflect (fun m => -a m) = fun m => -conjReflect a m := by
  funext m; simp [conjReflect]

private lemma conjReflect_const_mul_of_real {c : ℂ} (hc : (starRingEnd ℂ) c = c) {a : Seq n}
    (ha : conjReflect a = a) : conjReflect (fun m => c * a m) = fun m => c * a m := by
  funext m
  have h := congrFun ha m
  simp only [conjReflect, map_mul] at *
  rw [hc, h]

private lemma conjReflect_seqConv_of_fixed {a b : Seq n} (ha : conjReflect a = a)
    (hb : conjReflect b = b) : conjReflect (seqConv a b) = seqConv a b := by
  rw [conjReflect_seqConv, ha, hb]

private lemma vreal_vpartial {v : VecSeq n N} (hv : VReal v) (i : Fin n) :
    VReal (vpartial i v) := fun α => by
  show conjReflect (partialCoeff i (v α)) = partialCoeff i (v α)
  rw [conjReflect_partialCoeff, hv α]

private lemma vreal_vlap {v : VecSeq n N} (hv : VReal v) : VReal (vlap v) := fun α => by
  show conjReflect (fun m => -(laplacianCoeff (v α) m)) = _
  rw [conjReflect_neg', conjReflect_laplacianCoeff, hv α]
  rfl

private lemma conjReflect_dotConv {v w : VecSeq n N} (hv : VReal v) (hw : VReal w) :
    conjReflect (dotConv v w) = dotConv v w := by
  show conjReflect (fun m => ∑ α, seqConv (v α) (w α) m) = _
  rw [conjReflect_finset_sum]
  funext m
  show ∑ α, conjReflect (seqConv (v α) (w α)) m = ∑ α, seqConv (v α) (w α) m
  exact Finset.sum_congr rfl fun α _ =>
    congrFun (conjReflect_seqConv_of_fixed (hv α) (hw α)) m

private lemma conjReflect_resolvent_dotConv {v w : VecSeq n N} (hv : VReal v) (hw : VReal w) :
    conjReflect (resolventCoeff (dotConv v w)) = resolventCoeff (dotConv v w) := by
  rw [conjReflect_resolventCoeff, conjReflect_dotConv hv hw]

private lemma conjReflect_Fb {v : VecSeq n N} (hv : VReal v) (i : Fin n) :
    conjReflect (Fb i v v) = Fb i v v := by
  show conjReflect (fun m => -(resolventCoeff (dotConv (vlap v) (vpartial i v)) m)) = _
  rw [conjReflect_neg', conjReflect_resolvent_dotConv (vreal_vlap hv) (vreal_vpartial hv i)]
  rfl

private lemma conjReflect_Ub {v : VecSeq n N} (hv : VReal v) (i j : Fin n) :
    conjReflect (Ub i j v v) = Ub i j v v := by
  have hc2 : (starRingEnd ℂ) 2 = 2 := map_ofNat _ 2
  have h1 := conjReflect_resolvent_dotConv (vreal_vpartial hv i) (vreal_vpartial hv j)
  have h2 := conjReflect_const_mul_of_real hc2
    (conjReflect_resolvent_dotConv (vreal_vlap hv) (vreal_vpartial (vreal_vpartial hv j) i))
  have h3 : conjReflect (fun m => ∑ k, resolventCoeff
      (dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))) m)
      = fun m => ∑ k, resolventCoeff
      (dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))) m := by
    rw [conjReflect_finset_sum]
    funext m
    exact Finset.sum_congr rfl fun k _ => congrFun
      (conjReflect_resolvent_dotConv (vreal_vpartial (vreal_vpartial hv k) i)
        (vreal_vpartial (vreal_vpartial hv k) j)) m
  have h4 := conjReflect_const_mul_of_real hc2 h3
  show conjReflect (fun m => (resolventCoeff (dotConv (vpartial i v) (vpartial j v)) m
      + (2 : ℂ) * resolventCoeff (dotConv (vlap v) (vpartial i (vpartial j v))) m)
      - (2 : ℂ) * ∑ k, resolventCoeff
          (dotConv (vpartial i (vpartial k v)) (vpartial j (vpartial k v))) m) = _
  rw [conjReflect_sub, conjReflect_add, h1, h2, h4]
  rfl

/-! ## Realness is preserved by the iteration -/

/--
@isnad1 id=vreal.0h2v.s5.4e0a31b82879 from=translated src=- shape=887242f4 vocab=312f6a96
-/
lemma vreal_zero : VReal (0 : VecSeq n N) := fun _ => by funext m; simp [conjReflect]

/--
@isnad1 id=vreal.2h4v.s6.60e86d27217c from=translated src=- shape=a7eadc1c vocab=e3482aeb
-/
lemma vreal_gT {d : GuntherData n N} (hd : d.Real) {v : VecSeq n N} (hv : VReal v) :
    VReal (gC d + gB d v v) := by
  have hhalf : (starRingEnd ℂ) (1 / 2 : ℂ) = 1 / 2 := by rw [map_div₀, map_one, map_ofNat]
  intro α
  have hform : (gC d + gB d v v) α = fun m =>
      -(∑ pq ∈ pairs n, seqConv (fun m => (1 / 2 : ℂ) * d.h pq.1 pq.2 m) (d.b pq.1 pq.2 α) m)
      + (-(∑ i, seqConv (Fb i v v) (d.a i α) m)
         + ∑ pq ∈ pairs n,
            seqConv (fun m => (1 / 2 : ℂ) * Ub pq.1 pq.2 v v m) (d.b pq.1 pq.2 α) m) := by
    funext m
    simp [gC, gB, smulSeq, Finset.sum_apply]
  have hs1 : conjReflect (fun m =>
      ∑ pq ∈ pairs n, seqConv (fun m => (1 / 2 : ℂ) * d.h pq.1 pq.2 m) (d.b pq.1 pq.2 α) m)
      = fun m => ∑ pq ∈ pairs n,
        seqConv (fun m => (1 / 2 : ℂ) * d.h pq.1 pq.2 m) (d.b pq.1 pq.2 α) m := by
    rw [conjReflect_finset_sum]
    funext m
    exact Finset.sum_congr rfl fun pq _ => congrFun (conjReflect_seqConv_of_fixed
      (conjReflect_const_mul_of_real hhalf (hd.h_real pq.1 pq.2)) (hd.b_real pq.1 pq.2 α)) m
  have hs2 : conjReflect (fun m => ∑ i, seqConv (Fb i v v) (d.a i α) m)
      = fun m => ∑ i, seqConv (Fb i v v) (d.a i α) m := by
    rw [conjReflect_finset_sum]
    funext m
    exact Finset.sum_congr rfl fun i _ => congrFun
      (conjReflect_seqConv_of_fixed (conjReflect_Fb hv i) (hd.a_real i α)) m
  have hs3 : conjReflect (fun m =>
      ∑ pq ∈ pairs n, seqConv (fun m => (1 / 2 : ℂ) * Ub pq.1 pq.2 v v m) (d.b pq.1 pq.2 α) m)
      = fun m => ∑ pq ∈ pairs n,
        seqConv (fun m => (1 / 2 : ℂ) * Ub pq.1 pq.2 v v m) (d.b pq.1 pq.2 α) m := by
    rw [conjReflect_finset_sum]
    funext m
    exact Finset.sum_congr rfl fun pq _ => congrFun (conjReflect_seqConv_of_fixed
      (conjReflect_const_mul_of_real hhalf (conjReflect_Ub hv pq.1 pq.2))
      (hd.b_real pq.1 pq.2 α)) m
  rw [hform, conjReflect_add, conjReflect_neg', hs1, conjReflect_add, conjReflect_neg', hs2, hs3]

/--
@isnad1 id=vreal.2h4v.s6.e1d9aa898b5a from=translated src=- shape=0ed50e32 vocab=aca43e28
-/
lemma vreal_of_tendsto {u : ℕ → VecSeq n N} {a : VecSeq n N} (hu : ∀ p, VReal (u p))
    (hlim : ∀ α m, Tendsto (fun p => u p α m) atTop (𝓝 (a α m))) : VReal a := by
  intro α
  funext m
  -- `conjReflect (u p α) m = u p α m` for all `p`; pass to the limit
  have h1 : Tendsto (fun p => conjReflect (u p α) m) atTop (𝓝 (conjReflect (a α) m)) := by
    unfold conjReflect
    exact (Complex.continuous_conj.tendsto _).comp (hlim α (-m))
  have h2 : (fun p => conjReflect (u p α) m) = fun p => u p α m := by
    funext p; rw [hu p α]
  rw [h2] at h1
  exact tendsto_nhds_unique h1 (hlim α m)

/-! ## Position-space pieces of the fixed point -/

/-- Real synthesis of a scalar sequence.-/
def ssynth (n : ℕ) (f : Seq n) : (Fin n → ℝ) → ℝ := fun x => (fourierSynthesis n f x).re

private lemma ssynth_smoothPeriodic (hn : 0 < n) {f : Seq n} (hf : IsRapidDecay n f) :
    SmoothPeriodic (ssynth n f) := by
  constructor
  · have h := Complex.reCLM.contDiff.comp (fourierSynthesis_contDiff hn hf)
    unfold ssynth
    exact h
  · intro x k
    unfold ssynth
    rw [fourierSynthesis_isPeriodic2Pi x k]

/-- The position-space `F̃ᵢ`.-/
def Ftil (n : ℕ) (v : VecSeq n N) (i : Fin n) : (Fin n → ℝ) → ℝ := ssynth n (Fb i v v)

/-- The position-space `Ũᵢⱼ`.-/
def Util (n : ℕ) (v : VecSeq n N) (i j : Fin n) : (Fin n → ℝ) → ℝ := ssynth n (Ub i j v v)

/-- The position-space right-hand side `W = -∑ᵢ F̃ᵢ Dᵢ + ∑_{p≤q} ½(Ũ_{pq} - h_{pq}) D_{pq}`.-/
def Wfun (n : ℕ) (u₀ : (Fin n → ℝ) → (Fin N → ℝ)) (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ)
    (v : VecSeq n N) : (Fin n → ℝ) → (Fin N → ℝ) :=
  fun x => -(∑ i, Ftil n v i x • dualA u₀ i x)
    + ∑ pq ∈ pairs n, ((1 / 2 : ℝ) * (Util n v pq.1 pq.2 x - h x pq.1 pq.2)) • dualB u₀ pq.1 pq.2 x

/--
@isnad1 id=smoothpe.3h4v.s5.50a2a78cd399 from=translated src=- shape=96731a08 vocab=b55afa61
-/
lemma Ftil_smoothPeriodic (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v)
    (i : Fin n) : SmoothPeriodic (Ftil n v i) :=
  ssynth_smoothPeriodic hn (isRapidDecay_Fb hn hv i)

/--
@isnad1 id=smoothpe.3h5v.s5.431faf010c65 from=translated src=- shape=8bff4bf5 vocab=4a8e5dd4
-/
lemma Util_smoothPeriodic (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v)
    (i j : Fin n) : SmoothPeriodic (Util n v i j) :=
  ssynth_smoothPeriodic hn (isRapidDecay_Ub hn hv i j)

/--
@isnad1 id=eq.2h5v.s5.3d040f6ffb98 from=translated src=- shape=8e80ab85 vocab=8f5f46b9
-/
lemma Util_symm (hn : 0 < n) {v : VecSeq n N} (hv : VRapid n N v) (i j : Fin n) :
    Util n v i j = Util n v j i := by
  unfold Util; rw [Ub_symm hn hv i j]

/--
@isnad1 id=smoothpe.6h5v.s7.a0d990677b60 from=translated src=- shape=a016a625 vocab=a0e71c99
-/
lemma Wfun_smoothPeriodic (hn : 0 < n) {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hu : SmoothPeriodic u₀)
    (hfree : IsFree u₀) {h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ} (hh : SmoothPeriodic h)
    {v : VecSeq n N} (hv : VRapid n N v) (hr : VReal v) :
    SmoothPeriodic (Wfun n u₀ h v) := by
  have hF : ∀ i, SmoothPeriodic (Ftil n v i) := fun i => Ftil_smoothPeriodic hn hv hr i
  have hU : ∀ p q, SmoothPeriodic (Util n v p q) := fun p q => Util_smoothPeriodic hn hv hr p q
  have hA : ∀ i, SmoothPeriodic (dualA u₀ i) := fun i => dualA_smoothPeriodic hu hfree i
  have hB : ∀ p q, SmoothPeriodic (dualB u₀ p q) := fun p q => dualB_smoothPeriodic hu hfree p q
  have hhc : ∀ p q : Fin n, ContDiff ℝ ∞ (fun x => h x p q) := fun p q =>
    contDiff_pi.mp (contDiff_pi.mp hh.smooth p) q
  constructor
  · unfold Wfun
    refine ContDiff.add (ContDiff.neg (ContDiff.sum fun i _ => ?_)) (ContDiff.sum fun pq _ => ?_)
    · exact ContDiff.smul (f := fun x => Ftil n v i x) (g := fun x => dualA u₀ i x)
        (hF i).smooth (hA i).smooth
    · exact ContDiff.smul (f := fun x => (1 / 2 : ℝ) * (Util n v pq.1 pq.2 x - h x pq.1 pq.2))
        (g := fun x => dualB u₀ pq.1 pq.2 x)
        (contDiff_const.mul ((hU pq.1 pq.2).smooth.sub (hhc pq.1 pq.2))) (hB pq.1 pq.2).smooth
  · intro x k
    unfold Wfun
    congr 1
    · congr 1
      exact Finset.sum_congr rfl fun i _ => by
        rw [(hF i).periodic x k, (hA i).periodic x k]
    · exact Finset.sum_congr rfl fun pq _ => by
        rw [(hU pq.1 pq.2).periodic x k, (hB pq.1 pq.2).periodic x k, hh.periodic x k]

/-! ## The ansatz from the dual frame -/

/-- `W · ∂ᵢu₀ = -F̃ᵢ`.
@isnad1 id=eq.1h7v.s7.e428582cdf4e from=translated src=- shape=febda177 vocab=abe01fee
-/
lemma Wfun_dot_pderiv {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hfree : IsFree u₀)
    (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : VecSeq n N) (i : Fin n) (x : Fin n → ℝ) :
    Wfun n u₀ h v x ⬝ᵥ pderiv i u₀ x = -Ftil n v i x := by
  have hd := dualFrame_dotProduct hfree
  have hA : ∀ k, dualA u₀ k x ⬝ᵥ pderiv i u₀ x = if k = i then 1 else 0 := fun k => by
    have := hd (Sum.inl k) (Sum.inl i) x
    simpa [dualA, frame] using this
  have hB : ∀ pq ∈ pairs n, dualB u₀ pq.1 pq.2 x ⬝ᵥ pderiv i u₀ x = 0 := fun pq hpq => by
    have hle : pq.1 ≤ pq.2 := (Finset.mem_filter.mp hpq).2
    have := hd (Sum.inr ⟨pq, hle⟩) (Sum.inl i) x
    simp only [frame, reduceCtorEq, ite_false] at this
    simp [dualB, hle, this]
  unfold Wfun
  rw [add_dotProduct, neg_dotProduct, sum_dotProduct, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, hA, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ite_true]
  rw [Finset.sum_eq_zero (fun pq hpq => by rw [hB pq hpq, mul_zero]), add_zero]

/-- `W · ∂ₚ∂_q u₀ = ½(Ũ_{pq} - h_{pq})` for `p ≤ q`.
@isnad1 id=eq.2h8v.s7.623a7f94709c from=translated src=- shape=d9279dff vocab=27bf89dc
-/
lemma Wfun_dot_pderiv_pderiv {u₀ : (Fin n → ℝ) → (Fin N → ℝ)} (hfree : IsFree u₀)
    (h : (Fin n → ℝ) → Matrix (Fin n) (Fin n) ℝ) (v : VecSeq n N) {p q : Fin n} (hpq : p ≤ q)
    (x : Fin n → ℝ) :
    Wfun n u₀ h v x ⬝ᵥ pderiv p (pderiv q u₀) x = (1 / 2 : ℝ) * (Util n v p q x - h x p q) := by
  have hd := dualFrame_dotProduct hfree
  have hA : ∀ k, dualA u₀ k x ⬝ᵥ pderiv p (pderiv q u₀) x = 0 := fun k => by
    have := hd (Sum.inl k) (Sum.inr ⟨(p, q), hpq⟩) x
    simpa [dualA, frame] using this
  have hB : ∀ pq ∈ pairs n, dualB u₀ pq.1 pq.2 x ⬝ᵥ pderiv p (pderiv q u₀) x
      = if pq = (p, q) then 1 else 0 := fun pq hpq' => by
    have hle : pq.1 ≤ pq.2 := (Finset.mem_filter.mp hpq').2
    have := hd (Sum.inr ⟨pq, hle⟩) (Sum.inr ⟨(p, q), hpq⟩) x
    simp only [frame, Sum.inr.injEq, Subtype.mk.injEq] at this
    simp [dualB, hle, this]
  have hmem : (p, q) ∈ pairs n := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpq⟩
  unfold Wfun
  rw [add_dotProduct, neg_dotProduct, sum_dotProduct, sum_dotProduct]
  simp only [smul_dotProduct, smul_eq_mul, hA, mul_zero, Finset.sum_const_zero, neg_zero, zero_add]
  rw [Finset.sum_congr rfl fun pq hpq' => by rw [hB pq hpq']]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq' (pairs n) (p, q)]
  simp [hmem]

/-- `∂ᵢ(-f) = -∂ᵢf` for smooth scalar `f`.
@isnad1 id=eq.0h3v.s6.2a8a3fe940ec from=translated src=- shape=8083f581 vocab=a5214882
-/
lemma pderiv_neg (f : (Fin n → ℝ) → ℝ) (i : Fin n) :
    pderiv i (fun y => -f y) = fun y => -pderiv i f y := by
  funext y
  unfold pderiv
  rw [fderiv_fun_neg]
  simp

/-! ## Theorem B -/

end NashEmbedding

end
