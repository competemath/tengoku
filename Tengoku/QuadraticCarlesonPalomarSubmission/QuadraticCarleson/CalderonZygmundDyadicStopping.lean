/-
Copyright (c) 2026 Quadratic Carleson formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Quadratic Carleson formalization contributors
-/

import Tengoku.QuadraticCarlesonPalomarSubmission.QuadraticCarleson.CalderonZygmundDecomposition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dyadic stopping intervals for the Calderón--Zygmund decomposition

This module supplies an explicit global dyadic grid and proves the quantitative
parent/child facts behind the height-one stopping rule.  In particular, a
child of a good parent has `‖f‖`-average at most two.
-/

open Filter MeasureTheory Set
open scoped ENNReal BigOperators Function Topology

namespace QuadraticCarleson
namespace CalderonZygmundDyadicStopping

set_option autoImplicit false

noncomputable section

/-- Length of a depth-`n` cell in the dyadic grid with root length `L`.-/
def dyadicLength (L : ℝ) (n : ℕ) : ℝ := L / (2 : ℝ) ^ n

/-- The half-open dyadic cell with depth `n` and integer address `q`.-/
def dyadicInterval (L : ℝ) (n : ℕ) (q : ℤ) : Set ℝ :=
  Ico ((q : ℝ) * dyadicLength L n) (((q : ℝ) + 1) * dyadicLength L n)

/--
@isnad1 id=lt.1h2v.s4.8385a79acb20 from=translated src=- shape=9141f3a7 vocab=bf6a8eea
-/
theorem dyadicLength_pos {L : ℝ} (hL : 0 < L) (n : ℕ) :
    0 < dyadicLength L n := by
  exact div_pos hL (by positivity)

/--
@isnad1 id=eq.0h2v.s5.4c64f6682165 from=translated src=- shape=92837d39 vocab=6ee5f8bb
-/
theorem dyadicLength_succ (L : ℝ) (n : ℕ) :
    dyadicLength L (n + 1) = dyadicLength L n / 2 := by
  simp [dyadicLength, pow_succ]
  ring

/--
@isnad1 id=eq.0h3v.s5.53b41057bff9 from=translated src=- shape=950917ee vocab=c2ae8334
-/
@[simp] theorem volume_dyadicInterval (L : ℝ) (n : ℕ) (q : ℤ) :
    volume (dyadicInterval L n q) = ENNReal.ofReal (dyadicLength L n) := by
  rw [dyadicInterval, Real.volume_Ico]
  congr 1
  ring

/--
@isnad1 id=eq.1h3v.s5.59b53d587e0c from=translated src=- shape=0170a868 vocab=ff4513d3
-/
theorem volumeReal_dyadicInterval {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (q : ℤ) :
    volume.real (dyadicInterval L n q) = dyadicLength L n := by
  rw [Measure.real, volume_dyadicInterval]
  exact ENNReal.toReal_ofReal (div_nonneg hL (by positivity))

/--
@isnad1 id=le.1h3v.s5.65d6b976972d from=translated src=- shape=cc69a8d7 vocab=c97f9c24
-/
theorem leftChild_subset {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (q : ℤ) :
    dyadicInterval L (n + 1) (2 * q) ⊆ dyadicInterval L n q := by
  intro x hx
  simp only [dyadicInterval, mem_Ico] at hx ⊢
  rw [dyadicLength_succ] at hx
  have hd : 0 ≤ dyadicLength L n := div_nonneg hL (by positivity)
  push_cast at hx ⊢
  constructor <;> nlinarith

/--
@isnad1 id=le.1h3v.s6.c1a2f0a54dc1 from=translated src=- shape=1d291f2c vocab=c97f9c24
-/
theorem rightChild_subset {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (q : ℤ) :
    dyadicInterval L (n + 1) (2 * q + 1) ⊆ dyadicInterval L n q := by
  intro x hx
  simp only [dyadicInterval, mem_Ico] at hx ⊢
  rw [dyadicLength_succ] at hx
  have hd : 0 ≤ dyadicLength L n := div_nonneg hL (by positivity)
  push_cast at hx ⊢
  constructor <;> nlinarith

/--
@isnad1 id=disjoint.1h3v.s6.50bf2aa8cd42 from=translated src=- shape=ce3f7e69 vocab=91e9c676
-/
theorem left_right_children_disjoint {L : ℝ} (hL : 0 ≤ L) (n : ℕ) (q : ℤ) :
    Disjoint (dyadicInterval L (n + 1) (2 * q))
      (dyadicInterval L (n + 1) (2 * q + 1)) := by
  apply Set.disjoint_left.2
  intro x hxleft hxright
  simp only [dyadicInterval, mem_Ico] at hxleft hxright
  rw [dyadicLength_succ] at hxleft hxright
  have hd : 0 ≤ dyadicLength L n := div_nonneg hL (by positivity)
  push_cast at hxleft hxright
  linarith

/-- A coarse dyadic length is an integral power-of-two multiple of every
finer dyadic length.
@isnad1 id=eq.1h3v.s5.5b277f66ef89 from=translated src=- shape=beb22464 vocab=455e1277
-/
theorem dyadicLength_eq_pow_mul {L : ℝ} {n m : ℕ} (hnm : n ≤ m) :
    dyadicLength L n = (2 : ℝ) ^ (m - n) * dyadicLength L m := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hnm
  unfold dyadicLength
  rw [Nat.add_sub_cancel_left]
  rw [pow_add]
  field_simp

/-- At different depths, a fine dyadic cell is either contained in a given
coarser cell or disjoint from it.  This is the arithmetic laminarity property
of the half-open global dyadic grid.
@isnad1 id=or.2h5v.s6.1d30bb501317 from=translated src=- shape=d953a538 vocab=2a7a9c24
-/
theorem dyadicInterval_subset_or_disjoint_of_le {L : ℝ} (hL : 0 < L)
    {n m : ℕ} (hnm : n ≤ m) (q r : ℤ) :
    dyadicInterval L m r ⊆ dyadicInterval L n q ∨
      Disjoint (dyadicInterval L m r) (dyadicInterval L n q) := by
  let D : ℤ := (2 : ℕ) ^ (m - n)
  have hDpos : 0 < D := by
    dsimp [D]
    exact_mod_cast (pow_pos (by decide : 0 < (2 : ℕ)) (m - n))
  have hlen := dyadicLength_eq_pow_mul (L := L) hnm
  have hcastD : (D : ℝ) = (2 : ℝ) ^ (m - n) := by
    simp [D]
  have hdm : 0 < dyadicLength L m := dyadicLength_pos hL m
  by_cases hrange : q * D ≤ r ∧ r < (q + 1) * D
  · left
    intro x hx
    simp only [dyadicInterval, mem_Ico] at hx ⊢
    have hloZ : q * D ≤ r := hrange.1
    have hhiZ : r + 1 ≤ (q + 1) * D := by omega
    have hloR : ((q * D : ℤ) : ℝ) * dyadicLength L m ≤
        (r : ℝ) * dyadicLength L m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hloZ) hdm.le
    have hhiR : ((r + 1 : ℤ) : ℝ) * dyadicLength L m ≤
        (((q + 1) * D : ℤ) : ℝ) * dyadicLength L m :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hhiZ) hdm.le
    rw [hlen, ← hcastD]
    push_cast at hloR hhiR ⊢
    constructor <;> nlinarith
  · right
    rw [not_and_or] at hrange
    rcases hrange with hlo | hhi
    · apply Set.disjoint_left.2
      intro x hxf hxc
      simp only [dyadicInterval, mem_Ico] at hxf hxc
      have hz : r + 1 ≤ q * D := by omega
      have hzR : ((r + 1 : ℤ) : ℝ) * dyadicLength L m ≤
          ((q * D : ℤ) : ℝ) * dyadicLength L m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hdm.le
      rw [hlen, ← hcastD] at hxc
      push_cast at hzR hxc
      nlinarith
    · apply Set.disjoint_left.2
      intro x hxf hxc
      simp only [dyadicInterval, mem_Ico] at hxf hxc
      have hz : (q + 1) * D ≤ r := by omega
      have hzR : (((q + 1) * D : ℤ) : ℝ) * dyadicLength L m ≤
          (r : ℝ) * dyadicLength L m :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hdm.le
      rw [hlen, ← hcastD] at hxc
      push_cast at hzR hxc
      nlinarith

/-- Any two cells in the global dyadic grid are nested or disjoint.
@isnad1 id=or.1h5v.s6.8297aa78a2c8 from=translated src=- shape=d8fcf618 vocab=2a7a9c24
-/
theorem dyadicInterval_laminar {L : ℝ} (hL : 0 < L)
    (n : ℕ) (q : ℤ) (m : ℕ) (r : ℤ) :
    dyadicInterval L n q ⊆ dyadicInterval L m r ∨
      dyadicInterval L m r ⊆ dyadicInterval L n q ∨
      Disjoint (dyadicInterval L n q) (dyadicInterval L m r) := by
  rcases le_total n m with hnm | hmn
  · rcases dyadicInterval_subset_or_disjoint_of_le hL hnm q r with hsub | hdis
    · exact Or.inr (Or.inl hsub)
    · exact Or.inr (Or.inr hdis.symm)
  · rcases dyadicInterval_subset_or_disjoint_of_le hL hmn r q with hsub | hdis
    · exact Or.inl hsub
    · exact Or.inr (Or.inr hdis)

/-- Distinct cells at one fixed depth are disjoint.
@isnad1 id=disjoint.2h4v.s5.1d7f33919f28 from=translated src=- shape=4abb990f vocab=b203d407
-/
theorem dyadicInterval_disjoint_of_sameDepth {L : ℝ} (hL : 0 < L)
    (n : ℕ) {q r : ℤ} (hqr : q ≠ r) :
    Disjoint (dyadicInterval L n q) (dyadicInterval L n r) := by
  apply Set.disjoint_left.2
  intro x hxq hxr
  simp only [dyadicInterval, mem_Ico] at hxq hxr
  have hd : 0 < dyadicLength L n := dyadicLength_pos hL n
  rcases lt_or_gt_of_ne hqr with hlt | hgt
  · have hz : q + 1 ≤ r := by omega
    have hzR : ((q + 1 : ℤ) : ℝ) * dyadicLength L n ≤
        (r : ℝ) * dyadicLength L n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hd.le
    push_cast at hzR
    linarith
  · have hz : r + 1 ≤ q := by omega
    have hzR : ((r + 1 : ℤ) : ℝ) * dyadicLength L n ≤
        (q : ℝ) * dyadicLength L n :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hz) hd.le
    push_cast at hzR
    linarith

/--
@isnad1 id=nonempty.1h3v.s4.a95f58bd22f7 from=translated src=- shape=04e54a36 vocab=03e4d183
-/
theorem dyadicInterval_nonempty {L : ℝ} (hL : 0 < L) (n : ℕ) (q : ℤ) :
    (dyadicInterval L n q).Nonempty := by
  rw [dyadicInterval, nonempty_Ico]
  have hd := dyadicLength_pos hL n
  nlinarith

/-- The data-dependent root length.  It is strictly larger than the global
`L¹` mass, so every depth-zero cell has average at most one.-/
def rootLength (f : ℝ → ℂ) : ℝ :=
  (∫ x, ‖f x‖) + 1

/--
@isnad1 id=lt.0h1v.s3.cc9307ca60cc from=translated src=- shape=e456648f vocab=5c8ab4cc
-/
theorem rootLength_pos {f : ℝ → ℂ} : 0 < rootLength f := by
  have hmass : 0 ≤ ∫ x, ‖f x‖ :=
    integral_nonneg_of_ae (μ := volume)
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  unfold rootLength
  linarith

/-- The scalar `‖f‖` average on a dyadic cell.-/
def dyadicNormAverage (f : ℝ → ℂ) (L : ℝ) (n : ℕ) (q : ℤ) : ℝ :=
  ⨍ x in dyadicInterval L n q, ‖f x‖

/--
@isnad1 id=eq.1h4v.s6.168a4bd0790f from=translated src=- shape=a61f4f96 vocab=4dfec30f
-/
theorem dyadicNormAverage_eq {f : ℝ → ℂ} {L : ℝ} (hL : 0 < L)
    (n : ℕ) (q : ℤ) :
    dyadicNormAverage f L n q =
      (∫ x in dyadicInterval L n q, ‖f x‖) / dyadicLength L n := by
  rw [dyadicNormAverage, setAverage_eq, volumeReal_dyadicInterval hL.le]
  rw [div_eq_inv_mul]
  simp only [smul_eq_mul]

/--
@isnad1 id=le.1h2v.s6.815fa9a26a69 from=translated src=- shape=38ebe26b vocab=c5ac3ed4
-/
theorem root_dyadicNormAverage_le_one {f : ℝ → ℂ} (hf : Integrable f) (q : ℤ) :
    dyadicNormAverage f (rootLength f) 0 q ≤ 1 := by
  have hlocal : (∫ x in dyadicInterval (rootLength f) 0 q, ‖f x‖) ≤ ∫ x, ‖f x‖ :=
    setIntegral_le_integral hf.norm (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  rw [dyadicNormAverage_eq rootLength_pos, dyadicLength]
  simp only [pow_zero, div_one]
  have hmass : 0 ≤ ∫ x, ‖f x‖ :=
    integral_nonneg_of_ae (μ := volume)
      (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  rw [div_le_one (by unfold rootLength; linarith)]
  exact hlocal.trans (by unfold rootLength; linarith)

private theorem child_integral_le_parent
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} {n : ℕ} {q child : ℤ}
    (hsub : dyadicInterval L (n + 1) child ⊆ dyadicInterval L n q) :
    (∫ x in dyadicInterval L (n + 1) child, ‖f x‖) ≤
      ∫ x in dyadicInterval L n q, ‖f x‖ := by
  apply setIntegral_mono_set hf.norm.integrableOn
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  exact Filter.Eventually.of_forall hsub

/-- Quantitative stopping lemma: the left child of a height-one good parent
has average at most two.
@isnad1 id=le.3h4v.s6.5f076ad4c599 from=translated src=- shape=b8a317b7 vocab=0dd29618
-/
theorem leftChild_dyadicNormAverage_le_two
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} (hL : 0 < L)
    {n : ℕ} {q : ℤ} (hparent : dyadicNormAverage f L n q ≤ 1) :
    dyadicNormAverage f L (n + 1) (2 * q) ≤ 2 := by
  have hmono := child_integral_le_parent hf (leftChild_subset hL.le n q)
  rw [dyadicNormAverage_eq hL] at hparent
  rw [dyadicNormAverage_eq hL, dyadicLength_succ]
  have hlen : 0 < dyadicLength L n := dyadicLength_pos hL n
  rw [div_le_iff₀ (half_pos hlen)]
  rw [div_le_iff₀ hlen] at hparent
  nlinarith

/-- Quantitative stopping lemma for the right child.
@isnad1 id=le.3h4v.s6.432d4396794f from=translated src=- shape=92930f53 vocab=0dd29618
-/
theorem rightChild_dyadicNormAverage_le_two
    {f : ℝ → ℂ} (hf : Integrable f) {L : ℝ} (hL : 0 < L)
    {n : ℕ} {q : ℤ} (hparent : dyadicNormAverage f L n q ≤ 1) :
    dyadicNormAverage f L (n + 1) (2 * q + 1) ≤ 2 := by
  have hmono := child_integral_le_parent hf (rightChild_subset hL.le n q)
  rw [dyadicNormAverage_eq hL] at hparent
  rw [dyadicNormAverage_eq hL, dyadicLength_succ]
  have hlen : 0 < dyadicLength L n := dyadicLength_pos hL n
  rw [div_le_iff₀ (half_pos hlen)]
  rw [div_le_iff₀ hlen] at hparent
  nlinarith

/-! ## The intrinsic first-crossing stopping predicate -/

/-- An address in the global dyadic forest.  Every tree starts at a depth-zero
cell, and `left`/`right` record successive bisections.-/
inductive DyadicNode where
  | root (q : ℤ)
  | left (parent : DyadicNode)
  | right (parent : DyadicNode)
  deriving DecidableEq, Encodable

/-- Depth of a dyadic node.-/
def DyadicNode.depth : DyadicNode → ℕ
  | .root _ => 0
  | .left p => p.depth + 1
  | .right p => p.depth + 1

/-- Integer address of a dyadic node in the global grid at its depth.-/
def DyadicNode.index : DyadicNode → ℤ
  | .root q => q
  | .left p => 2 * p.index
  | .right p => 2 * p.index + 1

/--
@isnad1 id=injectiv.0h0v.s3.ab68cf1e33e2 from=translated src=- shape=3828e7c2 vocab=e1e730ad
-/
theorem DyadicNode.depth_index_injective :
    Function.Injective (fun p : DyadicNode ↦ (p.depth, p.index)) := by
  intro p
  induction p with
  | root q =>
      intro r h
      cases r with
      | root s => simp only [depth, index, Prod.mk.injEq] at h; simp [h.2]
      | left r => simp [depth] at h
      | right r => simp [depth] at h
  | left p ih =>
      intro r h
      cases r with
      | root s => simp [depth] at h
      | left r =>
          simp only [depth, index, Prod.mk.injEq] at h
          have hindex : p.index = r.index :=
            mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) h.2
          have hparent : p = r := ih (Prod.ext (Nat.add_right_cancel h.1) hindex)
          simp [hparent]
      | right r =>
          simp only [depth, index, Prod.mk.injEq] at h
          omega
  | right p ih =>
      intro r h
      cases r with
      | root s => simp [depth] at h
      | left r =>
          simp only [depth, index, Prod.mk.injEq] at h
          omega
      | right r =>
          simp only [depth, index, Prod.mk.injEq] at h
          have hmul : 2 * p.index = 2 * r.index := by omega
          have hindex : p.index = r.index :=
            mul_left_cancel₀ (by norm_num : (2 : ℤ) ≠ 0) hmul
          have hparent : p = r := ih (Prod.ext (Nat.add_right_cancel h.1) hindex)
          simp [hparent]

/-- The half-open interval represented by a node.-/
def DyadicNode.interval (L : ℝ) (p : DyadicNode) : Set ℝ :=
  dyadicInterval L p.depth p.index

/-- The scalar norm average on the interval represented by a node.-/
def DyadicNode.normAverage (f : ℝ → ℂ) (L : ℝ) (p : DyadicNode) : ℝ :=
  dyadicNormAverage f L p.depth p.index

/--
@isnad1 id=eq.0h2v.s4.87f814a1051b from=translated src=- shape=71d250c3 vocab=389ee4be
-/
@[simp] theorem DyadicNode.interval_root (L : ℝ) (q : ℤ) :
    (DyadicNode.root q).interval L = dyadicInterval L 0 q := rfl

/--
@isnad1 id=eq.0h2v.s5.40f776464c60 from=translated src=- shape=f6dc84bc vocab=d220f465
-/
@[simp] theorem DyadicNode.interval_left (L : ℝ) (p : DyadicNode) :
    p.left.interval L =
      dyadicInterval L (p.depth + 1) (2 * p.index) := rfl

/--
@isnad1 id=eq.0h2v.s5.ad30c40e9210 from=translated src=- shape=1cf2eb57 vocab=9952f14b
-/
@[simp] theorem DyadicNode.interval_right (L : ℝ) (p : DyadicNode) :
    p.right.interval L =
      dyadicInterval L (p.depth + 1) (2 * p.index + 1) := rfl

/--
@isnad1 id=le.1h2v.s4.f214409ea19a from=translated src=- shape=a7fc91c9 vocab=e9784270
-/
theorem DyadicNode.left_interval_subset {L : ℝ} (hL : 0 ≤ L)
    (p : DyadicNode) : p.left.interval L ⊆ p.interval L :=
  leftChild_subset hL p.depth p.index

/--
@isnad1 id=le.1h2v.s4.d134a20d49da from=translated src=- shape=a7fc91c9 vocab=dc9e756a
-/
theorem DyadicNode.right_interval_subset {L : ℝ} (hL : 0 ≤ L)
    (p : DyadicNode) : p.right.interval L ⊆ p.interval L :=
  rightChild_subset hL p.depth p.index

/--
@isnad1 id=disjoint.1h2v.s5.bf456dac2c4e from=translated src=- shape=78b6a6ee vocab=27b7695c
-/
theorem DyadicNode.children_disjoint {L : ℝ} (hL : 0 ≤ L)
    (p : DyadicNode) : Disjoint (p.left.interval L) (p.right.interval L) :=
  left_right_children_disjoint hL p.depth p.index

/-- All strict dyadic ancestors of a node have height-one-good norm average.
This is stated intrinsically in terms of the global grid: every strictly
coarser cell containing the node's interval is good.-/
def ancestorsGood (f : ℝ → ℂ) (L : ℝ) (p : DyadicNode) : Prop :=
  ∀ (m : ℕ) (r : ℤ), m < p.depth →
    p.interval L ⊆ dyadicInterval L m r → dyadicNormAverage f L m r ≤ 1

/-- A first-crossing stopping node: its own norm average is above one, while
every strict ancestor has average at most one.-/
def IsStoppingNode (f : ℝ → ℂ) (L : ℝ) (p : DyadicNode) : Prop :=
  ancestorsGood f L p ∧ 1 < p.normAverage f L

/-- The subtype of intrinsic stopping nodes for the data-dependent root
length.  It is countable because the dyadic forest itself is encodable.-/
def stoppingNode (f : ℝ → ℂ) :=
  {p : DyadicNode // IsStoppingNode f (rootLength f) p}

/--
@isnad1 id=lt.0h2v.s4.9e4c063107bc from=translated src=- shape=fca15e0d vocab=d74ff56c
-/
theorem stoppingNode_lower_average {f : ℝ → ℂ} (p : stoppingNode f) :
    1 < p.1.normAverage f (rootLength f) := p.2.2

/--
@isnad1 id=not.1h2v.s5.1056c12f4d26 from=translated src=- shape=10907b1a vocab=756e3807
-/
theorem root_not_stopping {f : ℝ → ℂ} (hf : Integrable f) (q : ℤ) :
    ¬ IsStoppingNode f (rootLength f) (.root q) := by
  intro h
  exact (not_lt_of_ge (root_dyadicNormAverage_le_one hf q)) h.2

/-- The parent of a stopping node is height-one good.
@isnad1 id=match1.0h2v.s5.a63357abbe6c from=translated src=- shape=f1592666 vocab=65b9c95c
-/
theorem stoppingNode_parent_good {f : ℝ → ℂ} (p : stoppingNode f) :
    match p.1 with
    | .root _ => True
    | .left parent => parent.normAverage f (rootLength f) ≤ 1
    | .right parent => parent.normAverage f (rootLength f) ≤ 1 := by
  rcases p with ⟨p, hp⟩
  cases p with
  | root q => trivial
  | left parent =>
      exact hp.1 parent.depth parent.index (by simp [DyadicNode.depth])
        (DyadicNode.left_interval_subset rootLength_pos.le parent)
  | right parent =>
      exact hp.1 parent.depth parent.index (by simp [DyadicNode.depth])
        (DyadicNode.right_interval_subset rootLength_pos.le parent)

/-- Sharp upper-average estimate for every intrinsic first-crossing node.
The factor two is exactly the ratio between a parent and either child on the
line.
@isnad1 id=le.1h2v.s6.4276494f53fe from=translated src=- shape=fd652fc9 vocab=bd355cbe
-/
theorem stoppingNode_upper_average {f : ℝ → ℂ} (hf : Integrable f)
    (p : stoppingNode f) :
    p.1.normAverage f (rootLength f) ≤ 2 := by
  rcases p with ⟨p, hp⟩
  cases p with
  | root q =>
      exact (root_dyadicNormAverage_le_one hf q).trans one_le_two
  | left parent =>
      apply leftChild_dyadicNormAverage_le_two hf rootLength_pos
      exact hp.1 parent.depth parent.index (by simp [DyadicNode.depth])
        (DyadicNode.left_interval_subset rootLength_pos.le parent)
  | right parent =>
      apply rightChild_dyadicNormAverage_le_two hf rootLength_pos
      exact hp.1 parent.depth parent.index (by simp [DyadicNode.depth])
        (DyadicNode.right_interval_subset rootLength_pos.le parent)

/--
@isnad1 id=mem.1h2v.s6.d6a1d9698878 from=translated src=- shape=0b342fee vocab=ea3f382f
-/
theorem stoppingNode_average_mem_Ioc {f : ℝ → ℂ} (hf : Integrable f)
    (p : stoppingNode f) :
    p.1.normAverage f (rootLength f) ∈ Set.Ioc 1 2 :=
  ⟨stoppingNode_lower_average p, stoppingNode_upper_average hf p⟩

/-- Distinct intrinsic first-crossing nodes represent disjoint half-open
intervals.
@isnad1 id=pairwise.0h1v.s5.fb39ae969c21 from=translated src=- shape=b6be4117 vocab=76707eff
-/
theorem stoppingNode_pairwiseDisjoint {f : ℝ → ℂ} :
    Pairwise (Disjoint on fun p : stoppingNode f ↦
      p.1.interval (rootLength f)) := by
  intro p q hpq
  have reverse_of_subset {a b : DyadicNode} (hab : a.depth ≤ b.depth)
      (hsub : a.interval (rootLength f) ⊆ b.interval (rootLength f)) :
      b.interval (rootLength f) ⊆ a.interval (rootLength f) := by
    rcases dyadicInterval_subset_or_disjoint_of_le rootLength_pos hab a.index b.index with
      hrev | hdis
    · exact hrev
    · obtain ⟨x, hx⟩ := dyadicInterval_nonempty rootLength_pos a.depth a.index
      exact False.elim (Set.disjoint_left.1 hdis (hsub hx) hx)
  rcases dyadicInterval_laminar rootLength_pos p.1.depth p.1.index
      q.1.depth q.1.index with hpqsub | hqpsub | hdis
  · rcases lt_trichotomy p.1.depth q.1.depth with hlt | heq | hgt
    · have hrev := reverse_of_subset hlt.le hpqsub
      have hgood := q.2.1 p.1.depth p.1.index hlt hrev
      exact False.elim ((not_lt_of_ge hgood) p.2.2)
    · by_cases hindex : p.1.index = q.1.index
      · apply False.elim
        apply hpq
        apply Subtype.ext
        apply DyadicNode.depth_index_injective
        exact Prod.ext heq hindex
      · change Disjoint
          (dyadicInterval (rootLength f) p.1.depth p.1.index)
          (dyadicInterval (rootLength f) q.1.depth q.1.index)
        rw [← heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos p.1.depth hindex
    · have hgood := p.2.1 q.1.depth q.1.index hgt hpqsub
      exact False.elim ((not_lt_of_ge hgood) q.2.2)
  · rcases lt_trichotomy q.1.depth p.1.depth with hlt | heq | hgt
    · have hrev := reverse_of_subset hlt.le hqpsub
      have hgood := p.2.1 q.1.depth q.1.index hlt hrev
      exact False.elim ((not_lt_of_ge hgood) q.2.2)
    · by_cases hindex : p.1.index = q.1.index
      · apply False.elim
        apply hpq
        apply Subtype.ext
        apply DyadicNode.depth_index_injective
        exact Prod.ext heq.symm hindex
      · change Disjoint
          (dyadicInterval (rootLength f) p.1.depth p.1.index)
          (dyadicInterval (rootLength f) q.1.depth q.1.index)
        rw [heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos p.1.depth hindex
    · have hgood := q.2.1 p.1.depth p.1.index hgt hqpsub
      exact False.elim ((not_lt_of_ge hgood) p.2.2)
  · exact hdis

/-! ## Canonically indexed stopping cells

The following pair index has no redundant representations.  It is used for
the actual selected family and its countable union. -/

/-- A canonical cell is its depth and global integer index.-/
structure DyadicCell where
  depth : ℕ
  index : ℤ
  deriving DecidableEq, Encodable

def DyadicCell.interval (L : ℝ) (c : DyadicCell) : Set ℝ :=
  dyadicInterval L c.depth c.index

def DyadicCell.normAverage (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : ℝ :=
  dyadicNormAverage f L c.depth c.index

/-- Every strictly coarser dyadic cell containing `c` is good.-/
def cellAncestorsGood (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : Prop :=
  ∀ (m : ℕ) (r : ℤ), m < c.depth →
    c.interval L ⊆ dyadicInterval L m r → dyadicNormAverage f L m r ≤ 1

def IsStoppingCell (f : ℝ → ℂ) (L : ℝ) (c : DyadicCell) : Prop :=
  cellAncestorsGood f L c ∧ 1 < c.normAverage f L

/-- The canonical countable family of first-crossing cells.-/
def stoppingCell (f : ℝ → ℂ) :=
  {c : DyadicCell // IsStoppingCell f (rootLength f) c}

/--
@isnad1 id=countabl.0h1v.s2.271e3c1dc24c from=translated src=- shape=723ef0fc vocab=acb1e04b
-/
instance stoppingCell_countable (f : ℝ → ℂ) : Countable (stoppingCell f) :=
  Subtype.val_injective.countable

/--
@isnad1 id=lt.0h2v.s4.ae7dde710827 from=translated src=- shape=fca15e0d vocab=cacb08cc
-/
theorem stoppingCell_lower_average {f : ℝ → ℂ} (c : stoppingCell f) :
    1 < c.1.normAverage f (rootLength f) := c.2.2

/-- The parent argument gives the uniform upper average two on every
canonical first-crossing cell.
@isnad1 id=le.1h2v.s6.074e758b44a1 from=translated src=- shape=fd652fc9 vocab=cd731d5c
-/
theorem stoppingCell_upper_average {f : ℝ → ℂ} (hf : Integrable f)
    (c : stoppingCell f) : c.1.normAverage f (rootLength f) ≤ 2 := by
  rcases c with ⟨⟨n, q⟩, hc⟩
  cases n with
  | zero =>
      exact (root_dyadicNormAverage_le_one hf q).trans one_le_two
  | succ n =>
      rcases Int.even_or_odd' q with ⟨r, rfl | rfl⟩
      · apply leftChild_dyadicNormAverage_le_two hf rootLength_pos
        apply hc.1 n r (by simp)
        exact leftChild_subset rootLength_pos.le n r
      · apply rightChild_dyadicNormAverage_le_two hf rootLength_pos
        apply hc.1 n r (by simp)
        exact rightChild_subset rootLength_pos.le n r

/--
@isnad1 id=mem.1h2v.s6.9761ec4dd1d2 from=translated src=- shape=0b342fee vocab=f0cd9835
-/
theorem stoppingCell_average_mem_Ioc {f : ℝ → ℂ} (hf : Integrable f)
    (c : stoppingCell f) :
    c.1.normAverage f (rootLength f) ∈ Set.Ioc 1 2 :=
  ⟨stoppingCell_lower_average c, stoppingCell_upper_average hf c⟩

/-- The canonical first-crossing intervals are exactly pairwise disjoint.
@isnad1 id=pairwise.0h1v.s5.2313c71072a1 from=translated src=- shape=b6be4117 vocab=27b76fad
-/
theorem stoppingCell_pairwiseDisjoint {f : ℝ → ℂ} :
    Pairwise (Disjoint on fun c : stoppingCell f ↦
      c.1.interval (rootLength f)) := by
  intro c d hcd
  rcases dyadicInterval_laminar rootLength_pos c.1.depth c.1.index
      d.1.depth d.1.index with hsub | hsub | hdis
  · rcases lt_trichotomy c.1.depth d.1.depth with hlt | heq | hgt
    · rcases dyadicInterval_subset_or_disjoint_of_le rootLength_pos hlt.le
          c.1.index d.1.index with hrev | hdis'
      · exact False.elim ((not_lt_of_ge (d.2.1 c.1.depth c.1.index hlt hrev)) c.2.2)
      · obtain ⟨x, hx⟩ := dyadicInterval_nonempty rootLength_pos c.1.depth c.1.index
        exact False.elim (Set.disjoint_left.1 hdis' (hsub hx) hx)
    · by_cases hi : c.1.index = d.1.index
      · apply False.elim
        apply hcd
        apply Subtype.ext
        cases hc : c.1
        cases hd : d.1
        simp_all
      · change Disjoint
          (dyadicInterval (rootLength f) c.1.depth c.1.index)
          (dyadicInterval (rootLength f) d.1.depth d.1.index)
        rw [← heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos c.1.depth hi
    · exact False.elim ((not_lt_of_ge
        (c.2.1 d.1.depth d.1.index hgt hsub)) d.2.2)
  · rcases lt_trichotomy d.1.depth c.1.depth with hlt | heq | hgt
    · rcases dyadicInterval_subset_or_disjoint_of_le rootLength_pos hlt.le
          d.1.index c.1.index with hrev | hdis'
      · exact False.elim ((not_lt_of_ge (c.2.1 d.1.depth d.1.index hlt hrev)) d.2.2)
      · obtain ⟨x, hx⟩ := dyadicInterval_nonempty rootLength_pos d.1.depth d.1.index
        exact False.elim (Set.disjoint_left.1 hdis' (hsub hx) hx)
    · by_cases hi : c.1.index = d.1.index
      · apply False.elim
        apply hcd
        apply Subtype.ext
        cases hc : c.1
        cases hd : d.1
        simp_all
      · change Disjoint
          (dyadicInterval (rootLength f) c.1.depth c.1.index)
          (dyadicInterval (rootLength f) d.1.depth d.1.index)
        rw [heq]
        exact dyadicInterval_disjoint_of_sameDepth (L := rootLength f)
          rootLength_pos c.1.depth hi
    · exact False.elim ((not_lt_of_ge
        (d.2.1 c.1.depth c.1.index hgt hsub)) c.2.2)
  · exact hdis

def stoppingBadUnion (f : ℝ → ℂ) : Set ℝ :=
  ⋃ c : stoppingCell f, c.1.interval (rootLength f)

/--
@isnad1 id=measurab.0h2v.s4.4eed29cf9af8 from=translated src=- shape=d0502e1a vocab=6f2c50f4
-/
theorem measurableSet_stoppingCell_interval {f : ℝ → ℂ} (c : stoppingCell f) :
    MeasurableSet (c.1.interval (rootLength f)) := measurableSet_Ico

/--
@isnad1 id=measurab.0h1v.s3.845b6415954a from=translated src=- shape=47a19bcc vocab=523e35b8
-/
theorem measurableSet_stoppingBadUnion (f : ℝ → ℂ) :
    MeasurableSet (stoppingBadUnion f) := by
  let _ := Encodable.ofCountable (stoppingCell f)
  exact MeasurableSet.iUnion measurableSet_stoppingCell_interval

/--
@isnad1 id=eq.0h2v.s5.161adc116506 from=translated src=- shape=3c719167 vocab=da75cb43
-/
theorem volume_stoppingCell_interval {f : ℝ → ℂ} (c : stoppingCell f) :
    volume (c.1.interval (rootLength f)) =
      ENNReal.ofReal (dyadicLength (rootLength f) c.1.depth) :=
  volume_dyadicInterval _ _ _

/--
@isnad1 id=lt.0h2v.s5.166e18d0db91 from=translated src=- shape=13723eac vocab=b787b429
-/
theorem volume_stoppingCell_interval_lt_top {f : ℝ → ℂ} (c : stoppingCell f) :
    volume (c.1.interval (rootLength f)) < ∞ := by
  rw [volume_stoppingCell_interval]
  exact ENNReal.ofReal_lt_top

/-- Total length of the canonical stopping cells is bounded by the global
`L¹` mass.
@isnad1 id=le.1h1v.s6.ea47c851875b from=translated src=- shape=6dc5313f vocab=7d61a85e
-/
theorem tsum_volume_stoppingCell_le_lintegral_norm {f : ℝ → ℂ}
    (hf : Integrable f) :
    (∑' c : stoppingCell f, volume (c.1.interval (rootLength f))) ≤
      ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
  let _ := Encodable.ofCountable (stoppingCell f)
  have hlocal : ∀ c : stoppingCell f,
      volume (c.1.interval (rootLength f)) ≤
        ∫⁻ x in c.1.interval (rootLength f), ENNReal.ofReal ‖f x‖ := by
    intro c
    have hfin : volume (c.1.interval (rootLength f)) ≠ ∞ :=
      (volume_stoppingCell_interval_lt_top c).ne
    have havg : 1 < ⨍ x in c.1.interval (rootLength f), ‖f x‖ := c.2.2
    have hmpos : 0 < volume.real (c.1.interval (rootLength f)) := by
      rw [Measure.real, volume_stoppingCell_interval,
        ENNReal.toReal_ofReal (dyadicLength_pos rootLength_pos c.1.depth).le]
      exact dyadicLength_pos rootLength_pos c.1.depth
    have hreal : volume.real (c.1.interval (rootLength f)) <
        ∫ x in c.1.interval (rootLength f), ‖f x‖ := by
      calc
        volume.real (c.1.interval (rootLength f)) =
            volume.real (c.1.interval (rootLength f)) * 1 := by ring
        _ < volume.real (c.1.interval (rootLength f)) *
            (⨍ x in c.1.interval (rootLength f), ‖f x‖) :=
          mul_lt_mul_of_pos_left havg hmpos
        _ = ∫ x in c.1.interval (rootLength f), ‖f x‖ := by
          simpa [smul_eq_mul] using
            (measure_smul_setAverage (f := fun x ↦ ‖f x‖) hfin)
    calc
      volume (c.1.interval (rootLength f)) =
          ENNReal.ofReal (volume.real (c.1.interval (rootLength f))) := by
        rw [Measure.real, ENNReal.ofReal_toReal hfin]
      _ ≤ ENNReal.ofReal (∫ x in c.1.interval (rootLength f), ‖f x‖) :=
        ENNReal.ofReal_le_ofReal hreal.le
      _ = ∫⁻ x in c.1.interval (rootLength f), ENNReal.ofReal ‖f x‖ :=
        ofReal_integral_eq_lintegral_ofReal hf.norm.integrableOn
          (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
  calc
    (∑' c : stoppingCell f, volume (c.1.interval (rootLength f))) ≤
        ∑' c : stoppingCell f,
          ∫⁻ x in c.1.interval (rootLength f), ENNReal.ofReal ‖f x‖ :=
      ENNReal.tsum_le_tsum hlocal
    _ = ∫⁻ x in stoppingBadUnion f, ENNReal.ofReal ‖f x‖ := by
      rw [stoppingBadUnion,
        lintegral_iUnion measurableSet_stoppingCell_interval stoppingCell_pairwiseDisjoint]
    _ ≤ ∫⁻ x, ENNReal.ofReal ‖f x‖ := by
      simpa only [Measure.restrict_univ] using
        (lintegral_mono_set (μ := volume) (f := fun x ↦ ENNReal.ofReal ‖f x‖)
          (subset_univ (stoppingBadUnion f)))

/-! ## Minimal-depth selection and coverage reduction -/

/-- At depth `n`, some dyadic cell containing `x` has norm average above
one.-/
def HasBadCellAtDepth (f : ℝ → ℂ) (x : ℝ) (n : ℕ) : Prop :=
  ∃ q : ℤ, x ∈ dyadicInterval (rootLength f) n q ∧
    1 < dyadicNormAverage f (rootLength f) n q

/-- A bad cell at some depth contains an intrinsic first-crossing stopping
cell containing the same point.  The construction takes the least bad depth,
so no maximality or selection principle is assumed.
@isnad1 id=ex.1h2v.s5.b07c6b378ef4 from=translated src=- shape=bfe94bff vocab=707d53a5
-/
theorem exists_stoppingCell_mem_of_exists_badCell {f : ℝ → ℂ} {x : ℝ}
    (hx : ∃ n, HasBadCellAtDepth f x n) :
    ∃ c : stoppingCell f, x ∈ c.1.interval (rootLength f) := by
  classical
  let n := Nat.find hx
  have hn : HasBadCellAtDepth f x n := Nat.find_spec hx
  let q := hn.choose
  have hxq : x ∈ dyadicInterval (rootLength f) n q := hn.choose_spec.1
  have hqbad : 1 < dyadicNormAverage f (rootLength f) n q := hn.choose_spec.2
  let c : DyadicCell := ⟨n, q⟩
  have hcAnc : cellAncestorsGood f (rootLength f) c := by
    intro m r hm hsub
    by_contra hnot
    have hrbad : 1 < dyadicNormAverage f (rootLength f) m r := lt_of_not_ge hnot
    have hmBad : HasBadCellAtDepth f x m :=
      ⟨r, hsub hxq, hrbad⟩
    exact (Nat.not_lt_of_ge (Nat.find_min' hx hmBad)) hm
  exact ⟨⟨c, hcAnc, hqbad⟩, hxq⟩

/--
@isnad1 id=mem.1h2v.s4.5eb982f5e776 from=translated src=- shape=e4b4dd30 vocab=72c78728
-/
theorem mem_stoppingBadUnion_of_exists_badCell {f : ℝ → ℂ} {x : ℝ}
    (hx : ∃ n, HasBadCellAtDepth f x n) : x ∈ stoppingBadUnion f := by
  rcases exists_stoppingCell_mem_of_exists_badCell hx with ⟨c, hc⟩
  exact mem_iUnion.2 ⟨c, hc⟩

/-! ## Dyadic differentiation -/

/-- The unique integer index of the half-open depth-`n` cell containing a
point.-/
def containingIndex (L : ℝ) (n : ℕ) (x : ℝ) : ℤ :=
  ⌊x / dyadicLength L n⌋

/--
@isnad1 id=mem.1h3v.s4.9e6d9008843d from=translated src=- shape=7cf52f59 vocab=0307fec1
-/
theorem mem_dyadicInterval_containingIndex {L : ℝ} (hL : 0 < L)
    (n : ℕ) (x : ℝ) :
    x ∈ dyadicInterval L n (containingIndex L n x) := by
  have hd := dyadicLength_pos hL n
  simp only [dyadicInterval, mem_Ico, containingIndex]
  constructor
  · exact (le_div_iff₀ hd).mp (Int.floor_le (x / dyadicLength L n))
  · exact (div_lt_iff₀ hd).mp (Int.lt_floor_add_one (x / dyadicLength L n))

def containingCenter (L : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  ((containingIndex L n x : ℝ) + 1 / 2) * dyadicLength L n

def containingRadius (L : ℝ) (n : ℕ) : ℝ :=
  dyadicLength L n / 2

/--
@isnad1 id=eq.0h3v.s6.376f659dd6dc from=translated src=- shape=d1b82e04 vocab=51473f27
-/
theorem closedBall_containing_eq_Icc (L : ℝ) (n : ℕ) (x : ℝ) :
    Metric.closedBall (containingCenter L n x) (containingRadius L n) =
      Icc ((containingIndex L n x : ℝ) * dyadicLength L n)
        (((containingIndex L n x : ℝ) + 1) * dyadicLength L n) := by
  rw [Real.closedBall_eq_Icc]
  simp only [containingCenter, containingRadius]
  congr 1 <;> ring

/--
@isnad1 id=eq.0h4v.s6.b0eb7f11444d from=translated src=- shape=04ada6a0 vocab=61a10437
-/
theorem setAverage_dyadicInterval_eq_closedBall (g : ℝ → ℝ)
    (L : ℝ) (n : ℕ) (x : ℝ) :
    (⨍ y in dyadicInterval L n (containingIndex L n x), g y) =
      ⨍ y in Metric.closedBall (containingCenter L n x) (containingRadius L n), g y := by
  rw [closedBall_containing_eq_Icc, dyadicInterval, setAverage_eq, setAverage_eq]
  simp only [Measure.real, Real.volume_Icc, Real.volume_Ico]
  rw [integral_Icc_eq_integral_Ico]

/--
@isnad1 id=tendsto.1h1v.s5.909e30a2fc6e from=translated src=- shape=f9dfa87e vocab=6e8d6451
-/
theorem tendsto_containingRadius_nhdsGT_zero {L : ℝ} (hL : 0 < L) :
    Tendsto (containingRadius L) atTop (𝓝[>] 0) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hp : Tendsto (fun n : ℕ ↦ (((2 : ℝ)⁻¹) ^ n)) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
    have hmul := hp.const_mul (L / 2)
    convert hmul using 1
    · funext n
      simp only [containingRadius, dyadicLength, div_eq_mul_inv]
      norm_num
      rw [← inv_pow]
      norm_num
      ring
    · ring
  · exact Filter.Eventually.of_forall fun n ↦
      half_pos (dyadicLength_pos hL n)

/--
@isnad1 id=mem.1h3v.s5.0f835839161f from=translated src=- shape=7d6287e3 vocab=9233500b
-/
theorem mem_closedBall_containing {L : ℝ} (hL : 0 < L) (n : ℕ) (x : ℝ) :
    x ∈ Metric.closedBall (containingCenter L n x) (containingRadius L n) := by
  rw [closedBall_containing_eq_Icc]
  exact ⟨(mem_dyadicInterval_containingIndex hL n x).1,
    (mem_dyadicInterval_containingIndex hL n x).2.le⟩

/-- Lebesgue differentiation along the unique half-open dyadic cells
containing a point.
@isnad1 id=eventual.1h1v.s6.da8255a5db49 from=translated src=- shape=24230e1f vocab=91113fa4
-/
theorem ae_tendsto_dyadicNormAverage {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume,
      Tendsto
        (fun n ↦ dyadicNormAverage f (rootLength f) n
          (containingIndex (rootLength f) n x))
        atTop (𝓝 ‖f x‖) := by
  have hdiff := IsUnifLocDoublingMeasure.ae_tendsto_average
    (volume : Measure ℝ) hf.norm.locallyIntegrable 1
  filter_upwards [hdiff] with x hx
  have hball := hx
    (containingCenter (rootLength f) · x)
    (containingRadius (rootLength f))
    (tendsto_containingRadius_nhdsGT_zero rootLength_pos)
    (Filter.Eventually.of_forall fun n ↦ by
      simpa using mem_closedBall_containing rootLength_pos n x)
  rw [show (fun n ↦
      ⨍ y in Metric.closedBall
        (containingCenter (rootLength f) n x)
        (containingRadius (rootLength f) n), ‖f y‖) =
      (fun n ↦ dyadicNormAverage f (rootLength f) n
        (containingIndex (rootLength f) n x)) by
    funext n
    exact (setAverage_dyadicInterval_eq_closedBall
      (fun y ↦ ‖f y‖) (rootLength f) n x).symm] at hball
  exact hball

/-- Almost every point whose value is above height one belongs to a bad
dyadic cell at some finite depth.
@isnad1 id=eventual.1h1v.s6.088bbb490f94 from=translated src=- shape=89d9135e vocab=232f7223
-/
theorem ae_exists_badCell_of_high {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume, 1 < ‖f x‖ → ∃ n, HasBadCellAtDepth f x n := by
  filter_upwards [ae_tendsto_dyadicNormAverage hf] with x hxlim
  intro hxhigh
  have hev : ∀ᶠ n in atTop,
      1 < dyadicNormAverage f (rootLength f) n
        (containingIndex (rootLength f) n x) :=
    (tendsto_order.1 hxlim).1 1 hxhigh
  rcases hev.exists with ⟨n, hn⟩
  exact ⟨n, containingIndex (rootLength f) n x,
    mem_dyadicInterval_containingIndex rootLength_pos n x, hn⟩

/-- The intrinsic stopping intervals cover the height-one superlevel set
almost everywhere.
@isnad1 id=eventual.1h1v.s6.753ab06236e4 from=translated src=- shape=6339550b vocab=ee4b3e2d
-/
theorem ae_highPoint_mem_stoppingBadUnion {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume, 1 < ‖f x‖ → x ∈ stoppingBadUnion f := by
  filter_upwards [ae_exists_badCell_of_high hf] with x hx
  exact fun hhigh ↦ mem_stoppingBadUnion_of_exists_badCell (hx hhigh)

/-! ## The full good part -/

def stoppingCellAverage (f : ℝ → ℂ) (c : stoppingCell f) : ℂ :=
  ⨍ y in c.1.interval (rootLength f), f y

/--
@isnad1 id=le.0h2v.s4.5ce8bc51df34 from=translated src=- shape=a055b48d vocab=15bae330
-/
theorem norm_stoppingCellAverage_le_normAverage {f : ℝ → ℂ}
    (c : stoppingCell f) :
    ‖stoppingCellAverage f c‖ ≤ c.1.normAverage f (rootLength f) := by
  have hmpos : 0 < volume.real (c.1.interval (rootLength f)) := by
    rw [Measure.real, volume_stoppingCell_interval,
      ENNReal.toReal_ofReal (dyadicLength_pos rootLength_pos c.1.depth).le]
    exact dyadicLength_pos rootLength_pos c.1.depth
  rw [stoppingCellAverage, DyadicCell.normAverage, dyadicNormAverage,
    setAverage_eq, setAverage_eq]
  simp only [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hmpos,
    smul_eq_mul]
  exact mul_le_mul_of_nonneg_left (norm_integral_le_integral_norm _)
    (inv_nonneg.2 hmpos.le)

/--
@isnad1 id=le.1h2v.s5.c106c3be93dd from=translated src=- shape=41d1a840 vocab=84864532
-/
theorem norm_stoppingCellAverage_le_two {f : ℝ → ℂ} (hf : Integrable f)
    (c : stoppingCell f) : ‖stoppingCellAverage f c‖ ≤ 2 :=
  (norm_stoppingCellAverage_le_normAverage c).trans
    (stoppingCell_upper_average hf c)

/-- The usual Calderón--Zygmund good part: `f` off the stopping union and
the interval average on each stopping cell.  The pointwise sum has at most
one nonzero term because the cells are pairwise disjoint.-/
def stoppingGoodPart (f : ℝ → ℂ) (x : ℝ) : ℂ :=
  (stoppingBadUnion f)ᶜ.indicator f x +
    ∑' c : stoppingCell f,
      (c.1.interval (rootLength f)).indicator
        (fun _ ↦ stoppingCellAverage f c) x

private theorem tsum_stoppingPiece_eq_of_mem {f : ℝ → ℂ}
    (c : stoppingCell f) {x : ℝ} (hx : x ∈ c.1.interval (rootLength f)) :
    (∑' d : stoppingCell f,
      (d.1.interval (rootLength f)).indicator
        (fun _ ↦ stoppingCellAverage f d) x) = stoppingCellAverage f c := by
  classical
  rw [tsum_eq_single c]
  · simp [hx]
  · intro d hdc
    have hdis := stoppingCell_pairwiseDisjoint (f := f) hdc.symm
    have hxnot : x ∉ d.1.interval (rootLength f) :=
      fun hxd ↦ Set.disjoint_left.1 hdis hx hxd
    simp [hxnot]

private theorem tsum_stoppingPiece_eq_zero_of_notMem {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ stoppingBadUnion f) :
    (∑' c : stoppingCell f,
      (c.1.interval (rootLength f)).indicator
        (fun _ ↦ stoppingCellAverage f c) x) = 0 := by
  have hzero : (fun c : stoppingCell f ↦
      (c.1.interval (rootLength f)).indicator
        (fun _ ↦ stoppingCellAverage f c) x) = 0 := by
    funext c
    have hxc : x ∉ c.1.interval (rootLength f) := fun hmem ↦
      hx (mem_iUnion.2 ⟨c, hmem⟩)
    simp [hxc]
  rw [hzero]
  exact tsum_zero

/--
@isnad1 id=eq.1h3v.s5.69962e0fe22b from=translated src=- shape=d0704d47 vocab=c24cb251
-/
theorem stoppingGoodPart_eq_average_of_mem {f : ℝ → ℂ}
    (c : stoppingCell f) {x : ℝ} (hx : x ∈ c.1.interval (rootLength f)) :
    stoppingGoodPart f x = stoppingCellAverage f c := by
  have hxu : x ∈ stoppingBadUnion f := mem_iUnion.2 ⟨c, hx⟩
  have hxcomp : x ∉ (stoppingBadUnion f)ᶜ := by simpa
  rw [stoppingGoodPart, indicator_of_notMem hxcomp,
    tsum_stoppingPiece_eq_of_mem c hx, zero_add]

/--
@isnad1 id=eq.1h2v.s4.efe2a480cc92 from=translated src=- shape=1cbe68bf vocab=821fbb78
-/
theorem stoppingGoodPart_eq_of_notMem {f : ℝ → ℂ} {x : ℝ}
    (hx : x ∉ stoppingBadUnion f) : stoppingGoodPart f x = f x := by
  rw [stoppingGoodPart, indicator_of_mem (mem_compl hx),
    tsum_stoppingPiece_eq_zero_of_notMem hx, add_zero]

/-- The full good part, including the averages on stopping intervals, has
the sharp height-two essential bound.
@isnad1 id=eventual.1h1v.s6.5266941091fb from=translated src=- shape=0603455c vocab=cf3506ef
-/
theorem ae_norm_stoppingGoodPart_le_two {f : ℝ → ℂ} (hf : Integrable f) :
    ∀ᵐ x ∂volume, ‖stoppingGoodPart f x‖ ≤ 2 := by
  filter_upwards [ae_highPoint_mem_stoppingBadUnion hf] with x hxcover
  by_cases hxu : x ∈ stoppingBadUnion f
  · rcases mem_iUnion.1 hxu with ⟨c, hxc⟩
    rw [stoppingGoodPart_eq_average_of_mem c hxc]
    exact norm_stoppingCellAverage_le_two hf c
  · rw [stoppingGoodPart_eq_of_notMem hxu]
    exact (le_of_not_gt (fun hhigh ↦ hxu (hxcover hhigh))).trans one_le_two

/--
@isnad1 id=eq.0h1v.s6.2bd0f080fa8a from=translated src=- shape=90af2367 vocab=89e71602
-/
theorem volume_stoppingBadUnion_eq_tsum (f : ℝ → ℂ) :
    volume (stoppingBadUnion f) =
      ∑' c : stoppingCell f, volume (c.1.interval (rootLength f)) := by
  let _ := Encodable.ofCountable (stoppingCell f)
  rw [stoppingBadUnion,
    measure_iUnion stoppingCell_pairwiseDisjoint measurableSet_stoppingCell_interval]

/--
@isnad1 id=lt.1h1v.s6.5ad67eca1554 from=translated src=- shape=007a2f36 vocab=cd4b10ef
-/
theorem volume_stoppingBadUnion_lt_top {f : ℝ → ℂ} (hf : Integrable f) :
    volume (stoppingBadUnion f) < ∞ := by
  rw [volume_stoppingBadUnion_eq_tsum]
  refine (tsum_volume_stoppingCell_le_lintegral_norm hf).trans_lt ?_
  rw [← ofReal_integral_eq_lintegral_ofReal hf.norm
    (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))]
  exact ENNReal.ofReal_lt_top

/--
@isnad1 id=le.1h1v.s6.703ff725d15e from=translated src=- shape=58e3cf4f vocab=f8df56f6
-/
theorem volumeReal_stoppingBadUnion_le_integral_norm {f : ℝ → ℂ}
    (hf : Integrable f) :
    volume.real (stoppingBadUnion f) ≤ ∫ x, ‖f x‖ := by
  have hvol := tsum_volume_stoppingCell_le_lintegral_norm hf
  rw [← volume_stoppingBadUnion_eq_tsum] at hvol
  have hreal := ENNReal.toReal_mono
    (by
      rw [← ofReal_integral_eq_lintegral_ofReal hf.norm
        (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))]
      exact ENNReal.ofReal_ne_top) hvol
  rw [Measure.real]
  simp only [ofReal_norm] at hreal
  exact hreal.trans_eq (integral_norm_eq_lintegral_enorm hf.1).symm

/--
@isnad1 id=aestrong.1h1v.s6.776f1a52b58c from=translated src=- shape=d62be1ad vocab=80600702
-/
theorem aestronglyMeasurable_stoppingGoodPart {f : ℝ → ℂ} (hf : Integrable f) :
    AEStronglyMeasurable (stoppingGoodPart f) volume := by
  let _ := Encodable.ofCountable (stoppingCell f)
  apply (hf.1.indicator (measurableSet_stoppingBadUnion f).compl).add
  apply AEStronglyMeasurable.tsum
  intro c
  exact (measurable_const.indicator
    (measurableSet_stoppingCell_interval (f := f) c)).aestronglyMeasurable

/--
@isnad1 id=integrab.1h1v.s6.1874f03907e9 from=translated src=- shape=cd647116 vocab=2b924a04
-/
theorem integrable_sq_norm_stoppingGoodPart {f : ℝ → ℂ} (hf : Integrable f) :
    Integrable (fun x ↦ ‖stoppingGoodPart f x‖ ^ 2) := by
  let majorant : ℝ → ℝ := fun x ↦ ‖f x‖ +
    (stoppingBadUnion f).indicator (fun _ ↦ (4 : ℝ)) x
  have hconst : Integrable
      ((stoppingBadUnion f).indicator (fun _ ↦ (4 : ℝ))) :=
    (integrableOn_const (volume_stoppingBadUnion_lt_top hf).ne).integrable_indicator
      (measurableSet_stoppingBadUnion f)
  have hmajorant : Integrable majorant := hf.norm.add hconst
  apply Integrable.mono' hmajorant
  · exact AEMeasurable.aestronglyMeasurable
      ((aestronglyMeasurable_stoppingGoodPart hf).norm.aemeasurable.pow_const 2)
  · filter_upwards [ae_highPoint_mem_stoppingBadUnion hf] with x hxcover
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    by_cases hxu : x ∈ stoppingBadUnion f
    · rcases mem_iUnion.1 hxu with ⟨c, hxc⟩
      rw [stoppingGoodPart_eq_average_of_mem c hxc]
      simp only [majorant, indicator_of_mem hxu]
      nlinarith [norm_nonneg (f x), norm_nonneg (stoppingCellAverage f c),
        norm_stoppingCellAverage_le_two hf c]
    · rw [stoppingGoodPart_eq_of_notMem hxu]
      simp only [majorant, indicator_of_notMem hxu, add_zero]
      have hnorm : ‖f x‖ ≤ 1 := le_of_not_gt fun hhigh ↦ hxu (hxcover hhigh)
      nlinarith [norm_nonneg (f x)]

/-- A global squared-`L²` estimate for the complete good part.  The constant
five comes from the direct domination `‖g‖² ≤ ‖f‖ + 4⋅1_Ω`; it uses only
integrability of `f` and the stopping-family length bound.
@isnad1 id=le.1h1v.s7.dec8bffed505 from=translated src=- shape=fb132e5c vocab=808b609b
-/
theorem integral_sq_norm_stoppingGoodPart_le_five_l1 {f : ℝ → ℂ}
    (hf : Integrable f) :
    (∫ x, ‖stoppingGoodPart f x‖ ^ 2) ≤ 5 * ∫ x, ‖f x‖ := by
  let majorant : ℝ → ℝ := fun x ↦ ‖f x‖ +
    (stoppingBadUnion f).indicator (fun _ ↦ (4 : ℝ)) x
  have hconst : Integrable
      ((stoppingBadUnion f).indicator (fun _ ↦ (4 : ℝ))) :=
    (integrableOn_const (volume_stoppingBadUnion_lt_top hf).ne).integrable_indicator
      (measurableSet_stoppingBadUnion f)
  have hmajorant : Integrable majorant := hf.norm.add hconst
  have hpoint : ∀ᵐ x ∂volume, ‖stoppingGoodPart f x‖ ^ 2 ≤ majorant x := by
    filter_upwards [ae_highPoint_mem_stoppingBadUnion hf] with x hxcover
    by_cases hxu : x ∈ stoppingBadUnion f
    · rcases mem_iUnion.1 hxu with ⟨c, hxc⟩
      rw [stoppingGoodPart_eq_average_of_mem c hxc]
      simp only [majorant, indicator_of_mem hxu]
      nlinarith [norm_nonneg (f x), norm_nonneg (stoppingCellAverage f c),
        norm_stoppingCellAverage_le_two hf c]
    · rw [stoppingGoodPart_eq_of_notMem hxu]
      simp only [majorant, indicator_of_notMem hxu, add_zero]
      have hnorm : ‖f x‖ ≤ 1 := le_of_not_gt fun hhigh ↦ hxu (hxcover hhigh)
      nlinarith [norm_nonneg (f x)]
  have hsqMeas : AEStronglyMeasurable
      (fun x ↦ ‖stoppingGoodPart f x‖ ^ 2) volume :=
    ((aestronglyMeasurable_stoppingGoodPart hf).norm.aemeasurable.pow_const 2).aestronglyMeasurable
  have hsq : Integrable (fun x ↦ ‖stoppingGoodPart f x‖ ^ 2) := by
    apply Integrable.mono' hmajorant hsqMeas
    filter_upwards [hpoint] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact hx
  calc
    (∫ x, ‖stoppingGoodPart f x‖ ^ 2) ≤ ∫ x, majorant x :=
      integral_mono_ae hsq hmajorant hpoint
    _ = (∫ x, ‖f x‖) + 4 * volume.real (stoppingBadUnion f) := by
      rw [integral_add hf.norm hconst, integral_indicator
        (measurableSet_stoppingBadUnion f), setIntegral_const]
      simp only [smul_eq_mul]
      ring
    _ ≤ 5 * ∫ x, ‖f x‖ := by
      have hmass : 0 ≤ ∫ x, ‖f x‖ :=
        integral_nonneg_of_ae
          (Filter.Eventually.of_forall fun x ↦ norm_nonneg (f x))
      nlinarith [volumeReal_stoppingBadUnion_le_integral_norm hf]

end
end CalderonZygmundDyadicStopping
end QuadraticCarleson
