/-
Copyright (c) 2023 Yaël Dillies, Chenyi Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chenyi Li, Ziyu Wang, Yaël Dillies
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Convex.Function
public import Tengoku.Seed.Analysis.InnerProductSpace.Basic

/-!
# Uniformly and strongly convex functions

In this file, we define uniformly convex functions and strongly convex functions.

For a real normed space `E`, a uniformly convex function with modulus `φ : ℝ → ℝ` is a function
`f : E → ℝ` such that `f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y - t * (1 - t) * φ ‖x - y‖`
for all `t ∈ [0, 1]`.

A `m`-strongly convex function is a uniformly convex function with modulus `fun r ↦ m / 2 * r ^ 2`.
If `E` is an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` being convex.

## TODO

Prove derivative properties of strongly convex functions.
-/

@[expose] public section

open Real

variable {E : Type*} [NormedAddCommGroup E]

section NormedSpace
variable [NormedSpace ℝ E] {φ ψ : ℝ → ℝ} {s : Set E} {m : ℝ} {f g : E → ℝ}

/-- A function `f` from a real normed space is uniformly convex with modulus `φ` if
`f (t • x + (1 - t) • y) ≤ t • f x + (1 - t) • f y - t * (1 - t) * φ ‖x - y‖` for all `t ∈ [0, 1]`.

`φ` is usually taken to be a monotone function such that `φ r = 0 ↔ r = 0`. -/
def UniformConvexOn (s : Set E) (φ : ℝ → ℝ) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    f (a • x + b • y) ≤ a • f x + b • f y - a * b * φ ‖x - y‖

/-- A function `f` from a real normed space is uniformly concave with modulus `φ` if
`t • f x + (1 - t) • f y + t * (1 - t) * φ ‖x - y‖ ≤ f (t • x + (1 - t) • y)` for all `t ∈ [0, 1]`.

`φ` is usually taken to be a monotone function such that `φ r = 0 ↔ r = 0`. -/
def UniformConcaveOn (s : Set E) (φ : ℝ → ℝ) (f : E → ℝ) : Prop :=
  Convex ℝ s ∧ ∀ ⦃x⦄, x ∈ s → ∀ ⦃y⦄, y ∈ s → ∀ ⦃a b : ℝ⦄, 0 ≤ a → 0 ≤ b → a + b = 1 →
    a • f x + b • f y + a * b * φ ‖x - y‖ ≤ f (a • x + b • y)

/--
@isnad1 id=iff.0h3v.s6.dd928fbbc88b from=seed src=0 shape=63418d78 vocab=7a1b7203
-/
@[simp] lemma uniformConvexOn_zero : UniformConvexOn s 0 f ↔ ConvexOn ℝ s f := by
  simp [UniformConvexOn, ConvexOn]

/--
@isnad1 id=iff.0h3v.s6.aa665faec72b from=seed src=0 shape=63418d78 vocab=be1bba7b
-/
@[simp] lemma uniformConcaveOn_zero : UniformConcaveOn s 0 f ↔ ConcaveOn ℝ s f := by
  simp [UniformConcaveOn, ConcaveOn]

/--
@isnad1 id=uniformc.1h3v.s6.2462a574704f from=seed src=0 shape=c0296571 vocab=7a1b7203
-/
protected alias ⟨_, ConvexOn.uniformConvexOn_zero⟩ := uniformConvexOn_zero
/--
@isnad1 id=uniformc.1h3v.s6.88bf5be95c50 from=seed src=0 shape=c0296571 vocab=be1bba7b
-/
protected alias ⟨_, ConcaveOn.uniformConcaveOn_zero⟩ := uniformConcaveOn_zero

/--
@isnad1 id=uniformc.2h5v.s5.0988e72b3dd0 from=seed src=0 shape=b3e00c06 vocab=9dffbebb
-/
lemma UniformConvexOn.mono (hψφ : ψ ≤ φ) (hf : UniformConvexOn s φ f) : UniformConvexOn s ψ f :=
  ⟨hf.1, fun x hx y hy a b ha hb hab ↦ (hf.2 hx hy ha hb hab).trans <| by gcongr; apply hψφ⟩

/--
@isnad1 id=uniformc.2h5v.s5.832493bbc630 from=seed src=0 shape=b3e00c06 vocab=97bf1d77
-/
lemma UniformConcaveOn.mono (hψφ : ψ ≤ φ) (hf : UniformConcaveOn s φ f) : UniformConcaveOn s ψ f :=
  ⟨hf.1, fun x hx y hy a b ha hb hab ↦ (hf.2 hx hy ha hb hab).trans' <| by gcongr; apply hψφ⟩

/--
@isnad1 id=convexon.2h4v.s7.2b829c08819c from=seed src=0 shape=0f2e2ac1 vocab=35378465
-/
lemma UniformConvexOn.convexOn (hf : UniformConvexOn s φ f) (hφ : 0 ≤ φ) : ConvexOn ℝ s f := by
  simpa using hf.mono hφ

/--
@isnad1 id=concaveo.2h4v.s7.87512107ebe5 from=seed src=0 shape=0f2e2ac1 vocab=d08bcc8c
-/
lemma UniformConcaveOn.concaveOn (hf : UniformConcaveOn s φ f) (hφ : 0 ≤ φ) : ConcaveOn ℝ s f := by
  simpa using hf.mono hφ

/--
@isnad1 id=strictco.2h4v.s7.4c1eca968e99 from=seed src=0 shape=f83e158e vocab=6a655c68
-/
lemma UniformConvexOn.strictConvexOn (hf : UniformConvexOn s φ f) (hφ : ∀ r, r ≠ 0 → 0 < φ r) :
    StrictConvexOn ℝ s f := by
  refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab ↦ (hf.2 hx hy ha.le hb.le hab).trans_lt <|
    sub_lt_self _ ?_⟩
  rw [← sub_ne_zero, ← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']

/--
@isnad1 id=strictco.2h4v.s7.b7896b732aa6 from=seed src=0 shape=f83e158e vocab=fcf998e9
-/
lemma UniformConcaveOn.strictConcaveOn (hf : UniformConcaveOn s φ f) (hφ : ∀ r, r ≠ 0 → 0 < φ r) :
    StrictConcaveOn ℝ s f := by
  refine ⟨hf.1, fun x hx y hy hxy a b ha hb hab ↦ (hf.2 hx hy ha.le hb.le hab).trans_lt' <|
    lt_add_of_pos_right _ ?_⟩
  rw [← sub_ne_zero, ← norm_pos_iff] at hxy
  positivity [hφ _ hxy.ne']

/--
@isnad1 id=uniformc.2h6v.s6.a5455203bae8 from=seed src=0 shape=aeb2bce8 vocab=4e87e6f9
-/
lemma UniformConvexOn.add (hf : UniformConvexOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm, sub_add_sub_comm]
    using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

/--
@isnad1 id=uniformc.2h6v.s6.f78d8187898f from=seed src=0 shape=aeb2bce8 vocab=5596bd5b
-/
lemma UniformConcaveOn.add (hf : UniformConcaveOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f + g) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ ?_⟩
  simpa [mul_add, add_add_add_comm] using add_le_add (hf.2 hx hy ha hb hab) (hg.2 hx hy ha hb hab)

/--
@isnad1 id=uniformc.1h4v.s5.8596b5c48020 from=seed src=0 shape=22ca4898 vocab=ac51d835
-/
lemma UniformConvexOn.neg (hf : UniformConvexOn s φ f) : UniformConcaveOn s φ (-f) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, le_sub_iff_add_le'] using hf.2 hx hy ha hb hab

/--
@isnad1 id=uniformc.1h4v.s5.92242eb8dbe2 from=seed src=0 shape=22ca4898 vocab=ac51d835
-/
lemma UniformConcaveOn.neg (hf : UniformConcaveOn s φ f) : UniformConvexOn s φ (-f) := by
  refine ⟨hf.1, fun x hx y hy a b ha hb hab ↦ le_of_neg_le_neg ?_⟩
  simpa [add_comm, -neg_le_neg_iff, ← le_sub_iff_add_le', sub_eq_add_neg, neg_add]
    using hf.2 hx hy ha hb hab

/--
@isnad1 id=uniformc.2h6v.s6.f09f7ee5d15f from=seed src=0 shape=bab0e154 vocab=303d7d24
-/
lemma UniformConvexOn.sub (hf : UniformConvexOn s φ f) (hg : UniformConcaveOn s ψ g) :
    UniformConvexOn s (φ + ψ) (f - g) := by simpa using! hf.add hg.neg

/--
@isnad1 id=uniformc.2h6v.s6.1b553dc3a49f from=seed src=0 shape=bab0e154 vocab=303d7d24
-/
lemma UniformConcaveOn.sub (hf : UniformConcaveOn s φ f) (hg : UniformConvexOn s ψ g) :
    UniformConcaveOn s (φ + ψ) (f - g) := by simpa using! hf.add hg.neg

/-- A function `f` from a real normed space is `m`-strongly convex if it is uniformly convex with
modulus `φ(r) = m / 2 * r ^ 2`.

In an inner product space, this is equivalent to `x ↦ f x - m / 2 * ‖x‖ ^ 2` being convex. -/
def StrongConvexOn (s : Set E) (m : ℝ) : (E → ℝ) → Prop :=
  UniformConvexOn s fun r ↦ m / (2 : ℝ) * r ^ 2

/-- A function `f` from a real normed space is `m`-strongly concave if is strongly concave with
modulus `φ(r) = m / 2 * r ^ 2`.

In an inner product space, this is equivalent to `x ↦ f x + m / 2 * ‖x‖ ^ 2` being concave. -/
def StrongConcaveOn (s : Set E) (m : ℝ) : (E → ℝ) → Prop :=
  UniformConcaveOn s fun r ↦ m / (2 : ℝ) * r ^ 2

variable {s : Set E} {f : E → ℝ} {m n : ℝ}

/--
@isnad1 id=strongco.2h5v.s5.0f6aec0ede47 from=seed src=0 shape=2b6c640f vocab=66103882
-/
nonrec lemma StrongConvexOn.mono (hmn : m ≤ n) (hf : StrongConvexOn s n f) : StrongConvexOn s m f :=
  hf.mono fun r ↦ by gcongr

/--
@isnad1 id=strongco.2h5v.s5.9b716e80c4f0 from=seed src=0 shape=2b6c640f vocab=66f75bcb
-/
nonrec lemma StrongConcaveOn.mono (hmn : m ≤ n) (hf : StrongConcaveOn s n f) :
    StrongConcaveOn s m f := hf.mono fun r ↦ by gcongr

/--
@isnad1 id=iff.0h3v.s6.f4e2f13068a2 from=seed src=0 shape=dd6c6f6a vocab=f979545a
-/
@[simp] lemma strongConvexOn_zero : StrongConvexOn s 0 f ↔ ConvexOn ℝ s f := by
  simp [StrongConvexOn, ← Pi.zero_def]

/--
@isnad1 id=iff.0h3v.s6.fed965215f9a from=seed src=0 shape=dd6c6f6a vocab=6301aa92
-/
@[simp] lemma strongConcaveOn_zero : StrongConcaveOn s 0 f ↔ ConcaveOn ℝ s f := by
  simp [StrongConcaveOn, ← Pi.zero_def]

/--
@isnad1 id=strictco.2h4v.s6.7adca49b9ede from=seed src=0 shape=ceee45d0 vocab=1f3cde71
-/
nonrec lemma StrongConvexOn.strictConvexOn (hf : StrongConvexOn s m f) (hm : 0 < m) :
    StrictConvexOn ℝ s f := hf.strictConvexOn fun r hr ↦ by positivity

/--
@isnad1 id=strictco.2h4v.s6.23c648c6c77f from=seed src=0 shape=ceee45d0 vocab=74587499
-/
nonrec lemma StrongConcaveOn.strictConcaveOn (hf : StrongConcaveOn s m f) (hm : 0 < m) :
    StrictConcaveOn ℝ s f := hf.strictConcaveOn fun r hr ↦ by positivity

end NormedSpace

section InnerProductSpace
variable [InnerProductSpace ℝ E] {s : Set E} {a b m : ℝ} {x y : E} {f : E → ℝ}

private lemma aux_sub (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * (f x - m / (2 : ℝ) * ‖x‖ ^ 2) + b * (f y - m / (2 : ℝ) * ‖y‖ ^ 2) +
      m / (2 : ℝ) * ‖a • x + b • y‖ ^ 2
      = a * f x + b * f y - m / (2 : ℝ) * a * b * ‖x - y‖ ^ 2 := by
  rw [norm_add_sq_real, norm_sub_sq_real, norm_smul, norm_smul, real_inner_smul_left,
    inner_smul_right, norm_of_nonneg ha, norm_of_nonneg hb, mul_pow, mul_pow]
  obtain rfl := eq_sub_of_add_eq hab
  ring_nf

private lemma aux_add (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    a * (f x + m / (2 : ℝ) * ‖x‖ ^ 2) + b * (f y + m / (2 : ℝ) * ‖y‖ ^ 2) -
      m / (2 : ℝ) * ‖a • x + b • y‖ ^ 2
      = a * f x + b * f y + m / (2 : ℝ) * a * b * ‖x - y‖ ^ 2 := by
  simpa [neg_div] using! aux_sub (E := E) (m := -m) ha hb hab

/--
@isnad1 id=iff.0h4v.s7.617f607f575c from=seed src=0 shape=5ef9e343 vocab=f8866b4b
-/
lemma strongConvexOn_iff_convex :
    StrongConvexOn s m f ↔ ConvexOn ℝ s fun x ↦ f x - m / (2 : ℝ) * ‖x‖ ^ 2 := by
  refine and_congr_right fun _ ↦ forall₄_congr fun x _ y _ ↦ forall₅_congr fun a b ha hb hab ↦ ?_
  simp_rw [sub_le_iff_le_add, smul_eq_mul, aux_sub ha hb hab, mul_assoc, mul_left_comm]

/--
@isnad1 id=iff.0h4v.s7.ed56aeb12abd from=seed src=0 shape=5ef9e343 vocab=bfa22630
-/
lemma strongConcaveOn_iff_convex :
    StrongConcaveOn s m f ↔ ConcaveOn ℝ s fun x ↦ f x + m / (2 : ℝ) * ‖x‖ ^ 2 := by
  refine and_congr_right fun _ ↦ forall₄_congr fun x _ y _ ↦ forall₅_congr fun a b ha hb hab ↦ ?_
  simp_rw [← sub_le_iff_le_add, smul_eq_mul, aux_add ha hb hab, mul_assoc, mul_left_comm]

end InnerProductSpace
