/-
Copyright (c) 2025 Xavier Généreux. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Généreux, María Inés de Frutos Fernández
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Group.Pointwise.Finset.Basic
public import Tengoku.Seed.Algebra.SkewMonoidAlgebra.Basic

/-!
# Lemmas about the support of an element of a skew monoid algebra

For `f : SkewMonoidAlgebra k G`, `f.support` is the set of all `a ∈ G` such that `f.coeff a ≠ 0`.
-/

public section

open scoped Pointwise

namespace SkewMonoidAlgebra

open Finset Finsupp

variable {k G : Type*}

section AddCommMonoid

variable [AddCommMonoid k] {a : G} {b : k}

/--
@isnad1 id=eq.1h4v.s5.00888d3418ca from=seed src=0 shape=635f27d5 vocab=b628f43b
-/
@[simp] lemma support_single (a : G) (h : b ≠ 0) : (single a b).support = {a} :=
  Finsupp.support_single _ h

/--
@isnad1 id=eq.1h4v.s5.00888d3418ca from=seed src=0 shape=635f27d5 vocab=b628f43b
-/
@[deprecated (since := "2026-05-05")] alias support_single_ne_zero := support_single

/--
@isnad1 id=le.0h4v.s5.3d0e3d5a64f9 from=seed src=0 shape=40f84c0e vocab=4d69cdf6
-/
theorem support_single_subset : (single a b).support ⊆ {a} := Finsupp.support_single_subset

/--
@isnad1 id=le.0h6v.s7.f836a73b533f from=seed src=0 shape=de19d6a2 vocab=eaa276c0
-/
theorem support_sum {k' G' : Type*} [DecidableEq G'] [AddCommMonoid k'] {f : SkewMonoidAlgebra k G}
    {g : G → k → SkewMonoidAlgebra k' G'} :
    (f.sum g).support ⊆ f.support.biUnion fun a ↦ (g a (f.coeff a)).support := by
  simp_rw [support, coeff_sum']
  apply Finsupp.support_sum

end AddCommMonoid

section AddCommGroup

variable [AddCommGroup k]

/--
@isnad1 id=eq.0h3v.s6.08b252b82f80 from=seed src=0 shape=b615d7aa vocab=22622d0f
-/
theorem support_neg (p : SkewMonoidAlgebra k G) : (-p).support = p.support := by
  rw [support, coeff_neg, Finsupp.support_neg, support_coeff]

end AddCommGroup

section AddCommMonoidWithOne

variable [One G] [AddCommMonoidWithOne k]

/--
@isnad1 id=le.0h2v.s6.fd5dee0d84e1 from=seed src=0 shape=ecea5480 vocab=a87556ef
-/
lemma support_one_subset : (1 : SkewMonoidAlgebra k G).support ⊆ 1 :=
  Finsupp.support_single_subset

/--
@isnad1 id=eq.0h2v.s6.37be4a72e3ca from=seed src=0 shape=9f34130e vocab=70c36448
-/
@[simp]
lemma support_one [NeZero (1 : k)] : (1 : SkewMonoidAlgebra k G).support = 1 :=
  Finsupp.support_single _ one_ne_zero

end AddCommMonoidWithOne

section Semiring

variable [Monoid G] [Semiring k] [MulSemiringAction G k]
variable (f g : SkewMonoidAlgebra k G)

section DecidableEq

variable [DecidableEq G]

/--
@isnad1 id=le.0h4v.s7.051540bbad1e from=seed src=0 shape=afb9be07 vocab=5f3d4618
-/
theorem support_mul : (f * g).support ⊆ f.support * g.support :=
  support_sum.trans <| biUnion_subset.2 fun _x hx ↦
    support_sum.trans <| biUnion_subset.2 fun _y hy ↦
      support_single_subset.trans <| singleton_subset_iff.2 <| mem_image₂_of_mem hx hy

/--
@isnad1 id=le.0h5v.s7.5ed74ee16639 from=seed src=0 shape=a9ee81ba vocab=0a345abc
-/
theorem support_single_mul_subset (r : k) (a : G) :
    (single a r * f : SkewMonoidAlgebra k G).support ⊆ Finset.image (a * ·) f.support :=
  (support_mul _ _).trans <| (Finset.image₂_subset_right support_single_subset).trans <| by
    rw [Finset.image₂_singleton_left]

/--
@isnad1 id=le.0h5v.s7.bc8bc411d140 from=seed src=0 shape=2d7a4b51 vocab=0a345abc
-/
theorem support_mul_single_subset (r : k) (a : G) :
    (f * single a r).support ⊆ Finset.image (· * a) f.support :=
  (support_mul _ _).trans <| (Finset.image₂_subset_left support_single_subset).trans <| by
    rw [Finset.image₂_singleton_right]

/--
@isnad1 id=eq.2h5v.s8.a9573acd01e2 from=seed src=0 shape=015a6db5 vocab=ad2ddd9b
-/
theorem support_single_mul_eq_image {r : k} {x : G} (lx : IsLeftRegular x)
    (hrx : ∀ y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = Finset.image (x * ·) f.support := by
  refine subset_antisymm (support_single_mul_subset f _ _) fun y hy ↦ ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ x * a = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, Ne,
    zero_mul, ite_self, sum_zero, lx.eq_iff]

/--
@isnad1 id=eq.2h5v.s8.ae7d316e8466 from=seed src=0 shape=9dae777b vocab=0738e3ed
-/
theorem support_mul_single_eq_image {r : k} {x : G} (rx : IsRightRegular x)
    (hrx : ∀ g : G, ∀ y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = Finset.image (· * x) f.support := by
  refine subset_antisymm (support_mul_single_subset f _ _) fun y hy ↦ ?_
  obtain ⟨y, yf, rfl⟩ : ∃ a : G, a ∈ f.support ∧ a * x = y := by
    simpa only [Finset.mem_image, exists_prop] using hy
  simp [coeff_mul, mem_support_iff.mp yf, hrx, mem_support_iff, sum_single_index, mul_zero,
    ite_self, rx.eq_iff]

end DecidableEq

/--
@isnad1 id=eq.1h5v.s8.bb61fc3cd792 from=seed src=0 shape=015a1126 vocab=580d2c2a
-/
theorem support_mul_single [IsRightCancelMul G] (r : k) (x : G)
    (hrx : ∀ g : G, ∀ y, y * g • r = 0 ↔ y = 0) :
    (f * single x r).support = f.support.map (mulRightEmbedding x) := by
  classical
  ext a
  simp [support_mul_single_eq_image f (IsRightRegular.all x) hrx]

/--
@isnad1 id=eq.1h5v.s8.0a5bf27d47cf from=seed src=0 shape=f7a79ae5 vocab=dfd7ab25
-/
theorem support_single_mul [IsLeftCancelMul G] (r : k) (x : G)
    (hrx : ∀ y, r * x • y = 0 ↔ y = 0) :
    (single x r * f : SkewMonoidAlgebra k G).support = f.support.map (mulLeftEmbedding x) := by
  classical
  ext a
  simp [support_single_mul_eq_image f (IsLeftRegular.all x) hrx]

section Span

/-- An element of `SkewMonoidAlgebra k G` is in the subalgebra generated by its support.
@isnad1 id=mem.0h3v.s8.166e595a16be from=seed src=0 shape=75873016 vocab=8daac999
-/
theorem mem_span_support (f : SkewMonoidAlgebra k G) :
    f ∈ Submodule.span k (of k G '' (f.support : Set G)) := by
  rw [Fintype.mem_span_image_iff_exists_fun k]
  use Finset.restrict f.support f.coeff
  simp [smul_single, ← sum_def', sum_single]

end Span

end Semiring

end SkewMonoidAlgebra
