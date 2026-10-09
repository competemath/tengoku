/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.ContDiff.Comp
public import Tengoku.Seed.Analysis.Calculus.IteratedDeriv.Defs

/-!
# Iterated derivatives of compositions

In this file we specialize Faà di Bruno's formula to one-dimensional domain
to deduce formulae for `iteratedDerivWithin k (g ∘ f) s x` for `k = 2` and `k = 3`.

We use
- `vcomp` for lemmas about the composition of `g : E → F` with `f : 𝕜 → E`;
- `scomp` for lemmas about the composition of `g : 𝕜 → E` with `f : 𝕜 → 𝕜`;
- `comp` for lemmas about the composition of `g : 𝕜 → 𝕜` with `f : 𝕜 → 𝕜`.

## TODO

- What `UniqueDiffOn` assumptions can be discarded?
- In case of dimension 1 (and, more generally, in case of symmetric iterated derivatives),
  some terms are equal.
  Add versions of Faà di Bruno's formula that take the symmetries into account.
- Can we generalize `scomp`/`comp` to `f : 𝕜 → 𝕜'`,
  where `𝕜'` is a normed algebra over `𝕜`? E.g., `𝕜 = ℝ`, `𝕜' = ℂ`.

Before starting to work on these TODOs, please contact Yury Kudryashov
who may have partial progress towards some of them.
-/

public section

open Function Set
open scoped ContDiff

section vcomp

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  {g : E → F} {f : 𝕜 → E} {s : Set 𝕜} {t : Set E} {x : 𝕜} {n : ℕ∞ω} {i : ℕ}

/--
@isnad1 id=eq.7h10v.s8.ca1d458103d5 from=seed src=0 shape=2be30abd vocab=e1a700b5
-/
theorem iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) (hi : i ≤ n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i, iteratedFDerivWithin 𝕜 c.length g t (f x) fun j ↦
        iteratedDerivWithin (c.partSize j) f s x := by
  simp only [iteratedDerivWithin, iteratedFDerivWithin_comp hg hf ht hs hx hst hi]
  simp [FormalMultilinearSeries.taylorComp, ftaylorSeriesWithin,
    OrderedFinpartition.applyOrderedFinpartition_apply, comp_def]

/--
@isnad1 id=eq.3h8v.s8.2192825b8a3d from=seed src=0 shape=b0c8eac1 vocab=fdca5b28
-/
theorem iteratedDeriv_vcomp_eq_sum_orderedFinpartition
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : i ≤ n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i, iteratedFDeriv 𝕜 c.length g (f x) fun j ↦
        iteratedDeriv (c.partSize j) f x := by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ]
  exact iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _) hi

set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.6h8v.s9.2fb9e6115f84 from=seed src=0 shape=a8323c3f vocab=efe65158
-/
theorem iteratedDerivWithin_vcomp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      iteratedFDerivWithin 𝕜 2 g t (f x) (fun _ ↦ derivWithin f s x) +
      fderivWithin 𝕜 g t (f x) (iteratedDerivWithin 2 f s x) := by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp, Fintype.sum_sigma, Fintype.sum_unique,
    OrderedFinpartition.default_eq, Fintype.sum_option]
  have : (Fin.cons 1 (fun _ ↦ 1) : Fin 2 → ℕ) = fun _ ↦ 1 :=
    funext <| Fin.forall_fin_two.mpr ⟨rfl, rfl⟩
  simp [OrderedFinpartition.extendEquiv, OrderedFinpartition.extend,
    OrderedFinpartition.extendLeft, OrderedFinpartition.extendMiddle, ht _ (hst hx),
    OrderedFinpartition.atomic, this]

/--
@isnad1 id=eq.2h6v.s9.3baa910b05cf from=seed src=0 shape=898738a5 vocab=71584637
-/
theorem iteratedDeriv_vcomp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    iteratedDeriv 2 (g ∘ f) x =
      iteratedFDeriv 𝕜 2 g (f x) (fun _ ↦ deriv f x) + fderiv 𝕜 g (f x) (iteratedDeriv 2 f x) := by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_two hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/--
@isnad1 id=eq.6h8v.s10.dda73a504d53 from=seed src=0 shape=d042012e vocab=7e99702e
-/
theorem iteratedDerivWithin_vcomp_three
    (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 3 (g ∘ f) s x =
      iteratedFDerivWithin 𝕜 3 g t (f x) (fun _ ↦ derivWithin f s x) +
      iteratedFDerivWithin 𝕜 2 g t (f x) ![iteratedDerivWithin 2 f s x, derivWithin f s x] +
      2 • iteratedFDerivWithin 𝕜 2 g t (f x) ![derivWithin f s x, iteratedDerivWithin 2 f s x] +
      fderivWithin 𝕜 g t (f x) (iteratedDerivWithin 3 f s x) := by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst le_rfl]
  simp only [← (OrderedFinpartition.extendEquiv 1).sum_comp,
    ← (OrderedFinpartition.extendEquiv 2).sum_comp, Fintype.sum_sigma,
    Fintype.sum_option, Nat.reduceAdd, OrderedFinpartition.extendEquiv_apply,
    OrderedFinpartition.extend_none, OrderedFinpartition.extend_some,
    OrderedFinpartition.extendMiddle_length, OrderedFinpartition.default_eq, Fintype.sum_unique,
    OrderedFinpartition.atomic_length, OrderedFinpartition.extendLeft_length, Fin.sum_univ_two]
  simp? [add_assoc, two_smul, iteratedFDerivWithin_one_apply (ht _ <| hst hx)] says
    simp only [OrderedFinpartition.extendLeft_partSize, OrderedFinpartition.extendLeft_length,
      OrderedFinpartition.atomic_length, Nat.reduceAdd, OrderedFinpartition.atomic_partSize,
      Fin.isValue, OrderedFinpartition.extendMiddle_partSize, Fin.cons_zero, Fin.update_cons_zero,
      Fin.cons_one, Fin.default_eq_zero, OrderedFinpartition.extendMiddle_length, Fin.cons_update,
      Fin.succ_zero_eq_one, update_self, update_idem,
      iteratedFDerivWithin_one_apply (ht _ <| hst hx), add_assoc, two_smul]
  have (j : _) : (Fin.cons 1 (Fin.cons 1 fun _ ↦ 1) : Fin 3 → ℕ) j = 1 := by
    fin_cases j <;> rfl
  congr <;> ext x <;> fin_cases x <;> simp [this]

/--
@isnad1 id=eq.2h6v.s10.460d21a84c5a from=seed src=0 shape=ec5d8a7c vocab=b39106e9
-/
theorem iteratedDeriv_vcomp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x) :
    iteratedDeriv 3 (g ∘ f) x =
      iteratedFDeriv 𝕜 3 g (f x) (fun _ ↦ deriv f x) +
      iteratedFDeriv 𝕜 2 g (f x) ![iteratedDeriv 2 f x, deriv f x] +
      2 • iteratedFDeriv 𝕜 2 g (f x) ![deriv f x, iteratedDeriv 2 f x] +
      fderiv 𝕜 g (f x) (iteratedDeriv 3 f x) := by
  simp only [← iteratedDerivWithin_univ, ← iteratedFDerivWithin_univ,
    ← derivWithin_univ, ← fderivWithin_univ]
  exact iteratedDerivWithin_vcomp_three hg hf uniqueDiffOn_univ
    uniqueDiffOn_univ (mem_univ x) (mapsTo_univ f _)

end vcomp

section scomp

variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {g : 𝕜 → E} {f : 𝕜 → 𝕜} {s : Set 𝕜} {t : Set 𝕜} {x : 𝕜} {n : ℕ∞ω} {i : ℕ}

/--
@isnad1 id=eq.7h9v.s8.05f07fac0ed5 from=seed src=0 shape=82788ade vocab=c89544e0
-/
theorem iteratedDerivWithin_scomp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) (hi : i ≤ n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i,
        (∏ j, iteratedDerivWithin (c.partSize j) f s x) •
          iteratedDerivWithin c.length g t (f x) := by
  rw [iteratedDerivWithin_vcomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]

/--
@isnad1 id=eq.3h7v.s8.d787e068e97d from=seed src=0 shape=2f55336e vocab=c059e444
-/
theorem iteratedDeriv_scomp_eq_sum_orderedFinpartition
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : i ≤ n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i,
        (∏ j, iteratedDeriv (c.partSize j) f x) • iteratedDeriv c.length g (f x) := by
  rw [iteratedDeriv_vcomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod]

/--
@isnad1 id=eq.6h7v.s9.6c5b17abce4b from=seed src=0 shape=8e2ad24a vocab=199a3193
-/
theorem iteratedDerivWithin_scomp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      derivWithin f s x ^ 2 • iteratedDerivWithin 2 g t (f x) +
      iteratedDerivWithin 2 f s x • derivWithin g t (f x) := by
  rw [iteratedDerivWithin_vcomp_two hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]

/--
@isnad1 id=eq.2h5v.s8.0ac0e6b4995e from=seed src=0 shape=faea4007 vocab=0d8cb97a
-/
theorem iteratedDeriv_scomp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    iteratedDeriv 2 (g ∘ f) x
      = deriv f x ^ 2 • iteratedDeriv 2 g (f x) + iteratedDeriv 2 f x • deriv g (f x) := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

/--
@isnad1 id=eq.6h7v.s9.6d140756d3c2 from=seed src=0 shape=1f799688 vocab=199a3193
-/
theorem iteratedDerivWithin_scomp_three
    (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 3 (g ∘ f) s x =
      derivWithin f s x ^ 3 • iteratedDerivWithin 3 g t (f x) +
      3 • iteratedDerivWithin 2 f s x • derivWithin f s x • iteratedDerivWithin 2 g t (f x) +
      iteratedDerivWithin 3 f s x • derivWithin g t (f x) := by
  rw [iteratedDerivWithin_vcomp_three hg hf ht hs hx hst]
  simp [← toSpanSingleton_derivWithin, mul_smul, smul_comm (iteratedDerivWithin 2 f s x),
        iteratedFDerivWithin_apply_eq_iteratedDerivWithin_mul_prod]
  abel

/--
@isnad1 id=eq.2h5v.s9.bb6efaf59865 from=seed src=0 shape=c699db1b vocab=0d8cb97a
-/
theorem iteratedDeriv_scomp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x) :
    iteratedDeriv 3 (g ∘ f) x =
      deriv f x ^ 3 • iteratedDeriv 3 g (f x) +
      3 • iteratedDeriv 2 f x • deriv f x • iteratedDeriv 2 g (f x) +
      iteratedDeriv 3 f x • deriv g (f x) := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_scomp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

end scomp

section comp

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {g f : 𝕜 → 𝕜} {s t : Set 𝕜} {x : 𝕜} {n : ℕ∞ω} {i : ℕ}

/--
@isnad1 id=eq.7h8v.s8.36f49c36c829 from=seed src=0 shape=8d5e3f4b vocab=745666ec
-/
theorem iteratedDerivWithin_comp_eq_sum_orderedFinpartition
    (hg : ContDiffWithinAt 𝕜 n g t (f x)) (hf : ContDiffWithinAt 𝕜 n f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) (hi : i ≤ n) :
    iteratedDerivWithin i (g ∘ f) s x =
      ∑ c : OrderedFinpartition i,
        iteratedDerivWithin c.length g t (f x) * ∏ j, iteratedDerivWithin (c.partSize j) f s x := by
  rw [iteratedDerivWithin_scomp_eq_sum_orderedFinpartition hg hf ht hs hx hst hi]
  simp only [smul_eq_mul, mul_comm]

/--
@isnad1 id=eq.3h6v.s8.8d6678c12894 from=seed src=0 shape=8041feaf vocab=3b7aeca2
-/
theorem iteratedDeriv_comp_eq_sum_orderedFinpartition
    (hg : ContDiffAt 𝕜 n g (f x)) (hf : ContDiffAt 𝕜 n f x) (hi : i ≤ n) :
    iteratedDeriv i (g ∘ f) x =
      ∑ c : OrderedFinpartition i,
        iteratedDeriv c.length g (f x) * ∏ j, iteratedDeriv (c.partSize j) f x := by
  rw [iteratedDeriv_scomp_eq_sum_orderedFinpartition hg hf hi]
  simp only [smul_eq_mul, mul_comm]

/--
@isnad1 id=eq.6h6v.s9.54ec18a3f410 from=seed src=0 shape=64eebea7 vocab=9dce3f3b
-/
theorem iteratedDerivWithin_comp_two
    (hg : ContDiffWithinAt 𝕜 2 g t (f x)) (hf : ContDiffWithinAt 𝕜 2 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 2 (g ∘ f) s x =
      iteratedDerivWithin 2 g t (f x) * derivWithin f s x ^ 2 +
      derivWithin g t (f x) * iteratedDerivWithin 2 f s x := by
  rw [iteratedDerivWithin_scomp_two hg hf ht hs hx hst]
  simp only [smul_eq_mul, mul_comm]

/--
@isnad1 id=eq.2h4v.s8.56fa36ad7231 from=seed src=0 shape=56ed75b7 vocab=19d49d5e
-/
theorem iteratedDeriv_comp_two (hg : ContDiffAt 𝕜 2 g (f x)) (hf : ContDiffAt 𝕜 2 f x) :
    iteratedDeriv 2 (g ∘ f) x =
      iteratedDeriv 2 g (f x) * deriv f x ^ 2 + deriv g (f x) * iteratedDeriv 2 f x := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_two hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

/--
@isnad1 id=eq.6h6v.s9.0f72611828f3 from=seed src=0 shape=8e443ccf vocab=9dce3f3b
-/
theorem iteratedDerivWithin_comp_three
    (hg : ContDiffWithinAt 𝕜 3 g t (f x)) (hf : ContDiffWithinAt 𝕜 3 f s x)
    (ht : UniqueDiffOn 𝕜 t) (hs : UniqueDiffOn 𝕜 s) (hx : x ∈ s) (hst : MapsTo f s t) :
    iteratedDerivWithin 3 (g ∘ f) s x =
      iteratedDerivWithin 3 g t (f x) * derivWithin f s x ^ 3 +
      3 * iteratedDerivWithin 2 g t (f x) * iteratedDerivWithin 2 f s x * derivWithin f s x +
      derivWithin g t (f x) * iteratedDerivWithin 3 f s x := by
  rw [iteratedDerivWithin_scomp_three hg hf ht hs hx hst]
  simp only [nsmul_eq_mul, smul_eq_mul, Nat.cast_ofNat]
  ring

/--
@isnad1 id=eq.2h4v.s9.f9c071c2bc58 from=seed src=0 shape=0e03c760 vocab=19d49d5e
-/
theorem iteratedDeriv_comp_three (hg : ContDiffAt 𝕜 3 g (f x)) (hf : ContDiffAt 𝕜 3 f x) :
    iteratedDeriv 3 (g ∘ f) x =
      iteratedDeriv 3 g (f x) * deriv f x ^ 3 +
      3 * iteratedDeriv 2 g (f x) * iteratedDeriv 2 f x * deriv f x +
      deriv g (f x) * iteratedDeriv 3 f x := by
  simp only [← iteratedDerivWithin_univ, ← derivWithin_univ]
  exact iteratedDerivWithin_comp_three hg hf uniqueDiffOn_univ uniqueDiffOn_univ (mem_univ _)
    (mapsTo_univ _ _)

end comp
