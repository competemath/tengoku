/-
Copyright (c) 2026 Junyan Xu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Junyan Xu
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Analysis.Calculus.Deriv.Polynomial
public import Tengoku.Seed.Analysis.SpecialFunctions.Complex.LogDeriv
public import Tengoku.Seed.Analysis.SpecialFunctions.Pow.Complex
public import Tengoku.Seed.RingTheory.RootsOfUnity.Basic
public import Tengoku.Seed.Topology.Algebra.Polynomial
public import Tengoku.Seed.Topology.Covering.Quotient
public import Tengoku.Seed.Topology.LocalAtTarget
public import Tengoku.Seed.Topology.GDelta.MetrizableSpace

/-!
# Covering maps involving the complex plane

In this file, we show that `Complex.exp` and `(· ^ n)` (for `n ≠ 0`) are a covering map on `{0}ᶜ`.
We also show that any complex polynomial is a covering map on the set of regular values.
-/

public section

open Topology

namespace Complex

/--
@isnad1 id=isaddquo.0h0v.s7.a7c3a254a9e7 from=seed src=0 shape=afb78ddb vocab=92c4c2f8
-/
theorem isAddQuotientCoveringMap_exp :
    IsAddQuotientCoveringMap (fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}))
      (AddSubgroup.zmultiples (2 * Real.pi * I)) := by
  refine Topology.IsQuotientMap.isAddQuotientCoveringMap_of_addSubgroup ?_
    _ ⟨NormedSpace.discreteTopology_zmultiples _⟩ fun {z _} ↦ ?_
  · refine IsOpenMap.isQuotientMap ?_ (by fun_prop) fun z ↦ ⟨_, Subtype.ext (exp_log z.2)⟩
    exact (IsOpen.isOpenEmbedding_subtypeVal isClosed_singleton.1).isOpenMap_iff.mpr isOpenMap_exp
  · simp_rw [Subtype.ext_iff, eq_comm (a := exp z), exp_eq_exp_iff_exists_int,
      AddSubgroup.mem_zmultiples_iff, eq_add_neg_iff_add_eq, eq_comm, add_comm, zsmul_eq_mul]

/-- `exp : ℂ → ℂ \ {0}` is a covering map.
@isnad1 id=iscoveri.0h0v.s6.fac1d3598270 from=seed src=0 shape=2c5d8b67 vocab=aecf675f
-/
theorem isCoveringMap_exp : IsCoveringMap fun z : ℂ ↦ (⟨_, z.exp_ne_zero⟩ : {z : ℂ // z ≠ 0}) :=
  isAddQuotientCoveringMap_exp.isCoveringMap

/--
@isnad1 id=iscoveri.0h0v.s5.9380aeada7f7 from=seed src=0 shape=88fb288c vocab=2602af47
-/
theorem isCoveringMapOn_exp : IsCoveringMapOn Complex.exp {0}ᶜ :=
  .of_isCoveringMap_subtype (by simp) _ isCoveringMap_exp

end Complex

section

open Polynomial

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] [ProperSpace 𝕜]

/--
@isnad1 id=iscoveri.0h2v.s9.e181e4c28eb1 from=seed src=0 shape=c00d5f3a vocab=d1dfb930
-/
theorem Polynomial.isCoveringMapOn_eval (p : 𝕜[X]) :
    IsCoveringMapOn p.eval (p.eval '' {k | p.derivative.eval k = 0})ᶜ := by
  refine p.isClosedMap_eval.isCoveringMapOn_of_isLocalHomeomorphOn (fun x hx ↦ ?_)
    fun x hx ↦ ⟨_, ((p.hasStrictDerivAt x).hasStrictFDerivAt_equiv
      fun h ↦ hx ⟨x, h, rfl⟩).mem_toOpenPartialHomeomorph_source, by simp⟩
  obtain rfl | ne := eq_or_ne p (C x)
  · simp at hx
  · simpa only [preimage_eval_singleton ne] using rootSet_finite ..

/--
@isnad1 id=iscoveri.1h2v.s7.69f8d0bdc995 from=seed src=0 shape=5a061a5f vocab=ffe989c2
-/
theorem isCoveringMapOn_npow (n : ℕ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMapOn (fun x : 𝕜 ↦ x ^ n) {0}ᶜ := by
  convert! (X ^ n).isCoveringMapOn_eval.mono fun x' h ↦ _ with x
  · simp
  · assumption
  · simpa [derivative_X_pow, hn, show n ≠ 0 by aesop] using fun _ ↦ Ne.symm h

/-- `(· ^ n) : 𝕜 \ {0} → 𝕜 \ {0}` is a covering map (if `n ≠ 0` in `𝕜`).
@isnad1 id=iscoveri.1h2v.s8.3d71f3fc261d from=seed src=0 shape=6ceebff7 vocab=e9b2d612
-/
theorem isCoveringMap_npow (n : ℕ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMap fun x : {x : 𝕜 // x ≠ 0} ↦ (⟨x ^ n, pow_ne_zero n x.2⟩ : {x : 𝕜 // x ≠ 0}) := by
  convert!
    (isCoveringMapOn_npow n hn).isCoveringMap_restrictPreimage.comp_homeomorph
      (.setCongr (s := {x | x ≠ 0}) _) using 1
  ext; simp [show n ≠ 0 by aesop]

/-- `(· ^ n) : 𝕜 \ {0} → 𝕜 \ {0}` is a covering map (if `n ≠ 0` in `𝕜`).
@isnad1 id=iscoveri.1h2v.s8.65612b9df4d5 from=seed src=0 shape=6ceebff7 vocab=2bfc779d
-/
theorem isCoveringMap_zpow (n : ℤ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMap fun x : {x : 𝕜 // x ≠ 0} ↦ (⟨x ^ n, zpow_ne_zero n x.2⟩ : {x : 𝕜 // x ≠ 0}) := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · convert! isCoveringMap_npow n _ <;> aesop
  · convert! (isCoveringMap_npow n _).comp_homeomorph (.inv₀ 𝕜)
    · simp [Homeomorph.inv₀]
    · simpa using hn

/--
@isnad1 id=iscoveri.1h2v.s7.0e112dce2ccd from=seed src=0 shape=5a061a5f vocab=3f04f08a
-/
theorem isCoveringMapOn_zpow (n : ℤ) (hn : (n : 𝕜) ≠ 0) :
    IsCoveringMapOn (fun x : 𝕜 ↦ x ^ n) {0}ᶜ := by
  have (x : 𝕜) : x ^ n = 0 ↔ x = 0 := zpow_eq_zero_iff (by aesop)
  refine .of_isCoveringMap_restrictPreimage _ (by simp) ?_ ?_
  · convert isClosed_singleton (x := (0 : 𝕜)).isOpen_compl
    ext; simp [this]
  · convert! (isCoveringMap_zpow n hn).comp_homeomorph (.setCongr _) using 1
    ext; simpa using! (this _).not

attribute [-instance] Units.mulAction'

/--
@isnad1 id=isquotie.2h2v.s9.3782956cc9b9 from=seed src=0 shape=4890b5cd vocab=202ae008
-/
theorem isQuotientCoveringMap_npow (n : ℕ) (hn : (n : 𝕜) ≠ 0)
    (surj : (fun x : 𝕜 ↦ x ^ n).Surjective) :
    IsQuotientCoveringMap (fun x : 𝕜ˣ ↦ x ^ n) (powMonoidHom (α := 𝕜ˣ) n).ker := by
  rw [← rootsOfUnity_eq_ker]
  have : NeZero n := ⟨by aesop⟩
  have := ((isClosedMap_pow 𝕜 n).restrictPreimage {0}ᶜ).isQuotientMap
    (by fun_prop) (.restrictPreimage _ surj)
  have : IsQuotientMap fun x : 𝕜ˣ ↦ x ^ n := by
    let e := unitsHomeomorphNeZero (G₀ := 𝕜)
    convert! (e.symm.isQuotientMap.comp this).comp (e.trans (.ofEqSubtypes _)).isQuotientMap
    · exact (e.left_inv _).symm
    · ext; simp [NeZero.ne]
  refine this.isQuotientCoveringMap_of_subgroup _
    (Set.Finite.isDiscrete <| inferInstanceAs (Finite (rootsOfUnity ..))) ?_
  simp [mul_pow, mul_inv_eq_one, eq_comm]

/--
@isnad1 id=isquotie.0h1v.s8.c9e8580650ff from=seed src=0 shape=c6e0652f vocab=ac8198b1
-/
protected theorem Complex.isQuotientCoveringMap_npow (n : ℕ) [NeZero n] :
    IsQuotientCoveringMap (fun z : ℂˣ ↦ z ^ n) (powMonoidHom (α := ℂˣ) n).ker :=
  isQuotientCoveringMap_npow n (by simp [NeZero.ne]) fun _ ↦ ⟨_, cpow_nat_inv_pow _ (NeZero.ne n)⟩

/--
@isnad1 id=isquotie.2h2v.s9.f9b426b283e6 from=seed src=0 shape=4890b5cd vocab=68ee9382
-/
theorem isQuotientCoveringMap_zpow (n : ℤ) (hn : (n : 𝕜) ≠ 0)
    (surj : (fun x : 𝕜 ↦ x ^ n).Surjective) :
    IsQuotientCoveringMap (fun x : 𝕜ˣ ↦ x ^ n) (zpowGroupHom (α := 𝕜ˣ) n).ker := by
  obtain ⟨n, rfl | rfl⟩ := n.eq_nat_or_neg
  · exact isQuotientCoveringMap_npow n (by aesop) (by simpa using surj)
  rw [show (zpowGroupHom (α := 𝕜ˣ) (-n)).ker = (powMonoidHom n).ker by ext; simp]
  convert (isQuotientCoveringMap_npow n (by aesop) _).homeomorph_comp (.inv 𝕜ˣ)
  · ext; simp
  convert! inv_involutive.surjective.comp surj; simp

end
