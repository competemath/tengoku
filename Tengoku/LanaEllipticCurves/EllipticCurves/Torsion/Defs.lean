/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.Algebra.Module.Torsion.Basic
import Tengoku.Seed.AlgebraicGeometry.EllipticCurve.Affine.Point

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The `n`-torsion subgroup `E[n]` of a Weierstrass curve

For a Weierstrass curve `W` over a field `F`, the group of affine points `W.Point`
(`WeierstrassCurve.Affine.Point`) carries an `AddCommGroup` structure. Mathlib already provides the
`n`-torsion subgroup of an arbitrary additive commutative group `A` as `AddSubgroup.torsionBy`, with
the scoped notation `A[n]` for `n : ℤ` and the membership characterisation
`AddSubgroup.torsionBy.nsmul_iff`.

This file records the small pieces of general API that are still missing at the
`AddSubgroup.torsionBy` level (the values at `0` and `1`, and monotonicity in the divisibility
order), and specialises the construction to Weierstrass curves as
`WeierstrassCurve.Affine.torsion W n`, the `n`-torsion subgroup `E[n]` — equivalently the kernel of
multiplication by `n` on `W.Point`.

The finiteness of `E[n]` and the structure theorem `E[n] ≃ (ℤ/nℤ)²` require relating torsion points
to the division polynomials, and are developed separately.

## Main definitions

* `WeierstrassCurve.Affine.torsion W n`: the `n`-torsion subgroup `E[n]` of `W.Point`.

## Main statements

* `WeierstrassCurve.Affine.mem_torsion_iff`: `P ∈ E[n] ↔ n • P = 0`.
* `WeierstrassCurve.Affine.add_self_eq_zero_of_mem_torsion_two`,
  `WeierstrassCurve.Affine.add_add_self_eq_zero_of_mem_torsion_three`: the same membership at
  `n = 2` and `n = 3` in the *additive* form `P ⊕ P = O`, `P ⊕ P ⊕ P = O`, which is the shape the
  translation and Weil-pairing files consume as a hypothesis binder.
* `WeierstrassCurve.Affine.torsion_zero`, `WeierstrassCurve.Affine.torsion_one`:
  `E[0] = ⊤` and `E[1] = ⊥`.
* `WeierstrassCurve.Affine.torsion_mono`: `m ∣ n → E[m] ≤ E[n]`.

## ⚠️ One `@[simp]` attribute was removed here, and the lemma kept (`#1278`)

`nsmul_mem_torsion` carried `@[simp]`, and it is a **straight duplicate of Mathlib's
`AddSubgroup.torsionBy.nsmul`**, which is already `@[simp]` — so the default simp set proves it and
the attribute only added a second entry for the same rewrite. Measured with Mathlib's `simpNF`
environment linter, which had never been run on this tree. ⚠️ The lemma is kept and unchanged: it
has eleven named consumers across five files, and the point of the name is to state the fact in
`W.torsion` vocabulary rather than `AddSubgroup.torsionBy`.
-/

open scoped AddSubgroup

namespace AddSubgroup

variable {A : Type*} [AddCommGroup A]

/-- Membership in the integer `n`-torsion subgroup: `a ∈ A[n] ↔ n • a = 0`. -/
lemma torsionBy.zsmul_iff {n : ℤ} {a : A} : a ∈ A[n] ↔ n • a = 0 := by
  rw [torsionBy, Submodule.mem_toAddSubgroup, Submodule.mem_torsionBy_iff]

/-- The `0`-torsion subgroup is the whole group, since `0 • a = 0` for every `a`. -/
@[simp]
lemma torsionBy_zero : A[(0 : ℤ)] = ⊤ := by
  ext a
  simp

/-- The `1`-torsion subgroup is trivial. -/
@[simp]
lemma torsionBy_one : A[(1 : ℤ)] = ⊥ := by
  ext a
  simp only [torsionBy.zsmul_iff, one_smul, AddSubgroup.mem_bot]

/-- The integer torsion subgroups are monotone in the divisibility order:
if `m ∣ n` then `A[m] ≤ A[n]`. -/
lemma torsionBy_le_torsionBy_of_dvd {m n : ℤ} (h : m ∣ n) : A[m] ≤ A[n] := by
  intro a ha
  rw [torsionBy.zsmul_iff] at ha ⊢
  obtain ⟨k, rfl⟩ := h
  rw [mul_comm, mul_smul, ha, smul_zero]

end AddSubgroup

namespace WeierstrassCurve.Affine

variable {F : Type*} [Field F] [DecidableEq F]

variable (W : Affine F) in
/-- The `n`-torsion subgroup `E[n]` of a Weierstrass curve `W` over a field `F`: the subgroup of
points `P` of `W` with `n • P = 0`, i.e. the kernel of multiplication by `n` on `W.Point`. -/
abbrev torsion (n : ℕ) : AddSubgroup W.Point :=
  W.Point[(n : ℤ)]

variable {W : Affine F}

/-- A point lies in `E[n]` exactly when it is killed by multiplication by `n`. -/
lemma mem_torsion_iff {n : ℕ} {P : W.Point} : P ∈ W.torsion n ↔ n • P = 0 :=
  AddSubgroup.torsionBy.nsmul_iff

lemma nsmul_mem_torsion {n : ℕ} (P : W.torsion n) : n • P = 0 :=
  AddSubgroup.torsionBy.nsmul P

/-- `E[2]` membership as the two-term group relation `P ⊕ P = O`.

`mem_torsion_iff` states it as `2 • P = 0`, but the consumers in `FunctionField/` — the translation
and Weil-pairing files — take the additive form as a hypothesis binder, e.g.
`weilPairingElt_pow_eq_one_of_gS_two_torsion` asks for
`torsionPoint hT + torsionPoint hT = 0`.  ⚠️ This is deliberately *not* routed through
`mem_torsion_two_some_iff` (`EllipticCurves.Torsion.TwoTorsion`), which gives the different normal
form `P = -P`: reaching `P ⊕ P = O` from there costs an extra `add_eq_zero_iff_eq_neg` at every
site, which is why no consumer used it. -/
lemma add_self_eq_zero_of_mem_torsion_two {P : W.Point} (h : P ∈ W.torsion 2) :
    P + P = 0 := by
  have hn := mem_torsion_iff.mp h
  rwa [two_nsmul] at hn

/-- `E[3]` membership as the three-term group relation `P ⊕ P ⊕ P = O`.

The `n = 3` twin of `add_self_eq_zero_of_mem_torsion_two`, wanted for the same reason: it is the
hypothesis binder of `weilPairingElt_pow_eq_one_of_gS_three_baseField` and of the `3`-torsion
translation lemmas.  ⚠️ As at `n = 2`, this is not the same normal form as
`mem_torsion_three_iff_add_self_eq_neg` (`EllipticCurves.Torsion.ThreeTorsion`), which says
`P ⊕ P = ⊖P`. -/
lemma add_add_self_eq_zero_of_mem_torsion_three {P : W.Point} (h : P ∈ W.torsion 3) :
    P + P + P = 0 := by
  have hn := mem_torsion_iff.mp h
  rwa [show (3 : ℕ) = 2 + 1 from rfl, add_smul, two_nsmul, one_nsmul] at hn

/-- The `0`-torsion subgroup `E[0]` is the whole group of points. -/
@[simp]
lemma torsion_zero : W.torsion 0 = ⊤ := by
  ext P
  simp

/-- The `1`-torsion subgroup `E[1]` is trivial. -/
@[simp]
lemma torsion_one : W.torsion 1 = ⊥ := by
  ext P
  simp

/-- The torsion subgroups are monotone in the divisibility order: `m ∣ n → E[m] ≤ E[n]`. -/
lemma torsion_mono {m n : ℕ} (h : m ∣ n) : W.torsion m ≤ W.torsion n :=
  AddSubgroup.torsionBy_le_torsionBy_of_dvd (Int.natCast_dvd_natCast.mpr h)

end WeierstrassCurve.Affine
