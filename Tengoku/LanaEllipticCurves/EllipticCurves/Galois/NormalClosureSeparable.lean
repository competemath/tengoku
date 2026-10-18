/-
Copyright (c) 2026 The Elliptic Curves formalisation contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Elliptic Curves formalisation contributors
-/
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.FieldTheory.Normal.Closure
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The normal closure of a separable extension is Galois

For a separable field extension `K / F`, the normal closure of `K` inside an algebraic closure of
`K` is a Galois extension of `F`.

⚠️ **Nothing about elliptic curves enters this file.**  It is stated for an arbitrary pair of
fields, and it imports nothing from this development — the `EllipticCurves`-import closure of this
module is empty, as it is for `EllipticCurves.Galois.SubfieldAut`.

## Why this file exists

*Finite and separable* is not *Galois*: normality is not transitive, so a tower of two Galois floors
need not be normal over the bottom.  The standard repair is to pass to the normal closure, and the
repair is what a Galois-descent argument consumes, because Hilbert 90 and the fixed-field theorem
both ask for `IsGalois`.

⚠️ **Mathlib's `IsGalois.normalClosure` does not prove this at the pin.**  It concludes
`IsGalois F (normalClosure F K L)` from `[IsGalois F L]` for the **ambient** field `L`, and the
ambient field here is an algebraic closure, which is normal over `F` but not separable over it in
characteristic `p`.  So the two halves are assembled by hand:

* **normality** is `normalClosure.normal`, over the algebraic closure;
* **separability** is `IntermediateField.isSeparable_iSup` read through
  `normalClosure F K L = ⨆ f : K →ₐ[F] L, f.fieldRange`, each summand being
  `AlgEquiv.ofInjectiveField`-isomorphic to `K` and so separable over `F` with it.

⚠️ **No finiteness is assumed, and that is a measured statement rather than a design choice.**
The lemma was first written with `[FiniteDimensional F K]` beside the separability, and `lake lint`
convicted it: *"1 unused argument: argument 7: `[FiniteDimensional F K]`"*.  Neither half of the
proof looks at the degree — `Algebra.IsSeparable F K` already carries algebraicity, which is all
`Algebra.IsAlgebraic.trans` needs — so the hypothesis is dropped rather than `nolint`-ed.
⚠️ A consumer wanting *finite* Galois, which is what Mathlib's Hilbert 90 asks for, gets the other
half from `IntermediateField.normalClosure.is_finiteDimensional` and its own
`[FiniteDimensional F K]`; **it is a separate instance and not a corollary of this lemma.**

## Main statements

* `isGalois_normalClosure_of_isSeparable`: for `K / F` separable,
  `IsGalois F (IntermediateField.normalClosure F K (AlgebraicClosure K))`.

Its three consumers in this development are `EllipticCurves.Torsion.HalvingExtension`, for the
halving field of a `2`-torsion point over its own base, `EllipticCurves.Torsion.HalvingGaloisTower`,
for the two-floor tower `F ⊆ Ψ₂Sq.SplittingField ⊆ halvingField` over the bottom field, and
`EllipticCurves.Torsion.ThreeDivisionField`, for the `3`-division field over `F`.  ⚠️ **The count
is `3` from the commit that adds the third**, not from the next round that happens to open this
file: the sentence is false the moment a consumer lands, and nothing else re-runs it.

## What is *not* here

* **The normal closure inside an arbitrary ambient field.**  The statement below fixes the ambient
  field to `AlgebraicClosure K`; nothing here is said about `normalClosure F K L` for another `L`,
  and a consumer holding a different ambient field has to transport by hand.
* **An upstream candidate, stated as such.**  This is a gap in the pinned Mathlib rather than a
  statement about this development, and it is offered as it stands.  ⚠️ It has **not** been checked
  against Mathlib master, only against the pin.
* **Finiteness of the closure.**  Nothing below says `normalClosure F K (AlgebraicClosure K)` is
  finite over `F`; that is `IntermediateField.normalClosure.is_finiteDimensional`, it needs
  `[FiniteDimensional F K]`, and a consumer wanting *finite Galois* has to ask for both.
-/

open IntermediateField

/-- **The normal closure of a separable extension is Galois.**

For `K / F` separable, `normalClosure F K (AlgebraicClosure K)` is a Galois extension of `F`.
⚠️ Assembled by hand rather than taken from `IsGalois.normalClosure`, which needs the **ambient**
extension to be Galois over `F`; an algebraic closure is normal but not separable over `F` in
characteristic `p`.  ⚠️ **No finiteness anywhere**: see the module docstring for the `lake lint`
run that removed it. -/
theorem isGalois_normalClosure_of_isSeparable (F K : Type*) [Field F] [Field K] [Algebra F K]
    [Algebra.IsSeparable F K] :
    IsGalois F (normalClosure F K (AlgebraicClosure K)) := by
  haveI : Algebra.IsAlgebraic F (AlgebraicClosure K) :=
    Algebra.IsAlgebraic.trans F K (AlgebraicClosure K)
  haveI : IsAlgClosure F (AlgebraicClosure K) := ⟨inferInstance, inferInstance⟩
  haveI : Normal F (AlgebraicClosure K) := IsAlgClosure.normal _ _
  haveI : Normal F (normalClosure F K (AlgebraicClosure K)) :=
    normalClosure.normal F K (AlgebraicClosure K)
  haveI : Algebra.IsSeparable F ↥(normalClosure F K (AlgebraicClosure K)) := by
    haveI : ∀ f : K →ₐ[F] (AlgebraicClosure K), Algebra.IsSeparable F ↥f.fieldRange :=
      fun f => AlgEquiv.Algebra.isSeparable (AlgEquiv.ofInjectiveField f)
    change Algebra.IsSeparable F ↥(⨆ f : K →ₐ[F] (AlgebraicClosure K), f.fieldRange)
    infer_instance
  exact ⟨⟩
