/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Algebra.Homology.Ext.Basic

/-!
# `Ext` groups are invariant under an additive equivalence

Mathlib's `CategoryTheory.Adjunction.extEquiv` promotes an adjunction `F ⊣ G` between exact
functors to an additive equivalence `Extⁿ(F X, Y) ≃+ Extⁿ(X, G Y)`.  For an equivalence `e` this
specialises, along `CategoryTheory.Equivalence.toAdjunction` and the transport of the target along
the unit isomorphism from `TauCeti.extAddEquivOfIso`, to the invariance of `Ext` under `e`, which
Mathlib does not state in this form.  (`CategoryTheory.Abelian.Ext.mapExactFunctor` is shown
bijective only under a projective- or injective-object hypothesis.)

## Main definitions

* `CategoryTheory.Equivalence.extAddEquiv`: `Extⁿ(X, Y) ≃+ Extⁿ(e X, e Y)` for an additive
  equivalence `e`.
* `TauCeti.extLinearEquivOfEquivalence`: its `R`-linear refinement for an `R`-linear equivalence
  of `R`-linear abelian categories.  `R`-linearity of `e` is genuinely needed for the linear
  statement: an additive isomorphism of `k`-vector spaces need not preserve dimension.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

universe w v v' u u' t

variable {C : Type u} [Category.{v} C] [Abelian C] {D : Type u'} [Category.{v'} D] [Abelian D]
  [HasExt.{w} C] [HasExt.{w} D]

end TauCeti
