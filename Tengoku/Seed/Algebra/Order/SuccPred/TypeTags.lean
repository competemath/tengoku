/-
Copyright (c) 2024 Yakov Pechersky. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yakov Pechersky
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Order.SuccPred.Archimedean
public import Tengoku.Seed.Algebra.Order.Monoid.Unbundled.TypeTags

/-!
# Successor and predecessor on type tags

This file declares successor and predecessor orders on type tags.

-/

public section

variable {X : Type*}

instance [Preorder X] [h : SuccOrder X] : SuccOrder (Multiplicative X) := h
instance [Preorder X] [h : SuccOrder X] : SuccOrder (Additive X) := h

instance [Preorder X] [h : PredOrder X] : PredOrder (Multiplicative X) := h
instance [Preorder X] [h : PredOrder X] : PredOrder (Additive X) := h

instance [Preorder X] [SuccOrder X] [h : IsSuccArchimedean X] :
    IsSuccArchimedean (Multiplicative X) := h
instance [Preorder X] [SuccOrder X] [h : IsSuccArchimedean X] :
    IsSuccArchimedean (Additive X) := h

instance [Preorder X] [PredOrder X] [h : IsPredArchimedean X] :
    IsPredArchimedean (Multiplicative X) := h
instance [Preorder X] [PredOrder X] [h : IsPredArchimedean X] :
    IsPredArchimedean (Additive X) := h

namespace Order

open Additive Multiplicative

/--
@isnad1 id=eq.0h2v.s6.8de71593bf64 from=seed src=0 shape=dcd63932 vocab=04fe3394
-/
@[simp] lemma succ_ofMul [Preorder X] [SuccOrder X] (x : X) : succ (ofMul x) = ofMul (succ x) := rfl
/--
@isnad1 id=eq.0h2v.s6.b01476f29cf3 from=seed src=0 shape=56f14ef8 vocab=56f1a298
-/
@[simp] lemma succ_toMul [Preorder X] [SuccOrder X] (x : Additive X) :
    succ x.toMul = (succ x).toMul := rfl

/--
@isnad1 id=eq.0h2v.s6.0244c96d8e94 from=seed src=0 shape=dcd63932 vocab=4231a718
-/
@[simp] lemma succ_ofAdd [Preorder X] [SuccOrder X] (x : X) : succ (ofAdd x) = ofAdd (succ x) := rfl
/--
@isnad1 id=eq.0h2v.s6.5ad48d6a7484 from=seed src=0 shape=56f14ef8 vocab=b82badc0
-/
@[simp] lemma succ_toAdd [Preorder X] [SuccOrder X] (x : Multiplicative X) :
    succ x.toAdd = (succ x).toAdd :=
  rfl

/--
@isnad1 id=eq.0h2v.s6.f8d998fb2006 from=seed src=0 shape=dcd63932 vocab=cc0bad64
-/
@[simp] lemma pred_ofMul [Preorder X] [PredOrder X] (x : X) : pred (ofMul x) = ofMul (pred x) := rfl
/--
@isnad1 id=eq.0h2v.s6.889ef732977a from=seed src=0 shape=56f14ef8 vocab=762fbf00
-/
@[simp]
lemma pred_toMul [Preorder X] [PredOrder X] (x : Additive X) : pred x.toMul = (pred x).toMul := rfl

/--
@isnad1 id=eq.0h2v.s6.62c1f8c38648 from=seed src=0 shape=dcd63932 vocab=0b5bf881
-/
@[simp] lemma pred_ofAdd [Preorder X] [PredOrder X] (x : X) : pred (ofAdd x) = ofAdd (pred x) := rfl
/--
@isnad1 id=eq.0h2v.s6.6773630f99f9 from=seed src=0 shape=56f14ef8 vocab=8e8ae1ad
-/
@[simp] lemma pred_toAdd [Preorder X] [PredOrder X] (x : Multiplicative X) :
    pred x.toAdd = (pred x).toAdd :=
  rfl

end Order
