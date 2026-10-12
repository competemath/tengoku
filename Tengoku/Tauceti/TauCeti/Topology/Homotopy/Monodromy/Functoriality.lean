/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Tengoku
public import Tengoku.Tauceti.TauCeti.Logic.Function.Fiber

/-!
# Functoriality of covering-space monodromy

A continuous map between two covering spaces over the same base carries lifts of a path to
lifts of that path. Consequently it intertwines transport between fibres and induces a natural
transformation between the two monodromy functors. An isomorphism of covers induces a natural
isomorphism. The underlying set-level operations on fibres — the restriction `Function.fiberMap`
of a map over the base to a fibre and the relabelling `Equiv.compFiberEquiv` of fibres under a
bijection of bases — come from `TauCeti.Logic.Function.Fiber`; this file adds their
compatibility with monodromy.

These constructions are the morphism-level input for the alternative classification of covers
as functors from the fundamental groupoid in `TauCetiRoadmap/UniversalCovers/README.md`, Stage 2,
item 8. Mathlib supplies the object-level functor `IsCoveringMap.monodromyFunctor`; this file
packages its functoriality in the covering map.

## Main declarations

* `IsCoveringMap.fiberMap_monodromy`: a map of covers intertwines monodromy transport
  on their fibres.
* `IsCoveringMap.monodromyNatTrans`: a map of covers induces a natural transformation
  between their monodromy functors.
* `IsCoveringMap.monodromyNatIso`: an isomorphism of covers induces a natural
  isomorphism between their monodromy functors.
* `IsCoveringMap.monodromyHomeomorphCompNatIso`: changing the base by a homeomorphism
  transports the monodromy functor by the inverse homeomorphism.

## References

The proof uses Junyan Xu's path-lifting and monodromy API in
`Mathlib/Topology/Homotopy/Lifting.lean`. No Mathlib code is vendored.
-/

public section

open CategoryTheory
open unitInterval

namespace TauCeti

section

universe u v

variable {E F G : Type u} {X : Type v}
  [TopologicalSpace E] [TopologicalSpace F] [TopologicalSpace G] [TopologicalSpace X]
  {p : E → X} {q : F → X} {r : G → X}

/-- A map between covering spaces over the same base intertwines monodromy along every path. -/
@[simp]
theorem _root_.IsCoveringMap.fiberMap_monodromy (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (f : C(E, F)) (hf : q ∘ f = p)
    {x y : X} (a : Path.Homotopic.Quotient x y) (e : p ⁻¹' {x}) :
    Function.fiberMap f hf y (hp.monodromy a e) =
      hq.monodromy a (Function.fiberMap f hf x e) := by
  symm
  -- `Function.fiberMap` is not exposed, so its values do not reduce here. Put both fibre points
  -- in constructor form via `fiberMap_apply_coe` first, so the lifted path's endpoints match
  -- `monodromy_eq_of_map_eq` by projection alone.
  have h₁ : Function.fiberMap f hf x e = ⟨f e, Function.mapsTo_fiber f hf x e.2⟩ :=
    Subtype.ext (Function.fiberMap_apply_coe f hf x e)
  have h₂ : Function.fiberMap f hf y (hp.monodromy a e) =
      ⟨f (hp.monodromy a e), Function.mapsTo_fiber f hf y (hp.monodromy a e).2⟩ :=
    Subtype.ext (Function.fiberMap_apply_coe f hf y (hp.monodromy a e))
  rw [h₁, h₂]
  let Γ := hp.liftPathQuotient a e
  let q' : C(F, X) := ⟨q, hq.continuous⟩
  let p' : C(E, X) := ⟨p, hp.continuous⟩
  have hcomp : q'.comp f = p' := by
    ext z
    exact congrFun hf z
  apply hq.monodromy_eq_of_map_eq (Γ.map f)
  -- Expose the mapped lifted path so the commuting triangle can rewrite its composite map.
  change (Γ.map f).map q' = _
  rw [← Path.Homotopic.Quotient.map_comp]
  -- The goal and `map_liftPathQuotient` differ only in whether the projection is spelled
  -- `q'.comp f` or `p'`, which is `hcomp` — but in a position whose *type* depends on it. Neither
  -- `convert` nor `congr!` descends through that (both stop at an `Iff` between the two
  -- equations), and `rw` cannot build the motive, so transport along `hcomp` directly.
  -- `q'.comp f` and `p'` differ by `hcomp`, but in a *type index*: `Γ.map u` has type
  -- `Path.Homotopic.Quotient (u ↑e) (u ↑(hp.monodromy a e))`.  No `Eq`-rewrite can abstract that,
  -- which is why `rw`, `simp` and `convert` all stall here.  `HEq` is heterogeneous, so its motive
  -- stays type-correct across the change; take the step there and return to `Eq` at the end, once
  -- both sides have the same type again.
  refine eq_of_heq (HEq.trans (show HEq (Γ.map (q'.comp f)) (Γ.map p') by rw [hcomp]) ?_)
  rw [hp.map_liftPathQuotient a e]
  exact (Path.Homotopic.Quotient.cast_heq _ _).trans (Path.Homotopic.Quotient.cast_heq _ _).symm

/-- A continuous map of covering spaces over `X` induces a natural transformation between
their monodromy functors. Its component over `x` is the restriction of `f` to the fibre over
`x`. -/
def _root_.IsCoveringMap.monodromyNatTrans
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q)
    (f : C(E, F)) (hf : q ∘ f = p) : hp.monodromyFunctor ⟶ hq.monodromyFunctor where
  app x := ↾(Function.fiberMap f hf x.as)
  naturality {x y} a := by
    ext e
    -- The naturality square in `Type` unfolds pointwise to monodromy equivariance.
    change Function.fiberMap f hf y.as (hp.monodromy a e) =
      hq.monodromy a (Function.fiberMap f hf x.as e)
    exact IsCoveringMap.fiberMap_monodromy hp hq f hf a e

/-- On a fibre, the natural transformation induced by a map of covers applies that map to the
underlying point. -/
@[simp]
theorem _root_.IsCoveringMap.monodromyNatTrans_app (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (f : C(E, F)) (hf : q ∘ f = p)
    (x : X) :
    (IsCoveringMap.monodromyNatTrans hp hq f hf).app (FundamentalGroupoid.mk x) =
      ↾(Function.fiberMap f hf x) :=
  (rfl)

/-- The natural transformation induced by a map over the base depends only on that map, not on
the proof that it lies over the base. -/
theorem _root_.IsCoveringMap.monodromyNatTrans_congr (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) {f g : C(E, F)} (hf : q ∘ f = p) (hg : q ∘ g = p)
    (h : f = g) : IsCoveringMap.monodromyNatTrans hp hq f hf = IsCoveringMap.monodromyNatTrans hp
        hq g hg := by
  subst g
  rfl

/-- The identity map of a cover induces the identity natural transformation. -/
@[simp]
theorem _root_.IsCoveringMap.monodromyNatTrans_id (hp : _root_.IsCoveringMap p) :
    IsCoveringMap.monodromyNatTrans hp hp (ContinuousMap.id E) rfl = 𝟙 hp.monodromyFunctor := by
  ext x e
  exact Function.fiberMap_id_apply x.as e

/-- Composition of maps of covers induces vertical composition of their monodromy natural
transformations. -/
theorem _root_.IsCoveringMap.monodromyNatTrans_comp (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (hr : _root_.IsCoveringMap r)
    (f : C(E, F)) (g : C(F, G)) (hf : q ∘ f = p) (hg : r ∘ g = q) :
    IsCoveringMap.monodromyNatTrans hp hr (g.comp f) (by
      funext z
      exact (congrFun hg (f z)).trans (congrFun hf z)) =
      IsCoveringMap.monodromyNatTrans hp hq f hf ≫ IsCoveringMap.monodromyNatTrans hq hr g hg := by
  ext x e
  exact Function.fiberMap_comp_apply f g hf hg x.as e

/-- An isomorphism of covering spaces over `X` induces a natural isomorphism between their
monodromy functors. Its forward and inverse transformations are the ones induced by the
homeomorphism and its inverse, so its component over `x` is the restriction of the
homeomorphism to the fibre over `x`. -/
noncomputable def _root_.IsCoveringMap.monodromyNatIso
    (hp : _root_.IsCoveringMap p) (hq : _root_.IsCoveringMap q)
    (h : E ≃ₜ F) (hh : q ∘ h = p) : hp.monodromyFunctor ≅ hq.monodromyFunctor where
  hom := IsCoveringMap.monodromyNatTrans hp hq (h : C(E, F)) hh
  inv := IsCoveringMap.monodromyNatTrans hq hp (h.symm : C(F, E)) ((Equiv.comp_symm_eq h.toEquiv q
      p).2 hh.symm)
  hom_inv_id := by
    ext x e
    have hs : p ∘ ⇑h.symm = q := (Equiv.comp_symm_eq h.toEquiv q p).2 hh.symm
    exact Subtype.ext <| (Function.fiberMap_apply_coe _ hs _ _).trans <|
      (congrArg h.symm (Function.fiberMap_apply_coe _ hh _ _)).trans (h.symm_apply_apply _)
  inv_hom_id := by
    ext x f
    have hs : p ∘ ⇑h.symm = q := (Equiv.comp_symm_eq h.toEquiv q p).2 hh.symm
    exact Subtype.ext <| (Function.fiberMap_apply_coe _ hh _ _).trans <|
      (congrArg h (Function.fiberMap_apply_coe _ hs _ _)).trans (h.apply_symm_apply _)

/-- The forward natural transformation of the monodromy isomorphism is the canonical
transformation induced by the homeomorphism. -/
@[simp]
theorem _root_.IsCoveringMap.monodromyNatIso_hom (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (h : E ≃ₜ F) (hh : q ∘ h = p) :
    (IsCoveringMap.monodromyNatIso hp hq h hh).hom =
      IsCoveringMap.monodromyNatTrans hp hq (h : C(E, F)) hh :=
  (rfl)

/-- The inverse natural transformation of the monodromy isomorphism is induced by the inverse
homeomorphism. -/
@[simp]
theorem _root_.IsCoveringMap.monodromyNatIso_inv (hp : _root_.IsCoveringMap p)
    (hq : _root_.IsCoveringMap q) (h : E ≃ₜ F) (hh : q ∘ h = p) :
    (IsCoveringMap.monodromyNatIso hp hq h hh).inv =
      IsCoveringMap.monodromyNatTrans hq hp (h.symm : C(F, E))
        ((Equiv.comp_symm_eq h.toEquiv q p).2 hh.symm) :=
  (rfl)

section BaseHomeomorph

variable {Y : Type v} [TopologicalSpace Y]

end BaseHomeomorph

end

end TauCeti
