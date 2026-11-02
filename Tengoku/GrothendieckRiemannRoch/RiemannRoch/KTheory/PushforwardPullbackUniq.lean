/-
Copyright (c) 2026 Guanghao Li. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Guanghao Li
-/

import Tengoku.Seed.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# A `pushforward`-shaped equivalence functor is isomorphic to a `pullback`-shaped functor

`SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂ : SheafOfModules R ≌
SheafOfModules S` has `.functor := pushforward φ` and `.inverse := pushforward ψ`. Both
`pushforward φ` and `pullback ψ` (the general sheaf-of-modules pullback functor, left adjoint to
`pushforward ψ` when it exists) are left adjoints to the *same* functor `pushforward ψ` —
`pushforward φ` via `SheafOfModules.pushforwardPushforwardAdj eqv.toAdjunction φ ψ H₁ H₂`,
`pullback ψ` via `SheafOfModules.pullbackPushforwardAdjunction ψ` — so
`CategoryTheory.Adjunction.leftAdjointUniq` identifies them directly, without needing any new
sheafification-compatibility argument.

This is aimed at discharging `overEquivMonoidal` (see `docs/PR_LEDGER.md`): once
`Scheme.Modules.overEquiv U .functor` is identified with a `pullback`-shaped functor via this file,
`overEquivMonoidal` should be reachable through this project's already-verified
`pullbackTensorSheafHom` / `pullbackTensorSheafHom_isIso_of_iso_free` machinery
(`KTheory/GlobalPullbackTensor.lean`, `KTheory/GlobalPullbackTensorFree.lean`) transported across
the resulting isomorphism, rather than through a bespoke pushforward-sheafification fact.
-/

noncomputable section

open CategoryTheory

universe v v₁ v₂ u₁ u₂ u

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}

/-- `SheafOfModules.pushforward ψ` has a left adjoint, since it is the inverse-equivalence side of
`SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂`. Stated as a `theorem`, not an
`instance`, since `φ`, `H₁`, `H₂` are data/propositions that cannot be found by typeclass search —
supply it explicitly (e.g. via named-argument syntax `(hAdj := ⋯)`) at call sites.-/
theorem SheafOfModules.pushforward_isRightAdjoint_of_equivalence (eqv : C ≌ D)
    [Functor.IsContinuous eqv.functor J K] [Functor.IsContinuous eqv.inverse K J]
    (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{u} K J).obj S)
    (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
      ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
    (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj) :
    (SheafOfModules.pushforward.{v} ψ).IsRightAdjoint :=
  (SheafOfModules.pushforwardPushforwardEquivalence eqv φ ψ H₁ H₂).isRightAdjoint_inverse

/-- **A `pushforwardPushforwardEquivalence`'s `.functor` is isomorphic to a `pullback`-shaped
functor.** See the module docstring.-/
def SheafOfModules.pushforwardIsoPullback (eqv : C ≌ D)
    [Functor.IsContinuous eqv.functor J K] [Functor.IsContinuous eqv.inverse K J]
    (φ : S ⟶ (eqv.functor.sheafPushforwardContinuous RingCat.{u} J K).obj R)
    (ψ : R ⟶ (eqv.inverse.sheafPushforwardContinuous RingCat.{u} K J).obj S)
    (H₁ : Functor.whiskerRight (NatTrans.op eqv.counit) R.obj =
      ψ.hom ≫ eqv.inverse.op.whiskerLeft φ.hom)
    (H₂ : φ.hom ≫ eqv.functor.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op eqv.unit) S.obj = 𝟙 S.obj)
    [hAdj : (SheafOfModules.pushforward.{v} ψ).IsRightAdjoint] :
    SheafOfModules.pushforward.{v} φ ≅ SheafOfModules.pullback.{v} ψ :=
  Adjunction.leftAdjointUniq
    (SheafOfModules.pushforwardPushforwardAdj eqv.toAdjunction φ ψ H₁ H₂)
    (@SheafOfModules.pullbackPushforwardAdjunction _ _ _ _ _ _ _ _ _ _ ψ hAdj)

end
