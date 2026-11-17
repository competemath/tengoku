/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.GW.Descendants.Equations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Algebraic output package for a future virtual GW realization

This is the boundary between the axiomatic theory and future geometry. A
geometric construction must supply a primary Gromov--Witten theory, stabilized
stable-map descendants, and a descendant--ancestor residual decomposition.
The package is only a carrier for those algebraic outputs: it neither
constructs actual moduli stacks or virtual fundamental classes nor certifies
that its residual is supported on stabilization boundary strata.
-/

@[expose] public section

namespace AxiomaticGW

universe u

/-- Algebraic output carrier for a future virtual stable-map construction.
Every field is consumed by the axiomatic GW endpoint, but inhabiting this
structure is not itself evidence of a geometric realization.-/
structure VirtualGWPackage
    {R V B : Type u} [CommRing R] [Algebra ℚ R]
    [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
    [AddCancelCommMonoid B] (D : EffectiveCurveMonoid B)
    (C : StableCurveCohomology R) (P : PsiClasses C) where
  /-- Stored stabilized primary classes and their gluing laws.-/
  primary : GromovWittenTheory R V B D C
  /-- Stable-map cotangent insertions pushed to stable curves.-/
  descendants : StableMapDescendants primary
  /-- Residual decomposition against stable-curve ancestors.-/
  comparison : DescendantAncestorComparison P descendants

namespace VirtualGWPackage

variable {R V B : Type u} [CommRing R] [Algebra ℚ R]
  [AddCommGroup V] [Module R V] [Module.Free R V] [Module.Finite R V]
  [AddCancelCommMonoid B] {D : EffectiveCurveMonoid B}
  {C : StableCurveCohomology R} {P : PsiClasses C}

/-- Project the primary axiomatic GW theory stored in the package.-/
def toGromovWittenTheory
    (G : VirtualGWPackage (R := R) (V := V) (B := B) D C P) :
    GromovWittenTheory R V B D C :=
  G.primary

/-- Project the stable-map descendant extension stored in the package.-/
def toStableMapDescendants
    (G : VirtualGWPackage (R := R) (V := V) (B := B) D C P) :
    StableMapDescendants G.toGromovWittenTheory :=
  G.descendants

/-- Project the recorded descendant--ancestor residual decomposition.-/
def toDescendantAncestorComparison
    (G : VirtualGWPackage (R := R) (V := V) (B := B) D C P) :
    DescendantAncestorComparison P G.toStableMapDescendants :=
  G.comparison

end VirtualGWPackage

end AxiomaticGW
