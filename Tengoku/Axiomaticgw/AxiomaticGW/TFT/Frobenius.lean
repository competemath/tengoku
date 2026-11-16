/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.TFT.Basic
public import Tengoku.Axiomaticgw.AxiomaticGW.TFT.Sewing

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The two-dimensional TFT associated to a Frobenius algebra

This file bundles the correlators of a finite-free commutative Frobenius
algebra and the gluing theorems already proved for them.
-/

@[expose] public section

namespace AxiomaticGW

namespace CommFrobeniusAlgebra

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  [Module.Free R A] [Module.Finite R A]

/-- The two-dimensional TFT canonically associated to a finite-free
commutative Frobenius algebra.-/
noncomputable def toTwoDimensionalTFT
    (F : CommFrobeniusAlgebra R A) :
    TwoDimensionalTFT R A where
  pairing := F.pairing
  unit := 1
  correlator := F.correlator
  relabel := F.correlator_domDomCongr
  unit_insert := F.correlator_option_one_apply
  nonseparating := F.selfContract_correlator
  separating := F.pairContract_correlator
  normalization := F.correlator_zero_fin_two_apply

end CommFrobeniusAlgebra

end AxiomaticGW
