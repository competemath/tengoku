/-
Copyright (c) 2026 JMA. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JMA
-/
module

public import Tengoku.Axiomaticgw.AxiomaticGW.Frobenius.Constructions
public import Tengoku.Seed.LinearAlgebra.Multilinear.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-labelled multiplication

Mathlib's `MultilinearMap.mkPiAlgebra` is the finite-labelled multilinear
product used by TFT correlators. This file records the relabelling property
needed by the correlator construction.
-/

@[expose] public section

namespace AxiomaticGW

namespace TFT

variable {R A S : Type*} [CommRing R] [CommRing A] [Algebra R A] [Fintype S]

/-- Finite-labelled multiplication is invariant under relabelling.-/
theorem mkPiAlgebra_domDomCongr {T : Type*} [Fintype T] (e : S ≃ T) :
    (MultilinearMap.mkPiAlgebra R S A).domDomCongr e =
      MultilinearMap.mkPiAlgebra R T A := by
  ext a
  simpa only [MultilinearMap.domDomCongr_apply,
    MultilinearMap.mkPiAlgebra_apply] using e.prod_comp a

end TFT

end AxiomaticGW
