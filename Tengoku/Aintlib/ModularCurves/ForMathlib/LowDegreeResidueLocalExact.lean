/-
Copyright (c) 2026 Chris Birkbeck. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Birkbeck
-/
import Tengoku.Aintlib.ModularCurves.ForMathlib.LowDegreeFiniteProjectiveReplacement

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Local exactness from a residue fibre

This file transports exactness of a short complex over a residue field to
surjectivity of the finite-projective low-degree replacement.
-/

open Function
open CategoryTheory
open TensorProduct
open scoped ChangeOfRings

universe u

namespace ModularCurves
namespace LowDegreeFiniteReplacement

variable {R : Type u} [CommRing R] [IsNoetherianRing R]

local instance residueLocalHZeroFinite
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R (LinearMap.ker S.f.hom)] :
    Module.Finite R (HZero S.moduleCatToCycles) :=
  Module.Finite.ker_moduleCatToCycles S

local instance residueLocalHOneFinite
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.homology] :
    Module.Finite R (HOne S.moduleCatToCycles) :=
  Module.Finite.quotient_range_moduleCatToCycles S

end LowDegreeFiniteReplacement
end ModularCurves
