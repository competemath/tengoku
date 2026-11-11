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

/--
@isnad1 id=finite.0h2v.s13.c95941c65090 from=translated src=- shape=0b2dd5e4 vocab=9e9ba789
-/
local instance residueLocalHZeroFinite
    (S : ShortComplex (ModuleCat.{u} R))
    [Module.Finite R (LinearMap.ker S.f.hom)] :
    Module.Finite R (HZero S.moduleCatToCycles) :=
  Module.Finite.ker_moduleCatToCycles S

/--
@isnad1 id=finite.0h2v.s13.96a8d2aa5e90 from=translated src=- shape=0c311f01 vocab=1dc8257a
-/
local instance residueLocalHOneFinite
    (S : ShortComplex (ModuleCat.{u} R)) [Module.Finite R S.homology] :
    Module.Finite R (HOne S.moduleCatToCycles) :=
  Module.Finite.quotient_range_moduleCatToCycles S

end LowDegreeFiniteReplacement
end ModularCurves
