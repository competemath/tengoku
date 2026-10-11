/-
Copyright (c) 2026 ClassificationOfSurfaces contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ryan McCorvie, Jack McCarthy
-/
module

public import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicMoves
import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicP1Realization
import Tengoku.LeanPool.LeanPool.ClassificationOfSurfaces.FiniteCyclicP2Realization
public import Tengoku

/-!
# Realization invariance for finite cyclic move closures

This file closes the geometric proof obligations parameterizing `FiniteCyclicMoves`. Signed
presentation isomorphisms, P1 subdivisions, and genuine P2 face subdivisions all preserve the
faithful polygonal quotient. Consequently, clients of directed chains and common-subdivision
certificates do not need to pass the primitive invariance proofs explicitly.
-/

@[expose] public section

namespace LeanEval.Topology.ClassificationOfSurfaces

namespace FiniteCyclicPresentation

end FiniteCyclicPresentation

end LeanEval.Topology.ClassificationOfSurfaces
