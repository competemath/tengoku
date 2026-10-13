/-
Copyright (c) 2025 Salvatore Mercuri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Salvatore Mercuri, Kevin Buzzard
-/
module

public import Tengoku

/-!
# Finite Dimension

Material destined for Mathlib.
-/

@[expose] public section

/--
@isnad1 id=continuo.0h4v.s7.fd15e346640c from=translated src=- shape=0ecf70c5 vocab=7ce962de
-/
theorem Basis.toMatrix_continuous {ι R M : Type*} [AddCommGroup M]
    [Finite ι] [TopologicalSpace M] [NontriviallyNormedField R] [Module R M]
    [IsTopologicalAddGroup M] [ContinuousSMul R M] [CompleteSpace R] [T2Space M]
    [FiniteDimensional R M] (B : Module.Basis ι R M) :
    Continuous fun (v : ι → M) => B.toMatrix v :=
  let := Fintype.ofFinite ι
  LinearMap.continuous_of_finiteDimensional B.toMatrixEquiv.toLinearMap
