/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzMatrix identity and single-entry matrices.

  Links `AzMatrix.identity` to Mathlib's `1 : Matrix` and
  `AzMatrix.single` to `Matrix.stdBasisMatrix`.
-/
import Tengoku.Azurite.Azurite.AzMatrix.Operations
import Tengoku.Seed.Data.Matrix.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.Azurite end Tengoku.Azurite open Tengoku.Azurite
namespace Azurite
variable {R : Type _} [Zero R] [One R] {m n : Nat}

/-- The identity matrix equals Mathlib's `1 : Matrix (Fin n) (Fin n) R`.
@isnad1 id=eq.0h2v.s5.1136ae88eaeb from=translated src=- shape=fd02b3b0 vocab=fa0a155c
-/
theorem AzMatrix.toFn_identity :
    (AzMatrix.identity (R := R) (n := n)).toFn = fun i j => if i = j then 1 else 0 := by
  ext i j; simp [identity, toFn, ofFn, Vector.get]
  exact if_congr (Fin.val_inj (a := i) (b := j)) rfl rfl

/-- The single-entry matrix equals Mathlib's `Matrix.stdBasisMatrix`.
@isnad1 id=eq.0h5v.s6.40d1a3d53120 from=translated src=- shape=8929c167 vocab=5017ec4c
-/
theorem AzMatrix.toFn_single (i₀ : Fin m) (j₀ : Fin n) :
    (AzMatrix.single (R := R) i₀ j₀).toFn = fun i j => if i = i₀ ∧ j = j₀ then 1 else 0 := by
  ext i j; simp [single, toFn, ofFn, Vector.get]
  rfl

/-- `ofFn` of the identity function yields `AzMatrix.identity`.
@isnad1 id=eq.0h2v.s5.a3209bd0886d from=translated src=- shape=1a0f298b vocab=b867723d
-/
theorem AzMatrix.ofFn_identity :
    AzMatrix.ofFn (fun (i j : Fin n) => if i = j then (1 : R) else 0) = AzMatrix.identity := rfl

/-- `ofFn` of a single-entry function yields `AzMatrix.single`.
@isnad1 id=eq.0h5v.s6.6e6afcef91fc from=translated src=- shape=fc88b317 vocab=391d0a0d
-/
theorem AzMatrix.ofFn_single (i₀ : Fin m) (j₀ : Fin n) :
    AzMatrix.ofFn (fun i j => if i = i₀ ∧ j = j₀ then (1 : R) else 0) =
      AzMatrix.single i₀ j₀ := rfl

end Azurite
-- Tengoku: root names of this library moved to Tengoku.Azurite so they do not collide with other libraries (generated)
