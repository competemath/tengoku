/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Equivalence proofs for AzVector cross product.

  Links `AzVector.cross` to Mathlib's `crossProduct` bilinear map.
-/
import Tengoku.Azurite.Azurite.AzVector.Cross
import Tengoku.Azurite.Azurite.AzVector.Operations
import Tengoku.Seed.LinearAlgebra.CrossProduct

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} [CommRing R]

/-- Cross product commutes with `toFn`, yielding Mathlib's `crossProduct`.
@isnad1 id=eq.0h3v.s10.9c05eab3f4d1 from=translated src=- shape=02b754ca vocab=8573bc1e
-/
theorem AzVector.toFn_cross (v w : AzVector R 3) :
    (v.cross w).toFn = (crossProduct v.toFn) w.toFn := by
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ => simp [cross, crossProduct, AzVector.toFn, Vector.get, Matrix.cons_val_zero]
  | 1, _ => simp [cross, crossProduct, AzVector.toFn, Vector.get, Matrix.cons_val_zero,
                   Matrix.cons_val_one]
  | 2, _ => simp [cross, crossProduct, AzVector.toFn, Vector.get]

/-- Cross product commutes with `ofFn`.
@isnad1 id=eq.0h3v.s10.24c67a268538 from=translated src=- shape=e24682dc vocab=3b60636d
-/
theorem AzVector.ofFn_cross (f g : Fin 3 → R) :
    (AzVector.ofFn f).cross (AzVector.ofFn g) = AzVector.ofFn ((crossProduct f) g) := by
  apply AzVector.toFn_injective
  rw [toFn_cross]
  funext ⟨i, hi⟩
  match i, hi with
  | 0, _ =>
    simp [crossProduct, AzVector.toFn, AzVector.ofFn, Vector.get, Matrix.cons_val_zero]
    rfl
  | 1, _ =>
    simp [crossProduct, AzVector.toFn, AzVector.ofFn, Vector.get, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    rfl
  | 2, _ =>
    simp [crossProduct, AzVector.toFn, AzVector.ofFn, Vector.get]
    rfl

end Azurite
