/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Arithmetic operations for AzVector: Zero, Add, Neg, Sub, SMul.
  Provides `toFn_*` simp lemmas for each operation.
-/
import Tengoku.Azurite.Azurite.AzVector.Basic
import Tengoku.Seed.Algebra.Group.Pi.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Azurite
variable {R : Type _} {n : Nat}

/-! ### Zero -/

instance instAzVectorZero [Zero R] : Zero (AzVector R n) := ⟨⟨Vector.ofFn (fun _ => 0)⟩⟩

/--
@isnad1 id=eq.0h2v.s5.62018778a29c from=translated src=- shape=f1a087da vocab=6fda637b
-/
@[simp]
theorem AzVector.toFn_zero [Zero R] :
    (0 : AzVector R n).toFn = 0 := by
  ext i
  show (Vector.ofFn (fun _ => (0 : R))).get i = (0 : Fin n → R) i
  simp [Vector.get]

/--
@isnad1 id=eq.0h3v.s5.0abd8fdaca2e from=translated src=- shape=b83b7528 vocab=bfe8a638
-/
@[simp]
theorem AzVector.get_zero [Zero R] (i : Fin n) :
    (0 : AzVector R n).data.get i = 0 := by
  show (Vector.ofFn (fun _ => (0 : R))).get i = 0
  simp [Vector.get]

/-! ### Addition -/

instance instAzVectorAdd [Add R] : Add (AzVector R n) :=
  ⟨fun v w => v.zip (· + ·) w⟩

/--
@isnad1 id=eq.0h4v.s6.1830e829fb6d from=translated src=- shape=b054ac72 vocab=c603523c
-/
@[simp]
theorem AzVector.toFn_add [Add R] (v w : AzVector R n) :
    (v + w).toFn = v.toFn + w.toFn := by
  ext i
  show (v.zip (· + ·) w).toFn i = v.toFn i + w.toFn i
  simp

/-! ### Negation -/

instance instAzVectorNeg [Neg R] : Neg (AzVector R n) :=
  ⟨fun v => v.map (- ·)⟩

/--
@isnad1 id=eq.0h3v.s5.fae9488cd1e2 from=translated src=- shape=f73111cd vocab=7ed8808a
-/
@[simp]
theorem AzVector.toFn_neg [Neg R] (v : AzVector R n) :
    (-v).toFn = -v.toFn := by
  ext i
  show (v.map (- ·)).toFn i = -(v.toFn i)
  simp

/-! ### Subtraction -/

instance instAzVectorSub [Sub R] : Sub (AzVector R n) :=
  ⟨fun v w => v.zip (· - ·) w⟩

/--
@isnad1 id=eq.0h4v.s6.76c8af6cf33b from=translated src=- shape=b054ac72 vocab=5693f962
-/
@[simp]
theorem AzVector.toFn_sub [Sub R] (v w : AzVector R n) :
    (v - w).toFn = v.toFn - w.toFn := by
  ext i
  show (v.zip (· - ·) w).toFn i = v.toFn i - w.toFn i
  simp

/-! ### Scalar multiplication -/

instance instAzVectorSMul [SMul α R] : SMul α (AzVector R n) :=
  ⟨fun c v => v.map (c • ·)⟩

/--
@isnad1 id=eq.0h5v.s6.5fbb9e7b8e05 from=translated src=- shape=9b03f1ec vocab=cf4d4d7c
-/
@[simp]
theorem AzVector.toFn_smul [SMul α R] (c : α) (v : AzVector R n) :
    (c • v).toFn = c • v.toFn := by
  ext i
  show (v.map (c • ·)).toFn i = c • v.toFn i
  simp

end Azurite
