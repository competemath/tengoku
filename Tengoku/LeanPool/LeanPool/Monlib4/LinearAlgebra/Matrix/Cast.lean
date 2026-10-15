/-
Copyright (c) 2026 Monica Omar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Monica Omar
-/
module

public import Tengoku

/-!
# LeanPool.Monlib4.LinearAlgebra.Matrix.Cast

Imported Lean Pool material for `LeanPool.Monlib4.LinearAlgebra.Matrix.Cast`.
-/

@[expose] public section

variable {R k : Type*} {s : k → Type _}

/--
@isnad1 id=eq.1h8v.s5.2a9442a42c6d from=translated src=- shape=90835d7b vocab=6933bc76
-/
theorem Matrix.cast_apply {i j : k} (x : Matrix (s i) (s i) R) (h : i = j) (p q : s j) :
  (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp x p q =
    x (by rw [h]; exact p) (by rw [h]; exact q) :=
by aesop
/--
@isnad1 id=eq.1h8v.s5.bd5b6fa09aa4 from=translated src=- shape=a434037b vocab=8e71cdac
-/
theorem Matrix.cast_apply' {i j : k} (x : Matrix (s j) (s j) R) (h : j = i) (p q : s i) :
  (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mpr x p q =
    x (by rw [h]; exact p) (by rw [h]; exact q) :=
by aesop

/--
@isnad1 id=eq.1h7v.s6.13e1035eb2f4 from=translated src=- shape=32fe46fb vocab=f3e6eb22
-/
theorem Matrix.cast_hMul [Semiring R] [Π i, Fintype (s i)]
  {i j : k} (x y : Matrix (s i) (s i) R) (h : i = j) :
  (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp (x * y) =
    (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp x *
      (by rw [h] : Matrix (s i) (s i) R = Matrix (s j) (s j) R).mp y :=
by aesop
