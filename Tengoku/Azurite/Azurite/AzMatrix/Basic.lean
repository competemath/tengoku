/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/
namespace Tengoku.Azurite end Tengoku.Azurite open Tengoku.Azurite
/-
  AzMatrix: Computable fixed-size matrix type.

  Wraps `Vector (Vector R n) m` for efficient computation.
  Provides bidirectional conversion with Mathlib's `Matrix (Fin m) (Fin n) R`.
-/
namespace Azurite

/-- A computable `m × n` matrix over `R`.-/
structure AzMatrix (R : Type _) (m n : Nat) where
  data : Vector (Vector R n) m
deriving DecidableEq

variable {R : Type _} {m n : Nat}

/-- Convert to a Mathlib-compatible function `Fin m → Fin n → R`.-/
def AzMatrix.toFn (M : AzMatrix R m n) : Fin m → Fin n → R :=
  fun i j => (M.data.get i).get j

/-- Construct from a function `Fin m → Fin n → R`.-/
def AzMatrix.ofFn (f : Fin m → Fin n → R) : AzMatrix R m n :=
  ⟨Vector.ofFn (fun i => Vector.ofFn (f i))⟩

/-- Access the `(i, j)` entry.-/
def AzMatrix.get (M : AzMatrix R m n) (i : Fin m) (j : Fin n) : R :=
  (M.data.get i).get j

/-- Two matrices are equal iff all entries are equal.
@isnad1 id=eq.1h5v.s5.6c1d3be25f7b from=translated src=- shape=402ee7b0 vocab=9566ef65
-/
@[ext]
theorem AzMatrix.ext {M N : AzMatrix R m n}
    (h : ∀ i j, M.get i j = N.get i j) : M = N := by
  cases M; cases N; simp only [AzMatrix.mk.injEq]
  apply Vector.ext; intro i hi
  apply Vector.ext; intro j hj
  exact h ⟨i, hi⟩ ⟨j, hj⟩

/--
@isnad1 id=eq.0h6v.s5.31883129534f from=translated src=- shape=5798ecf0 vocab=bc390f2d
-/
@[simp]
theorem AzMatrix.toFn_ofFn (f : Fin m → Fin n → R) (i : Fin m) (j : Fin n) :
    (AzMatrix.ofFn f).toFn i j = f i j := by
  simp [toFn, ofFn, Vector.get]
  rfl

/--
@isnad1 id=eq.0h4v.s4.fb5d244c9375 from=translated src=- shape=f39cf9a7 vocab=9582bd61
-/
@[simp]
theorem AzMatrix.ofFn_toFn (M : AzMatrix R m n) : AzMatrix.ofFn M.toFn = M := by
  ext i j; simp [toFn, ofFn, get, Vector.get]
  rfl

/--
@isnad1 id=injectiv.0h3v.s4.2cedf2a1ee45 from=translated src=- shape=738e149d vocab=6d4e32fc
-/
theorem AzMatrix.toFn_injective :
    Function.Injective (AzMatrix.toFn (R := R) (m := m) (n := n)) := by
  intro a b h; ext i j; exact congr (congrFun h i) rfl

/-! ### Map -/

/-- Apply `f` to every entry of a matrix.-/
def AzMatrix.map {S : Type _} (f : R → S) (M : AzMatrix R m n) : AzMatrix S m n :=
  ⟨M.data.map (fun row => row.map f)⟩

/--
@isnad1 id=eq.0h8v.s5.943036ad6b5c from=translated src=- shape=16d249ba vocab=0710e6da
-/
@[simp]
theorem AzMatrix.toFn_map {S : Type _} (f : R → S) (M : AzMatrix R m n)
    (i : Fin m) (j : Fin n) :
    (M.map f).toFn i j = f (M.toFn i j) := by
  simp [map, AzMatrix.toFn, Vector.get, Vector.map]
  rfl

/-! ### Zip -/

/-- Combine two matrices entrywise with `f`.-/
def AzMatrix.zip {S T : Type _} (f : R → S → T)
    (M : AzMatrix R m n) (N : AzMatrix S m n) : AzMatrix T m n :=
  ⟨Vector.zipWith (fun r s => Vector.zipWith f r s) M.data N.data⟩

/--
@isnad1 id=eq.0h10v.s6.bd8ec5779825 from=translated src=- shape=99a6c8fe vocab=a775e78c
-/
@[simp]
theorem AzMatrix.toFn_zip {S T : Type _} (f : R → S → T)
    (M : AzMatrix R m n) (N : AzMatrix S m n) (i : Fin m) (j : Fin n) :
    (M.zip f N).toFn i j = f (M.toFn i j) (N.toFn i j) := by
  simp [zip, AzMatrix.toFn, Vector.get, Vector.zipWith]
  rfl

/-! ### ofLists -/

/-- Construct a matrix from a list of row lists.
    Usage: `AzMatrix.ofLists [[1, 2], [3, 4]]`-/
def AzMatrix.ofLists (rows : List (List R))
    (hm : rows.length = m := by decide)
    (hn : ∀ r ∈ rows, r.length = n := by decide) : AzMatrix R m n :=
  ⟨⟨(rows.attach.map (fun ⟨r, hr⟩ =>
    (⟨r.toArray, by simp [hn r hr]⟩ : Vector R n))).toArray,
    by simp [hm]⟩⟩

/-! ### toLists -/

/-- Convert a matrix to a list of row lists.
    Inverse of `ofLists`.-/
def AzMatrix.toLists (M : AzMatrix R m n) : List (List R) :=
  M.data.toList.map (·.toList)

/--
@isnad1 id=eq.0h4v.s4.52013d8ee192 from=translated src=- shape=da6f31aa vocab=52a8c755
-/
@[simp]
theorem AzMatrix.toLists_length (M : AzMatrix R m n) : M.toLists.length = m := by
  simp [toLists]

/--
@isnad1 id=eq.1h5v.s5.1f8fab8f877c from=translated src=- shape=85a7cdfb vocab=18dc6dcf
-/
theorem AzMatrix.mem_toLists_length {M : AzMatrix R m n} {row : List R}
    (h : row ∈ M.toLists) : row.length = n := by
  simp only [toLists, List.mem_map] at h
  obtain ⟨v, _, rfl⟩ := h
  simp

/--
@isnad1 id=eq.0h4v.s5.2e6952695817 from=translated src=- shape=7bd3d0d6 vocab=e511f35e
-/
theorem AzMatrix.ofLists_toLists (M : AzMatrix R m n) :
    AzMatrix.ofLists M.toLists M.toLists_length
      (fun _ h => AzMatrix.mem_toLists_length h) = M := by
  ext i j
  simp only [AzMatrix.ofLists, AzMatrix.toLists, AzMatrix.get, Vector.get,
    List.getElem_toArray, List.getElem_map, List.getElem_attach]
  rfl

end Azurite
-- Tengoku: root names of this library moved to Tengoku.Azurite so they do not collide with other libraries (generated)
