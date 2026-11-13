/-
Copyright © 2026 Mikhail Hogrefe

This file is part of Azurite.

Azurite is free software: you can redistribute it and/or modify it under the terms of the Apache
License, Version 2.0. See <https://www.apache.org/licenses/LICENSE-2.0>.
-/

/-
  Core definitions for AzVector: a computable fixed-length vector.

  `AzVector R n` wraps Lean's `Vector R n` (array-backed).
  Equivalence with Mathlib's `Fin n → R` via `toFn`/`ofFn`.
-/
namespace Tengoku.Azurite end Tengoku.Azurite open Tengoku.Azurite
namespace Azurite

/-- A computable fixed-length vector backed by `Vector`.-/
structure AzVector (R : Type _) (n : Nat) where
  /-- The underlying `Vector`.-/
  data : Vector R n

variable {R : Type _} {n : Nat}

/-- Convert to Mathlib's function representation `Fin n → R`.-/
def AzVector.toFn (v : AzVector R n) : Fin n → R := v.data.get

/-- Convert from Mathlib's function representation.-/
def AzVector.ofFn (f : Fin n → R) : AzVector R n := ⟨Vector.ofFn f⟩

/-- Index into a vector.-/
def AzVector.get (v : AzVector R n) (i : Fin n) : R := v.data.get i

/-- Extensionality: two `AzVector`s are equal iff they agree at every index.
@isnad1 id=eq.1h4v.s5.17737e584398 from=translated src=- shape=c70e8f1d vocab=dc68e60d
-/
@[ext]
theorem AzVector.ext {v w : AzVector R n} (h : ∀ i : Fin n, v.get i = w.get i) : v = w := by
  cases v; cases w; simp only [AzVector.mk.injEq]
  exact Vector.ext (fun i hi => h ⟨i, hi⟩)

/--
@isnad1 id=eq.0h4v.s4.1d40b85e1cf8 from=translated src=- shape=2ebb31cb vocab=91793446
-/
@[simp]
theorem AzVector.toFn_ofFn (f : Fin n → R) (i : Fin n) :
    (AzVector.ofFn f).toFn i = f i := by
  simp [toFn, ofFn, Vector.get]
  rfl

/--
@isnad1 id=eq.0h3v.s4.c7a69c909084 from=translated src=- shape=6fad1258 vocab=14c2f7e0
-/
@[simp]
theorem AzVector.ofFn_toFn (v : AzVector R n) : AzVector.ofFn v.toFn = v := by
  ext i; simp [toFn, ofFn, get, Vector.get]
  rfl

/-- `toFn` is injective.
@isnad1 id=injectiv.0h2v.s3.2fa78fd8b772 from=translated src=- shape=881aa24a vocab=aeff3f76
-/
theorem AzVector.toFn_injective : Function.Injective (AzVector.toFn (R := R) (n := n)) := by
  intro a b h; ext i; exact congrFun h i

/-! ### Map -/

/-- Apply `f` to every entry of a vector.-/
def AzVector.map {S : Type _} (f : R → S) (v : AzVector R n) : AzVector S n :=
  ⟨v.data.map f⟩

/--
@isnad1 id=eq.0h6v.s5.a0fc5194485c from=translated src=- shape=bbcbd644 vocab=155b5656
-/
@[simp]
theorem AzVector.toFn_map {S : Type _} (f : R → S) (v : AzVector R n) (i : Fin n) :
    (v.map f).toFn i = f (v.toFn i) := by
  simp [map, AzVector.toFn, Vector.get, Vector.map]
  rfl

/-! ### Zip -/

/-- Combine two vectors entrywise with `f`.-/
def AzVector.zip {S T : Type _} (f : R → S → T)
    (v : AzVector R n) (w : AzVector S n) : AzVector T n :=
  ⟨Vector.zipWith f v.data w.data⟩

/--
@isnad1 id=eq.0h8v.s5.5b8f07f2fa53 from=translated src=- shape=7932bd6d vocab=b68c9ab6
-/
@[simp]
theorem AzVector.toFn_zip {S T : Type _} (f : R → S → T)
    (v : AzVector R n) (w : AzVector S n) (i : Fin n) :
    (v.zip f w).toFn i = f (v.toFn i) (w.toFn i) := by
  simp [zip, AzVector.toFn, Vector.get, Vector.zipWith]
  rfl

/-! ### ofList -/

/-- Construct a vector from a list with a proof of the correct length.
    Usage: `AzVector.ofList [1, 2, 3]`-/
def AzVector.ofList (l : List R) (h : l.length = n := by decide) : AzVector R n :=
  ⟨⟨l.toArray, by simp [h]⟩⟩

instance : GetElem (AzVector R n) (Fin n) R (fun _ _ => True) where
  getElem v i _ := v.get i

end Azurite
-- Tengoku: root names of this library moved to Tengoku.Azurite so they do not collide with other libraries (generated)
