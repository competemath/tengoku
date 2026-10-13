/-
Copyright (c) 2025 Bryan Wang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bryan Wang
-/
module

public import Tengoku

/-!
# Defs

Material destined for Mathlib.
-/

@[expose] public section

namespace Matrix.GeneralLinearGroup

variable {n R : Type*} [DecidableEq n] [Fintype n] [CommRing R]

/-- The invertible diagonal matrix associated to a vector of units (the diagonal entries).
-/
def diagonal (d : n → Rˣ) : GL n R :=
  ⟨.diagonal (d ·), .diagonal <| fun i ↦ ((d i)⁻¹ : Rˣ),
    by simp, by simp⟩

/--
@isnad1 id=eq.0h3v.s6.bb26bc9ffda5 from=translated src=- shape=6ba04de8 vocab=c32b6a1a
-/
@[simp]
lemma val_diagonal (d : n → Rˣ) :
    (diagonal d).1 = .diagonal (d ·) := rfl

/--
@isnad1 id=eq.0h2v.s6.369c8131505b from=translated src=- shape=14c16321 vocab=c3520942
-/
@[simp]
lemma diagonal_one : diagonal (n := n) (R := R) 1 = 1 := by
  ext; simp [Matrix.GeneralLinearGroup.diagonal]

namespace GL2

-- **TODO** This might have just landed in mathlib as an AddChar?
/-- The unipotent matrix element `!![1, t; 0, 1]`. -/
noncomputable def unipotent (t : R) : GL (Fin 2) R :=
  ⟨!![1, t; 0, 1], !![1, -t; 0, 1],
    by ext i j; fin_cases i <;> fin_cases j <;> simp,
    by ext i j; fin_cases i <;> fin_cases j <;> simp⟩

/--
@isnad1 id=eq.0h2v.s8.0a7c46247bb0 from=translated src=- shape=91de8ec8 vocab=5cbd05c6
-/
lemma unipotent_def (t : R) :
    (unipotent t : Matrix (Fin 2) (Fin 2) R) = !![1, t; 0, 1] := rfl

/--
@isnad1 id=eq.0h2v.s6.85aec63ab4d2 from=translated src=- shape=70c2e655 vocab=cf7a6234
-/
@[simp] lemma unipotent_zero_zero (t : R) : unipotent t 0 0 = 1 := rfl
/--
@isnad1 id=eq.0h2v.s6.5eea0bfdec10 from=translated src=- shape=0ebc8534 vocab=cf7a6234
-/
@[simp] lemma unipotent_zero_one (t : R) : unipotent t 0 1 = t := rfl
/--
@isnad1 id=eq.0h2v.s6.00bda4172b3a from=translated src=- shape=70c2e655 vocab=cf7a6234
-/
@[simp] lemma unipotent_one_zero (t : R) : unipotent t 1 0 = 0 := rfl
/--
@isnad1 id=eq.0h2v.s6.4087928acf2c from=translated src=- shape=70c2e655 vocab=cf7a6234
-/
@[simp] lemma unipotent_one_one (t : R) : unipotent t 1 1 = 1 := rfl

/--
@isnad1 id=eq.0h2v.s7.f223548a6e2c from=translated src=- shape=4fb0e637 vocab=86c9cfdf
-/
@[simp]
lemma unipotent_inv (t : R) :
    (unipotent t)⁻¹ = unipotent (-t) := by ext1; rfl

/--
@isnad1 id=eq.0h3v.s7.39af7831ff14 from=translated src=- shape=26a34802 vocab=0585f7a7
-/
lemma unipotent_mul (t₁ t₂ : R) :
    unipotent t₂ * unipotent t₁ = unipotent (t₁ + t₂) := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [unipotent_def]

end GL2

end Matrix.GeneralLinearGroup
