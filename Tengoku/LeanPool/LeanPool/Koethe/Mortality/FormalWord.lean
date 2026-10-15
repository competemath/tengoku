/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Tengoku.LeanPool.LeanPool.Koethe.Mortality.Homogeneous
import Tengoku.LeanPool.LeanPool.Koethe.Mortality.Degree
import Tengoku.LeanPool.LeanPool.Koethe.Mortality.Minors
public import Tengoku

/-!
# Formal letters, specialization, and one scalar minor equation

A formal letter is either a fixed vector or an independently indexed hole.
The common-zero theorem is applied to the coefficients of a single pivot
minor.  Its equation count is the full word length plus one.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open KoetheMultiProjective

namespace KoetheCounterexample.Mortality

/-- A formal letter: a fixed letter vector, or a hole indexed by one of `N` variable blocks. -/
abbrev FormalLetter (k : Type*) (N : ℕ) := Triple k ⊕ Fin N

section FormalLetters

variable {k : Type*} {N d r : ℕ}

/-- The three coefficients of a formal letter, as elements of the hole ring. -/
def letterCoeffs [Field k] : FormalLetter k N → Fin 3 → HoleRing k N
  | .inl a => fun j => MvPolynomial.C (a j)
  | .inr b => fun j => MvPolynomial.X (b, j)

/-- The multidegree of a formal letter: zero for a fixed letter, one unit of its block for a
hole. -/
def letterDegree : FormalLetter k N → Fin N → ℕ
  | .inl _ => 0
  | .inr b => blockUnit b

/-- Specialize a formal letter at an assignment of the hole variables. -/
def specializeLetter (x : (Fin N × Fin 3) → k) : FormalLetter k N → Triple k
  | .inl a => a
  | .inr b => fun j => x (b, j)

/-- The forward product of the pencil lifted along a formal word. -/
def formalProd [Field k] (P : Pencil k d) (w : List (FormalLetter k N)) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) (Polynomial (HoleRing k N)) :=
  (w.map (fun a => P.lift (letterCoeffs a))).prod

/--
@isnad1 id=eq.0h4v.s5.13cbee80e5b7 from=translated src=- shape=ab1eafe3 vocab=e03b548c
-/
@[simp] theorem specializeLetter_inl (x : (Fin N × Fin 3) → k) (a : Triple k) :
    specializeLetter x (.inl a) = a := rfl

/--
@isnad1 id=eq.0h3v.s5.a2bb8b9c6c2a from=translated src=- shape=f5c25600 vocab=3abe3c70
-/
@[simp] theorem letterDegree_inl (a : Triple k) :
    letterDegree (N := N) (.inl a) = 0 := rfl

/--
@isnad1 id=eq.0h3v.s4.1620844c513d from=translated src=- shape=01e22a0e vocab=abacc9d1
-/
@[simp] theorem letterDegree_inr (b : Fin N) :
    letterDegree (k := k) (.inr b) = blockUnit b := rfl

/--
@isnad1 id=eq.0h3v.s6.5238143efd05 from=translated src=- shape=48594ee7 vocab=895bb119
-/
theorem constantWord_degree (w : List (Triple k)) :
    ((w.map (Sum.inl : Triple k → FormalLetter k N)).map letterDegree).sum = 0 := by
  simp only [List.map_map, Function.comp_def, letterDegree_inl, List.sum_map_zero]

/--
@isnad1 id=eq.0h4v.s5.699d80cf75be from=translated src=- shape=805f453d vocab=ba7e762b
-/
theorem specialize_constantWord (x : (Fin N × Fin 3) → k)
    (w : List (Triple k)) :
    (w.map (Sum.inl : Triple k → FormalLetter k N)).map (specializeLetter x) = w := by
  simp [Function.comp_def]

variable [Field k]

/--
@isnad1 id=ismultih.0h4v.s5.5de5abe6d132 from=translated src=- shape=0837c534 vocab=e48a4eca
-/
theorem letterCoeffs_hom (a : FormalLetter k N) (j : Fin 3) :
    IsMultiHomogeneous (letterCoeffs a j) (letterDegree a) := by
  cases a with
  | inl a => exact multiHom_C (a j)
  | inr b => exact multiHom_X b j

/--
@isnad1 id=matrixco.0h5v.s6.b926cef7a9e3 from=translated src=- shape=d61efe5f vocab=c371a237
-/
theorem formalProd_hom (P : Pencil k d) (w : List (FormalLetter k N)) :
    MatrixCoeffHom (formalProd P w) (w.map letterDegree).sum :=
  matrixCoeffHom_prod w _ _
    (fun a _ => lift_coeffHom P (letterCoeffs a) (letterDegree a) (letterCoeffs_hom a))

/--
@isnad1 id=le.1h8v.s8.42d969f2652e from=translated src=- shape=8bb3189b vocab=c7d64c19
-/
theorem formalMinor_natDegree_le (P : Pencil k d) (w : List (FormalLetter k N))
    (I J : Fin r → Fin (d + 1)) (hI : Function.Injective I) :
    (((formalProd P w).submatrix I J).det).natDegree ≤ w.length := by
  simpa only [formalProd, List.map_map, Function.comp_def, List.length_map] using
    det_liftWord_natDegree_le P (w.map letterCoeffs) I J hI

/--
@isnad1 id=eq.0h6v.s9.c13c7188ff71 from=translated src=- shape=ad3a6afb vocab=50d1997b
-/
theorem specialize_lift (P : Pencil k d) (a : FormalLetter k N)
    (x : (Fin N × Fin 3) → k) :
    (P.lift (letterCoeffs a)).map (Polynomial.mapRingHom (MvPolynomial.eval x)) =
      P.eval (specializeLetter x a) := by
  apply Matrix.ext
  intro i j
  change Polynomial.map (MvPolynomial.eval x) (P.lift (letterCoeffs a) i j) = _
  cases a <;>
    simp only [Pencil.lift, Pencil.eval, letterCoeffs, specializeLetter,
      MvPolynomial.algebraMap_eq, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_C, Polynomial.map_X, Polynomial.map_sum, map_sum, map_mul,
      MvPolynomial.eval_C, MvPolynomial.eval_X, mul_comm]

/--
@isnad1 id=eq.0h6v.s9.39c035b7ccbf from=translated src=- shape=fc640249 vocab=d78782d2
-/
theorem specialize_formalProd (P : Pencil k d) (w : List (FormalLetter k N))
    (x : (Fin N × Fin 3) → k) :
    (formalProd P w).map (Polynomial.mapRingHom (MvPolynomial.eval x)) =
      P.wordProd (w.map (specializeLetter x)) := by
  classical
  induction w with
  | nil =>
    simp only [formalProd, List.map_nil, List.prod_nil, Pencil.wordProd_nil]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  | cons a w ih =>
    simp only [formalProd, List.map_cons, List.prod_cons] at ih ⊢
    rw [Matrix.map_mul, specialize_lift, ih]
    rfl

end FormalLetters

end KoetheCounterexample.Mortality

end
