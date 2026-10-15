/-
Copyright (c) 2026 Tom Adamczewski and Epoch AI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: GPT-6 Astra, Tom Adamczewski
-/
module

public import Tengoku.LeanPool.LeanPool.Koethe.MultiProjective
public import Tengoku.LeanPool.LeanPool.Koethe.Pencil
public import Tengoku

/-!
# Coefficientwise multihomogeneity for matrix words

The central parameter is a univariate polynomial variable.  Its coefficient
ring is a multivariate polynomial ring whose variables are grouped into
independent triples.  The zero polynomial is homogeneous of every degree.
-/

@[expose] public section

noncomputable section

open scoped BigOperators
open KoetheMultiProjective

namespace KoetheCounterexample.Mortality

/-- The polynomial ring in `N` blocks of three hole variables. -/
abbrev HoleRing (k : Type*) [CommSemiring k] (N : ℕ) :=
  MvPolynomial (Fin N × Fin 3) k

/-- The multidegree contributed by one occurrence of block `b`. -/
def blockUnit {N : ℕ} (b : Fin N) : Fin N → ℕ := fun c => if c = b then 1 else 0

section Homogeneity

variable {k : Type*} [CommRing k] {N : ℕ}

/-- The coefficients in the central parameter are all multihomogeneous of
one and the same specified multidegree. -/
def CoeffHom (p : Polynomial (HoleRing k N)) (e : Fin N → ℕ) : Prop :=
  ∀ j, IsMultiHomogeneous (p.coeff j) e

/--
@isnad1 id=ismultih.1h6v.s6.a98a79737ad9 from=translated src=- shape=56e5cd32 vocab=7cfb7643
-/
theorem multiHom_sum {ι : Type*} (s : Finset ι) (f : ι → HoleRing k N)
    {e : Fin N → ℕ} (hf : ∀ i ∈ s, IsMultiHomogeneous (f i) e) :
    IsMultiHomogeneous (∑ i ∈ s, f i) e := by
  classical
  revert hf
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    intro hf
    rw [Finset.sum_insert hi]
    exact (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/--
@isnad1 id=ismultih.0h3v.s7.d859d5516e96 from=translated src=- shape=5230d381 vocab=ccc83b6d
-/
theorem multiHom_C (a : k) :
    IsMultiHomogeneous (MvPolynomial.C a : HoleRing k N) 0 := by
  exact isMultiHomogeneous_monomial (fun _ => blockDegree_zero _) a

/--
@isnad1 id=ismultih.0h4v.s5.a3c515583ffe from=translated src=- shape=9be2c863 vocab=ed3ea3be
-/
theorem multiHom_X (b : Fin N) (j : Fin 3) :
    IsMultiHomogeneous (MvPolynomial.X (b, j) : HoleRing k N) (blockUnit b) := by
  apply isMultiHomogeneous_monomial
  intro c
  by_cases h : c = b
  · subst c
    simp [blockDegree, blockUnit, Finsupp.single_apply]
  · simp [blockDegree, blockUnit, h]

/--
@isnad1 id=coeffhom.0h3v.s7.b7498aac3581 from=translated src=- shape=36e9d9fe vocab=8afb5a7d
-/
@[simp] theorem coeffHom_zero (e : Fin N → ℕ) :
    CoeffHom (0 : Polynomial (HoleRing k N)) e := by
  intro j
  simp

/--
@isnad1 id=coeffhom.1h4v.s8.f3a2bfb22800 from=translated src=- shape=a1542a1c vocab=2e2821fc
-/
theorem coeffHom_C {a : HoleRing k N} {e : Fin N → ℕ}
    (ha : IsMultiHomogeneous a e) : CoeffHom (Polynomial.C a) e := by
  intro j
  by_cases h : j = 0
  · simpa only [Polynomial.coeff_C, ite_eq_left h] using ha
  · simp only [Polynomial.coeff_C, ite_eq_right h, isMultiHomogeneous_zero]

/--
@isnad1 id=coeffhom.0h2v.s7.23772899f3ce from=translated src=- shape=b97247da vocab=8afb5a7d
-/
@[simp] theorem coeffHom_one : CoeffHom (1 : Polynomial (HoleRing k N)) 0 := by
  simpa only [map_one] using coeffHom_C (multiHom_C (N := N) (1 : k))

/--
@isnad1 id=coeffhom.0h2v.s6.494200955eab from=translated src=- shape=a340dc22 vocab=5698c326
-/
theorem coeffHom_X : CoeffHom (Polynomial.X : Polynomial (HoleRing k N)) 0 := by
  intro j
  by_cases h : 1 = j
  · simpa only [Polynomial.coeff_X, ite_eq_left h, map_one] using
      multiHom_C (N := N) (1 : k)
  · simp only [Polynomial.coeff_X, ite_eq_right h, isMultiHomogeneous_zero]

/--
@isnad1 id=coeffhom.2h5v.s8.affedc9210da from=translated src=- shape=eeb3154b vocab=2be86718
-/
theorem CoeffHom.add {p q : Polynomial (HoleRing k N)} {e : Fin N → ℕ}
    (hp : CoeffHom p e) (hq : CoeffHom q e) : CoeffHom (p + q) e := by
  intro j
  simpa only [Polynomial.coeff_add] using (hp j).add (hq j)

/--
@isnad1 id=coeffhom.1h6v.s7.618e5bf0b1ab from=translated src=- shape=2f6712cf vocab=e013a454
-/
theorem CoeffHom.sum {ι : Type*} (s : Finset ι)
    (f : ι → Polynomial (HoleRing k N)) {e : Fin N → ℕ}
    (hf : ∀ i ∈ s, CoeffHom (f i) e) : CoeffHom (∑ i ∈ s, f i) e := by
  intro j
  rw [Polynomial.finsetSum_coeff]
  exact multiHom_sum s _ (fun i hi => hf i hi j)

/--
@isnad1 id=coeffhom.2h6v.s8.922c4494137c from=translated src=- shape=cfa1e99b vocab=ba3a8888
-/
theorem CoeffHom.mul {p q : Polynomial (HoleRing k N)} {e f : Fin N → ℕ}
    (hp : CoeffHom p e) (hq : CoeffHom q f) : CoeffHom (p * q) (e + f) := by
  intro j
  rw [Polynomial.coeff_mul]
  exact multiHom_sum _ _ (fun i _ => (hp i.1).mul (hq i.2))

/-- The common multidegree of every coefficient of every matrix entry. -/
def MatrixCoeffHom {m n : Type*} (A : Matrix m n (Polynomial (HoleRing k N)))
    (e : Fin N → ℕ) : Prop := ∀ i j, CoeffHom (A i j) e

/--
@isnad1 id=matrixco.0h3v.s7.1b2c5390d89e from=translated src=- shape=6e47f54b vocab=05a950bb
-/
theorem matrixCoeffHom_one {n : Type*} [DecidableEq n] :
    MatrixCoeffHom (1 : Matrix n n (Polynomial (HoleRing k N))) 0 := by
  intro i j
  by_cases h : i = j <;> simp [Matrix.one_apply, h, coeffHom_one, coeffHom_zero]

/--
@isnad1 id=matrixco.2h9v.s8.cc4357a37641 from=translated src=- shape=84b7cd27 vocab=4fbb50ac
-/
theorem MatrixCoeffHom.mul {m n o : Type*} [Fintype n]
    {A : Matrix m n (Polynomial (HoleRing k N))}
    {B : Matrix n o (Polynomial (HoleRing k N))} {e f : Fin N → ℕ}
    (hA : MatrixCoeffHom A e) (hB : MatrixCoeffHom B f) :
    MatrixCoeffHom (A * B) (e + f) := by
  intro i j
  rw [Matrix.mul_apply]
  exact CoeffHom.sum _ _ (fun x _ => (hA i x).mul (hB x j))

/--
@isnad1 id=matrixco.1h7v.s9.c61c76e77a0f from=translated src=- shape=992aa300 vocab=a0a8474b
-/
theorem matrixCoeffHom_prod {n α : Type*} [Fintype n] [DecidableEq n]
    (w : List α) (L : α → Matrix n n (Polynomial (HoleRing k N)))
    (e : α → Fin N → ℕ) (hw : ∀ a ∈ w, MatrixCoeffHom (L a) (e a)) :
    MatrixCoeffHom (w.map L).prod (w.map e).sum := by
  revert hw
  induction w with
  | nil =>
    intro _
    simpa using (matrixCoeffHom_one (n := n) (N := N) (k := k))
  | cons a w ih =>
    intro hw
    simp only [List.map_cons, List.prod_cons, List.sum_cons]
    exact (hw a (List.mem_cons_self ..)).mul
      (ih (fun b hb => hw b (List.mem_cons_of_mem _ hb)))

end Homogeneity

section Lift

variable {k : Type*} [Field k] {N d : ℕ}

/--
@isnad1 id=matrixco.1h6v.s7.13dd8f2d6208 from=translated src=- shape=a2ae30ca vocab=abbb3214
-/
theorem lift_coeffHom (P : Pencil k d) (a : Fin 3 → HoleRing k N)
    (e : Fin N → ℕ) (ha : ∀ i, IsMultiHomogeneous (a i) e) :
    MatrixCoeffHom (P.lift a) e := by
  intro row col
  unfold Pencil.lift
  rw [MvPolynomial.algebraMap_eq]
  apply CoeffHom.add
  · apply coeffHom_C
    apply multiHom_sum
    intro i _
    simpa only [zero_add] using (multiHom_C (P.scalar i row col)).mul (ha i)
  · have hlin : CoeffHom
        (Polynomial.C (∑ i : Fin 3, MvPolynomial.C (P.linear i row col) * a i)) e := by
      apply coeffHom_C
      apply multiHom_sum
      intro i _
      simpa only [zero_add] using (multiHom_C (P.linear i row col)).mul (ha i)
    simpa only [zero_add] using coeffHom_X.mul hlin

end Lift

end KoetheCounterexample.Mortality

end
