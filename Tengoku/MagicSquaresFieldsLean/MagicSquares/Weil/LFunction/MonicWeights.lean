import Tengoku.Seed.LinearAlgebra.Lagrange
import Tengoku.Seed.NumberTheory.MulChar.Basic
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares.LN97

open Polynomial
open scoped BigOperators

/-!
# The monic-polynomial character weights in LN97 Theorem 5.39

For a split polynomial, the resultant weight is a product of character
values at its distinct roots, with the usual degree-dependent sign.
Monic polynomials of degree `n` are enumerated by their `n` lower coefficients.
Lagrange interpolation gives a permutation of these coefficients which
rescales the value at one root and fixes the values at all other roots.
This proves the cancellation required for the finite L-polynomial.
-/

section Rescale

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

private def affineRescale (l : V →ₗ[F] F) (b : V) (c a : F) (x : V) : V :=
  x + ((a - 1) * (c + l x)) • b

private theorem affineRescale_comp (l : V →ₗ[F] F) (b : V) (hb : l b = 1)
    (c a d : F) (x : V) :
    affineRescale l b c a (affineRescale l b c d x) = affineRescale l b c (a * d) x := by
  simp only [affineRescale, map_add, map_smul, hb, smul_eq_mul, mul_one]
  rw [add_assoc, ← add_smul]
  congr 1
  congr 1
  ring

private def affineRescaleEquiv (l : V →ₗ[F] F) (b : V) (hb : l b = 1)
    (c : F) (u : Fˣ) : V ≃ V where
  toFun := affineRescale l b c u
  invFun := affineRescale l b c ↑u⁻¹
  left_inv x := by rw [affineRescale_comp l b hb]; simp [affineRescale]
  right_inv x := by rw [affineRescale_comp l b hb]; simp [affineRescale]

end Rescale

variable {F : Type*} [Field F]

/-- The monic polynomial with prescribed lower coefficients.-/
noncomputable def monicOfCoeffs (n : ℕ) (v : Fin n → F) : Polynomial F :=
  X ^ n + ((degreeLTEquiv F n).symm v : Polynomial F)

/-- This encoding enumerates exactly the monic polynomials of degree `n`.-/
noncomputable def monicOfCoeffsEquiv (n : ℕ) :
    (Fin n → F) ≃ {p : Polynomial F // p.Monic ∧ p.natDegree = n} :=
  (degreeLTEquiv F n).symm.toEquiv.trans (monicEquivDegreeLT n).symm

/--
@isnad1 id=eq.0h3v.s8.20249a8c3c74 from=translated src=- shape=d538acc3 vocab=f6728bd5
-/
@[simp]
theorem monicOfCoeffsEquiv_val (n : ℕ) (v : Fin n → F) :
    (monicOfCoeffsEquiv n v).1 = monicOfCoeffs n v := rfl

/--
@isnad1 id=monic.0h3v.s4.cfe108891222 from=translated src=- shape=d798f006 vocab=4da80157
-/
theorem monicOfCoeffs_monic (n : ℕ) (v : Fin n → F) : (monicOfCoeffs n v).Monic :=
  (monicOfCoeffsEquiv n v).2.1

/--
@isnad1 id=eq.0h3v.s4.8c65ce12de83 from=translated src=- shape=833ca3e9 vocab=dc05dc7a
-/
@[simp]
theorem monicOfCoeffs_natDegree (n : ℕ) (v : Fin n → F) :
    (monicOfCoeffs n v).natDegree = n := (monicOfCoeffsEquiv n v).2.2

/--
@isnad1 id=eq.0h2v.s5.d2ed108f61ab from=translated src=- shape=6a8a44be vocab=67d7a1c5
-/
@[simp]
theorem monicOfCoeffs_zero (v : Fin 0 → F) : monicOfCoeffs 0 v = 1 := by
  simp [monicOfCoeffs, degreeLTEquiv]

/--
@isnad1 id=eq.0h2v.s7.4e052905e247 from=translated src=- shape=58d807f7 vocab=8e081a9c
-/
@[simp]
theorem monicOfCoeffs_one (v : Fin 1 → F) : monicOfCoeffs 1 v = X + C (v 0) := by
  simp [monicOfCoeffs, degreeLTEquiv]

private noncomputable def lowerEval (n : ℕ) (a : F) : (Fin n → F) →ₗ[F] F :=
  (Polynomial.leval a).comp
    ((degreeLT F n).subtype.comp (degreeLTEquiv F n).symm.toLinearMap)

private theorem monicOfCoeffs_eval (n : ℕ) (v : Fin n → F) (a : F) :
    (monicOfCoeffs n v).eval a = a ^ n + lowerEval n a v := by
  simp [monicOfCoeffs, lowerEval, Polynomial.leval_apply]

/-- Product of the character values of a polynomial at specified roots.
The characters may differ, so the construction also covers root exponents.-/
noncomputable def splitEvaluationWeight {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) (g : Polynomial F) : ℂ :=
  ∏ i, chars i (g.eval (roots i))

/--
@isnad1 id=eq.0h4v.s6.816131b0e485 from=translated src=- shape=234c5168 vocab=e774c117
-/
@[simp]
theorem splitEvaluationWeight_one {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) : splitEvaluationWeight roots chars 1 = 1 := by
  simp [splitEvaluationWeight]

/--
@isnad1 id=eq.0h6v.s7.ce10f0011e40 from=translated src=- shape=6d5e505a vocab=44cf169f
-/
theorem splitEvaluationWeight_mul {r : ℕ} (roots : Fin r → F)
    (chars : Fin r → MulChar F ℂ) (g h : Polynomial F) :
    splitEvaluationWeight roots chars (g * h) =
      splitEvaluationWeight roots chars g * splitEvaluationWeight roots chars h := by
  simp [splitEvaluationWeight, Finset.prod_mul_distrib]

/-- For `n ≥ r`, rescale exactly one of the root evaluations while
permuting the set of all monic degree-`n` polynomials.
@isnad1 id=ex.2h6v.s7.f1c6e1a41f38 from=translated src=- shape=75617bdb vocab=d0e63dec
-/
theorem exists_monic_rescale {r n : ℕ} (roots : Fin r → F)
    (hinj : Function.Injective roots) (hn : r ≤ n) (j : Fin r) (u : Fˣ) :
    ∃ e : (Fin n → F) ≃ (Fin n → F), ∀ v i,
      (monicOfCoeffs n (e v)).eval (roots i) =
        if i = j then (u : F) * (monicOfCoeffs n v).eval (roots i)
        else (monicOfCoeffs n v).eval (roots i) := by
  classical
  let p := Lagrange.basis Finset.univ roots j
  have hp : p ∈ degreeLT F n := by
    rw [mem_degreeLT]
    have hdegree := Lagrange.degree_basis hinj.injOn (Finset.mem_univ j)
    simp only [Finset.card_univ, Fintype.card_fin] at hdegree
    change p.degree = _ at hdegree
    rw [hdegree]
    exact_mod_cast (show r - 1 < n by have := j.isLt; omega)
  let b : Fin n → F := degreeLTEquiv F n ⟨p, hp⟩
  have hb (i : Fin r) : lowerEval n (roots i) b = if i = j then 1 else 0 := by
    change (Polynomial.eval (roots i) ((degreeLTEquiv F n).symm b : Polynomial F)) = _
    rw [show (degreeLTEquiv F n).symm b = ⟨p, hp⟩ from
      (degreeLTEquiv F n).symm_apply_apply _]
    change p.eval (roots i) = _
    split_ifs with hij
    · subst i
      exact Lagrange.eval_basis_self hinj.injOn (Finset.mem_univ j)
    · exact Lagrange.eval_basis_of_ne (Ne.symm hij) (Finset.mem_univ i)
  have hbj : lowerEval n (roots j) b = 1 := by simpa using hb j
  let e := affineRescaleEquiv (lowerEval n (roots j)) b hbj (roots j ^ n) u
  refine ⟨e, ?_⟩
  intro v i
  simp only [monicOfCoeffs_eval]
  change roots i ^ n + lowerEval n (roots i)
    (v + (((u : F) - 1) * (roots j ^ n + lowerEval n (roots j) v)) • b) = _
  rw [map_add, map_smul, hb]
  split_ifs with hij
  · subst i
    simp only [smul_eq_mul, mul_one]
    ring
  · simp

section Finite

variable [Fintype F]

/-- Cancellation of the sum of evaluation weights in every degree at least
the number of distinct roots, provided one root character is nontrivial.
This is the split case of the cancellation step (5.22) in LN97 5.39.
@isnad1 id=eq.3h5v.s7.0ea121331de1 from=translated src=- shape=542eb8f3 vocab=62bda428
-/
theorem sum_splitEvaluationWeight_monic_eq_zero {r n : ℕ}
    (roots : Fin r → F) (hinj : Function.Injective roots)
    (chars : Fin r → MulChar F ℂ) (hn : r ≤ n)
    (hchars : ∃ j, chars j ≠ 1) :
    ∑ v : Fin n → F, splitEvaluationWeight roots chars (monicOfCoeffs n v) = 0 := by
  classical
  obtain ⟨j, hj⟩ := hchars
  obtain ⟨u, hu⟩ := MulChar.ne_one_iff.mp hj
  obtain ⟨e, he⟩ := exists_monic_rescale roots hinj hn j u
  apply eq_zero_of_mul_eq_self_left hu
  calc
    _ = ∑ v : Fin n → F, splitEvaluationWeight roots chars (monicOfCoeffs n (e v)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      simp only [splitEvaluationWeight]
      rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ j),
        ← Finset.mul_prod_erase Finset.univ (fun i => chars i ((monicOfCoeffs n (e v)).eval (roots i)))
          (Finset.mem_univ j), he v j, ite_eq_left rfl, map_mul]
      have hrest : (∏ i ∈ Finset.univ.erase j, chars i ((monicOfCoeffs n (e v)).eval (roots i))) =
          ∏ i ∈ Finset.univ.erase j, chars i ((monicOfCoeffs n v).eval (roots i)) := by
        apply Finset.prod_congr rfl
        intro i hi
        rw [he v i, ite_eq_right (Finset.mem_erase.mp hi).1]
      rw [hrest]
      ring
    _ = _ := e.sum_comp (fun v => splitEvaluationWeight roots chars (monicOfCoeffs n v))

end Finite
end MagicSquares.LN97
