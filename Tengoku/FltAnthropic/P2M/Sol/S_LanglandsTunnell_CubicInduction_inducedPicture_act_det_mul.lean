import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_LanglandsTunnell_CubicInduction_inducedPicture_act_det_mul

set_option autoImplicit false

namespace WsC
namespace DC

open MvPolynomial

noncomputable section

abbrev R9 := MvPolynomial (Fin 3 × Fin 3) ℂ

def act (ν : Fin 3 → ℂ) (c d : Fin 3) (p : R9) : R9 :=
  (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
      (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
  ∑ i : Fin 3, ∑ j : Fin 3,
    (∑ m : Fin 3,
      (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
        else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
        else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
      MvPolynomial.pderiv (i, j) p

def D : R9 := (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : R9)).det

/--
@isnad1 id=eq.0h0v.s11.d5f7f338bf3c from=translated src=- shape=b04cef33 vocab=d7776a23
-/
theorem D_eq : D = X (0, 0) * X (1, 1) * X (2, 2) - X (0, 0) * X (1, 2) * X (2, 1)
    - X (0, 1) * X (1, 0) * X (2, 2) + X (0, 1) * X (1, 2) * X (2, 0)
    + X (0, 2) * X (1, 0) * X (2, 1) - X (0, 2) * X (1, 1) * X (2, 0) := by
  rw [D, Matrix.det_fin_three]
  simp only [Matrix.of_apply]

/--
@isnad1 id=eq.0h4v.s9.dbc04227755f from=translated src=- shape=75d575dd vocab=d4cc650f
-/
theorem pdX (i j a b : Fin 3) :
    pderiv (i, j) (X (a, b) : R9) = if a = i ∧ b = j then 1 else 0 := by
  classical
  rw [pderiv_X, Pi.single_apply]
  simp only [Prod.mk.injEq]

/--
@isnad1 id=lt.0h0v.s5.31822dcb5960 from=translated src=- shape=f9dc6c31 vocab=1173123d
-/
theorem lt01 : (0 : Fin 3) < 1 := by decide
/--
@isnad1 id=lt.0h0v.s5.5d6e9948f0a1 from=translated src=- shape=f9dc6c31 vocab=1173123d
-/
theorem lt02 : (0 : Fin 3) < 2 := by decide
/--
@isnad1 id=lt.0h0v.s5.24c9908ab213 from=translated src=- shape=f9dc6c31 vocab=1173123d
-/
theorem lt12 : (1 : Fin 3) < 2 := by decide
/--
@isnad1 id=not.0h0v.s5.b94308133da4 from=translated src=- shape=6cf5eb34 vocab=1173123d
-/
theorem nlt10 : ¬ (1 : Fin 3) < 0 := by decide
/--
@isnad1 id=not.0h0v.s5.697d9ed09d66 from=translated src=- shape=6cf5eb34 vocab=1173123d
-/
theorem nlt20 : ¬ (2 : Fin 3) < 0 := by decide
/--
@isnad1 id=not.0h0v.s5.4ac6e09c5b82 from=translated src=- shape=6cf5eb34 vocab=1173123d
-/
theorem nlt21 : ¬ (2 : Fin 3) < 1 := by decide
/--
@isnad1 id=ne.0h0v.s5.a12388f0aca2 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne01 : (0 : Fin 3) ≠ 1 := by decide
/--
@isnad1 id=ne.0h0v.s5.9556c64377c8 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne10 : (1 : Fin 3) ≠ 0 := by decide
/--
@isnad1 id=ne.0h0v.s5.93abf1c8e128 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne02 : (0 : Fin 3) ≠ 2 := by decide
/--
@isnad1 id=ne.0h0v.s5.d0ddbab9dc92 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne20 : (2 : Fin 3) ≠ 0 := by decide
/--
@isnad1 id=ne.0h0v.s5.1e882522a86f from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne12 : (1 : Fin 3) ≠ 2 := by decide
/--
@isnad1 id=ne.0h0v.s5.7b05c920c4d2 from=translated src=- shape=f9dc6c31 vocab=00dd0f92
-/
theorem ne21 : (2 : Fin 3) ≠ 1 := by decide

set_option maxHeartbeats 1600000 in
/--
@isnad1 id=eq.0h4v.s7.127767ea52e1 from=translated src=- shape=a4971603 vocab=55f258e7
-/
theorem key (ν : Fin 3 → ℂ) (c d : Fin 3) (P : R9) : act ν c d (D * P) = D * act ν c d P := by
  have hc : c = 0 ∨ c = 1 ∨ c = 2 := by fin_cases c <;> simp
  have hd : d = 0 ∨ d = 1 ∨ d = 2 := by fin_cases d <;> simp
  rcases hc with rfl | rfl | rfl <;> rcases hd with rfl | rfl | rfl <;>
  · simp only [act, D_eq, Fin.sum_univ_three, lt01, lt02, lt12, nlt10, nlt20, nlt21, lt_self_iff_false,
      ite_true, ite_false, pderiv_mul, map_add, map_sub, pdX, ne01, ne10, ne02, ne20, ne12, ne21,
      and_true, and_false, true_and, false_and, ite_true, ite_false, mul_one, mul_zero, zero_mul,
      add_zero, zero_add, sub_zero, zero_sub]
    ring

/--
@isnad1 id=other.0h4v.s11.255f3a929c0a from=translated src=- shape=a22013cb vocab=1e1b6967
-/
theorem main
    (ν : Fin 3 → ℂ) (c d : Fin 3) (P : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    act ν c d ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * P) =
      (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * act ν c d P := by
  exact key ν c d P

end

end WsC.DC

/--
@isnad1 id=other.0h4v.s11.255f3a929c0a from=translated src=- shape=a22013cb vocab=1e1b6967
-/
theorem solution
    (ν : Fin 3 → ℂ) (c d : Fin 3) (P : MvPolynomial (Fin 3 × Fin 3) ℂ) :
    let act : (Fin 3 → ℂ) → Fin 3 → Fin 3 →
        MvPolynomial (Fin 3 × Fin 3) ℂ → MvPolynomial (Fin 3 × Fin 3) ℂ :=
      fun ν c d p =>
        (∑ a : Fin 3, MvPolynomial.C (ν a + (![1, 0, -1] : Fin 3 → ℂ) a) *
            (MvPolynomial.X (a, c) * MvPolynomial.X (a, d))) * p +
        ∑ i : Fin 3, ∑ j : Fin 3,
          (∑ m : Fin 3,
            (if m < i then MvPolynomial.X (i, c) * MvPolynomial.X (m, d)
              else if i < m then -(MvPolynomial.X (m, c) * MvPolynomial.X (i, d))
              else (0 : MvPolynomial (Fin 3 × Fin 3) ℂ)) * MvPolynomial.X (m, j)) *
            MvPolynomial.pderiv (i, j) p
    act ν c d ((Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * P) =
      (Matrix.of fun i j : Fin 3 => (MvPolynomial.X (i, j) : MvPolynomial (Fin 3 × Fin 3) ℂ)).det * act ν c d P := by
  exact WsC.DC.main ν c d P
