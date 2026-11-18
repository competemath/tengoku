import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_GaloisRep_FrobeniusPowerDense

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Representation_cayleyHamilton_of_frobeniusPowerDense.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Representation_cayleyHamilton_of_frobeniusPowerDense

set_option autoImplicit false

open _root_.Matrix

namespace Matrix
export _root_.Matrix (trace_sub ext sub_apply trace_smul det_one scalar trace_one trace_mul_comm det_fin_two det_mul one_apply smul_apply det det_pow of one mul_apply trace module trace_fin_two)
open _root_.Matrix

variable {R : Type*} [CommRing R]

/--
@isnad1 id=eq.0h2v.s8.fde14fb5b9c1 from=translated src=- shape=48f608a3 vocab=47a7532c
-/
theorem sq_eq_trace_smul_sub_det_smul_one' (M : Matrix (Fin 2) (Fin 2) R) :
    M ^ 2 = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) R) := by
  ext i j
  simp only [pow_two, Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two,
    Matrix.det_fin_two, Matrix.sub_apply, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  fin_cases i <;> fin_cases j <;> simp <;> ring

/--
@isnad1 id=eq.0h3v.s9.11b062586957 from=translated src=- shape=c2afba95 vocab=d15b08ed
-/
theorem pow_add_two_eq_trace_smul_sub_det_smul' (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    M ^ (k + 2) = M.trace • M ^ (k + 1) - M.det • M ^ k := by
  have h : M ^ (k + 2) = M ^ k * M ^ 2 := by rw [← pow_add]
  rw [h, sq_eq_trace_smul_sub_det_smul_one', Matrix.mul_sub, mul_smul_comm, mul_smul_comm,
    mul_one, ← pow_succ]

/--
@isnad1 id=eq.0h3v.s9.bfad2dd2e513 from=translated src=- shape=f43945af vocab=f26931c3
-/
theorem trace_pow_add_two (M : Matrix (Fin 2) (Fin 2) R) (k : ℕ) :
    (M ^ (k + 2)).trace = M.trace * (M ^ (k + 1)).trace - M.det * (M ^ k).trace := by
  rw [pow_add_two_eq_trace_smul_sub_det_smul', Matrix.trace_sub, Matrix.trace_smul,
    Matrix.trace_smul, smul_eq_mul, smul_eq_mul]

end Matrix

noncomputable section

namespace CayleyHamiltonDensity

section Abstract

variable {k : Type*} [CommRing k] {B : Type*} [Ring B] [Algebra k B]

/--
@isnad1 id=eq.1h4v.s8.d82af1f45b9c from=translated src=- shape=e6c49899 vocab=a6873015
-/
theorem sq_eq_of_quadRel {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    a * a = M.trace • a - M.det • (1 : B) :=
  sub_eq_zero.mp (by rw [← h]; abel)

/--
@isnad1 id=eq.1h4v.s8.924a44613cce from=translated src=- shape=5d9ff287 vocab=a6873015
-/
theorem mul_compl_eq_det_smul_one {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    a * (M.trace • (1 : B) - a) = M.det • (1 : B) := by
  rw [mul_sub, mul_smul_comm, mul_one, sq_eq_of_quadRel h]
  abel

/--
@isnad1 id=eq.1h4v.s8.8acc2e49cbb1 from=translated src=- shape=d07a9d4c vocab=a6873015
-/
theorem compl_mul_eq_det_smul_one {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    (M.trace • (1 : B) - a) * a = M.det • (1 : B) := by
  rw [sub_mul, smul_mul_assoc, one_mul, sq_eq_of_quadRel h]
  abel

/--
@isnad1 id=commute.1h4v.s8.4c0746a4684f from=translated src=- shape=91f8fbdb vocab=c4a35132
-/
theorem commute_complRoot {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    Commute a (M.trace • (1 : B) - a) := by
  unfold Commute SemiconjBy
  rw [mul_compl_eq_det_smul_one h, compl_mul_eq_det_smul_one h]

/--
@isnad1 id=eq.1h5v.s8.a800c75cc58b from=translated src=- shape=2a076c89 vocab=de799445
-/
theorem pow_add_compl_pow_eq_trace_pow_smul_one {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) (m : ℕ) :
    a ^ m + (M.trace • (1 : B) - a) ^ m = (M ^ m).trace • (1 : B) := by
  set b : B := M.trace • (1 : B) - a with hb
  have hsum : a + b = M.trace • (1 : B) := by rw [hb]; abel
  have hcomm : Commute a b := commute_complRoot h
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    match m with
    | 0 =>
      simp only [pow_zero, Matrix.trace_one, Fintype.card_fin, Nat.cast_ofNat, two_smul]
    | 1 =>
      simp only [pow_one, hsum]
    | (m + 2) =>

      have hc1 : b * a ^ (m + 1) = a ^ (m + 1) * b := (hcomm.symm.pow_right (m + 1)).eq
      have hc2 : b * a ^ m = a ^ m * b := (hcomm.symm.pow_right m).eq
      have hrec : a ^ (m + 2) + b ^ (m + 2)
          = (a + b) * (a ^ (m + 1) + b ^ (m + 1)) - (a * b) * (a ^ m + b ^ m) := by
        have e1 : (a + b) * (a ^ (m + 1) + b ^ (m + 1))
            = a ^ (m + 2) + a * b ^ (m + 1) + (a ^ (m + 1) * b + b ^ (m + 2)) := by
          rw [add_mul, mul_add, mul_add, ← pow_succ', ← pow_succ', hc1]
        have e2 : (a * b) * (a ^ m + b ^ m)
            = a ^ (m + 1) * b + a * b ^ (m + 1) := by
          rw [mul_add, mul_assoc a b (a ^ m), hc2, ← mul_assoc, ← pow_succ',
            mul_assoc a b (b ^ m), ← pow_succ']
        rw [e1, e2]
        abel
      rw [hrec, ih (m + 1) (by omega), ih m (by omega), hsum,
        mul_compl_eq_det_smul_one h, smul_mul_smul_comm, smul_mul_smul_comm, mul_one,
        ← sub_smul, ← Matrix.trace_pow_add_two]

/--
@isnad1 id=eq.1h5v.s9.dcfb6b86a503 from=translated src=- shape=81c6cdf4 vocab=de799445
-/
theorem quadRel_pow {a : B} {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) (n : ℕ) :
    a ^ n * a ^ n - (M ^ n).trace • a ^ n + (M ^ n).det • (1 : B) = 0 := by
  set b : B := M.trace • (1 : B) - a with hb
  have hcomm : Commute a b := commute_complRoot h

  have hsum : (M ^ n).trace • (1 : B) = a ^ n + b ^ n :=
    (pow_add_compl_pow_eq_trace_pow_smul_one h n).symm

  have hprod : (M ^ n).det • (1 : B) = a ^ n * b ^ n := by
    rw [← hcomm.mul_pow, hb, mul_compl_eq_det_smul_one h, smul_pow, one_pow,
      Matrix.det_pow]

  have hsmul : (M ^ n).trace • a ^ n = ((M ^ n).trace • (1 : B)) * a ^ n := by
    rw [smul_mul_assoc, one_mul]
  rw [hsmul, hsum, hprod, add_mul, (hcomm.pow_pow n n).eq]
  abel

/--
@isnad1 id=eq.3h6v.s8.44acc9342d5e from=translated src=- shape=f523d030 vocab=a6873015
-/
theorem quadRel_conj {a u v : B} (huv : u * v = 1) (hvu : v * u = 1)
    {M : Matrix (Fin 2) (Fin 2) k}
    (h : a * a - M.trace • a + M.det • (1 : B) = 0) :
    (u * a * v) * (u * a * v) - M.trace • (u * a * v) + M.det • (1 : B) = 0 := by
  have key : (u * a * v) * (u * a * v) - M.trace • (u * a * v) + M.det • (1 : B)
      = u * (a * a - M.trace • a + M.det • (1 : B)) * v := by
    have e1 : (u * a * v) * (u * a * v) = u * (a * a) * v := by
      calc (u * a * v) * (u * a * v) = u * a * (v * u) * a * v := by
            simp only [mul_assoc]
        _ = u * (a * a) * v := by rw [hvu, mul_one, mul_assoc u a a]
    have e2 : M.trace • (u * a * v) = u * (M.trace • a) * v := by
      rw [mul_smul_comm, smul_mul_assoc]
    have e3 : M.det • (1 : B) = u * (M.det • (1 : B)) * v := by
      rw [mul_smul_comm, smul_mul_assoc, mul_one, huv]
    rw [mul_add, add_mul, mul_sub, sub_mul, ← e1, ← e2, ← e3]
  rw [key, h, mul_zero, zero_mul]

end Abstract

section MatrixConj

variable {k : Type*} [CommRing k]

/--
@isnad1 id=eq.1h4v.s8.0b95d1f010df from=translated src=- shape=ee2b07d4 vocab=ec358fb8
-/
theorem trace_matrix_conj {P Q : Matrix (Fin 2) (Fin 2) k} (hQP : Q * P = 1)
    (N : Matrix (Fin 2) (Fin 2) k) : (P * N * Q).trace = N.trace := by
  rw [Matrix.trace_mul_comm, ← mul_assoc, hQP, one_mul]

/--
@isnad1 id=eq.1h4v.s8.786cc8e6afb0 from=translated src=- shape=9ed6d8d6 vocab=556c2a3c
-/
theorem det_matrix_conj {P Q : Matrix (Fin 2) (Fin 2) k} (hPQ : P * Q = 1)
    (N : Matrix (Fin 2) (Fin 2) k) : (P * N * Q).det = N.det := by
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm P.det, mul_assoc, ← Matrix.det_mul, hPQ,
    Matrix.det_one, mul_one]

end MatrixConj

section DensityStep

/--
@isnad1 id=eq.1h5v.s7.ffdc00de3d5a from=translated src=- shape=8add4b55 vocab=8f8eb867
-/
theorem apply_eq_of_mul_inv_mem_ker {G M : Type*} [Group G] [Monoid M] (f : G →* M)
    {x σ : G} (h : x * σ⁻¹ ∈ f.ker) : f σ = f x := by
  have h1 : f x * f σ⁻¹ = 1 := by rw [← map_mul]; exact h
  have h2 : f σ⁻¹ * f σ = 1 := by rw [← map_mul, inv_mul_cancel, map_one]
  calc f σ = (f x * f σ⁻¹) * f σ := by rw [h1, one_mul]
    _ = f x * (f σ⁻¹ * f σ) := mul_assoc _ _ _
    _ = f x := by rw [h2, mul_one]

/--
@isnad1 id=eq.0h4v.s7.fe134c69c16e from=translated src=- shape=aab31211 vocab=a8c362c8
-/
theorem apply_mul_apply_inv_cancel {G M : Type*} [Group G] [Monoid M] (f : G →* M) (g : G) :
    f g * f g⁻¹ = 1 := by
  rw [← map_mul, mul_inv_cancel, map_one]

/--
@isnad1 id=eq.0h4v.s7.3d4d49d84fbb from=translated src=- shape=bcb6f604 vocab=a8c362c8
-/
theorem apply_inv_mul_apply_cancel {G M : Type*} [Group G] [Monoid M] (f : G →* M) (g : G) :
    f g⁻¹ * f g = 1 := by
  rw [← map_mul, inv_mul_cancel, map_one]

variable {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]

/--
@isnad1 id=eq.2h6v.s13.1c1ed45753bd from=translated src=- shape=d57b21bc vocab=e7f937eb
-/
theorem cayleyHamilton_of_frobeniusPowerDense_aux
    (ρV : Representation k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k)
    {S : Finset ℕ}
    (hCH : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          ρV τ * ρV τ - (ρ τ).trace • ρV τ + (ρ τ).det • (1 : Module.End k V) = 0)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ ρV.ker))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρV σ * ρV σ - (ρ σ).trace • ρV σ + (ρ σ).det • (1 : Module.End k V) = 0 := by
  obtain ⟨ℓ, A, τ, g, n, hℓ, hS, hA, hτ, hmem⟩ := hdense σ

  have keyρ : ρ σ = ρ g * (ρ τ) ^ n * ρ g⁻¹ := by
    rw [apply_eq_of_mul_inv_mem_ker ρ (Subgroup.mem_inf.mp hmem).1, map_mul, map_mul,
      map_pow]
  have keyρV : ρV σ = ρV g * (ρV τ) ^ n * ρV g⁻¹ := by
    rw [apply_eq_of_mul_inv_mem_ker ρV (Subgroup.mem_inf.mp hmem).2, map_mul, map_mul,
      map_pow]

  have htr : (ρ σ).trace = ((ρ τ) ^ n).trace := by
    rw [keyρ, trace_matrix_conj (apply_inv_mul_apply_cancel ρ g)]
  have hdet : (ρ σ).det = ((ρ τ) ^ n).det := by
    rw [keyρ, det_matrix_conj (apply_mul_apply_inv_cancel ρ g)]

  have hpow : (ρV τ) ^ n * (ρV τ) ^ n - ((ρ τ) ^ n).trace • (ρV τ) ^ n
      + ((ρ τ) ^ n).det • (1 : Module.End k V) = 0 :=
    quadRel_pow (hCH ℓ hℓ hS A hA τ hτ) n

  rw [htr, hdet, keyρV]
  exact quadRel_conj (apply_mul_apply_inv_cancel ρV g) (apply_inv_mul_apply_cancel ρV g) hpow

end DensityStep

end CayleyHamiltonDensity

end

/--
@isnad1 id=eq.2h6v.s13.1c1ed45753bd from=translated src=- shape=d57b21bc vocab=e7f937eb
-/
theorem solution {k : Type*} [CommRing k] {V : Type*} [AddCommGroup V] [Module k V]
    (ρV : Representation k (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) V)
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* Matrix (Fin 2) (Fin 2) k)
    {S : Finset ℕ}
    (hCH : ∀ ℓ : ℕ, ℓ.Prime → ℓ ∉ S →
      ∀ A : ValuationSubring (AlgebraicClosure ℚ), A.LiesOverPrime ℓ →
        ∀ τ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ, A.IsFrobeniusAt τ ℓ →
          ρV τ * ρV τ - (ρ τ).trace • ρV τ + (ρ τ).det • (1 : Module.End k V) = 0)
    (hdense : FrobeniusPowerDense S (ρ.ker ⊓ ρV.ker))
    (σ : AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) :
    ρV σ * ρV σ - (ρ σ).trace • ρV σ + (ρ σ).det • (1 : Module.End k V) = 0 :=
  CayleyHamiltonDensity.cayleyHamilton_of_frobeniusPowerDense_aux ρV ρ hCH hdense σ
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
