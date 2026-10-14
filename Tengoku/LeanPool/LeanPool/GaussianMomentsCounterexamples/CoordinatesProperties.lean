/-
Copyright (c) 2026 long-mathematics. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christopher D. Long
-/
module

public import Tengoku.LeanPool.LeanPool.GaussianMomentsCounterexamples.Coordinates
public import Tengoku

/-! Invertible coordinate substitutions, polynomial degree and explicit formulas. -/

@[expose] public section
noncomputable section
namespace GaussianMomentsCounterexamples
open MvPolynomial
/--
@isnad1 id=eq.0h0v.s8.07596830d59e from=translated src=- shape=87481c11 vocab=8627e8ae
-/
lemma inverseSub3_normalizedSub3 : inverseSub3.comp normalizedSub3 = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [inverseSub3, normalizedSub3, normalizedW] using recombineW (X (0 : Fin 3)) (X 1)
  · simpa [inverseSub3, normalizedSub3, normalizedZ] using recombineZ (X (0 : Fin 3)) (X 1)
  · simp [inverseSub3, normalizedSub3]
/--
@isnad1 id=eq.0h0v.s8.031cc7b34582 from=translated src=- shape=87481c11 vocab=edc97ade
-/
lemma inverseSub4_normalizedSub4 : inverseSub4.comp normalizedSub4 = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [inverseSub4, normalizedSub4, normalizedW] using recombineW (X (0 : Fin 4)) (X 1)
  · simpa [inverseSub4, normalizedSub4, normalizedZ] using recombineZ (X (0 : Fin 4)) (X 1)
  · simpa [inverseSub4, normalizedSub4, normalizedW] using recombineW (X (2 : Fin 4)) (X 3)
  · simpa [inverseSub4, normalizedSub4, normalizedZ] using recombineZ (X (2 : Fin 4)) (X 3)

/--
@isnad1 id=eq.0h0v.s8.6970d68ececf from=translated src=- shape=87481c11 vocab=8627e8ae
-/
lemma normalizedSub3_inverseSub3 : normalizedSub3.comp inverseSub3 = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [inverseSub3, normalizedSub3] using recoverX (0 : Fin 3) 1
  · simpa [inverseSub3, normalizedSub3] using recoverY (0 : Fin 3) 1
  · simp [inverseSub3, normalizedSub3]

/--
@isnad1 id=eq.0h0v.s8.e6d45a6d1ae1 from=translated src=- shape=87481c11 vocab=edc97ade
-/
lemma normalizedSub4_inverseSub4 : normalizedSub4.comp inverseSub4 = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i
  · simpa [inverseSub4, normalizedSub4] using recoverX (0 : Fin 4) 1
  · simpa [inverseSub4, normalizedSub4] using recoverY (0 : Fin 4) 1
  · simpa [inverseSub4, normalizedSub4] using recoverX (2 : Fin 4) 3
  · simpa [inverseSub4, normalizedSub4] using recoverY (2 : Fin 4) 3

/-- The normalized coordinates form an invertible complex polynomial coordinate change. -/
def coordinateEquiv3 : MvPolynomial (Fin 3) ℂ ≃ₐ[ℂ] MvPolynomial (Fin 3) ℂ :=
  AlgEquiv.ofAlgHom normalizedSub3 inverseSub3 normalizedSub3_inverseSub3
    inverseSub3_normalizedSub3

/-- The invertible polynomial coordinate change for two normalized conjugate pairs. -/
def coordinateEquiv4 : MvPolynomial (Fin 4) ℂ ≃ₐ[ℂ] MvPolynomial (Fin 4) ℂ :=
  AlgEquiv.ofAlgHom normalizedSub4 inverseSub4 normalizedSub4_inverseSub4
    inverseSub4_normalizedSub4

/--
@isnad1 id=ne.0h0v.s6.12028d3ef20b from=translated src=- shape=90f4a2ff vocab=033f7349
-/
theorem P3_ne_zero : P3 ≠ 0 := by
  exact coordinateEquiv3.injective.ne (show naturalP3 ≠ 0 from naturalP3_ne_zero)

/--
@isnad1 id=ne.0h0v.s6.81c44d6348c6 from=translated src=- shape=90f4a2ff vocab=81d65f03
-/
theorem P4_ne_zero : P4 ≠ 0 := by
  exact coordinateEquiv4.injective.ne (show naturalP4 ≠ 0 from naturalP4_ne_zero)

/--
@isnad1 id=eq.0h0v.s9.2ed135c3e314 from=translated src=- shape=e9d09363 vocab=9c2f0fa9
-/
theorem P4_formula : P4 = (1 + normalizedZ 2 3) *
    (normalizedW 0 1 * (1 - normalizedZ 0 1) + normalizedW 2 3) := by
  simp [P4, normalizedSub4, naturalP4]

/--
@isnad1 id=eq.0h0v.s10.0225f360505a from=translated src=- shape=5de7e8f5 vocab=2729c07d
-/
theorem P3_expansion : P3 = normalizedW 0 1 + normalizedW 0 1 * normalizedZ 0 1 -
    X 2 ^ 2 - C (3 / 2) * normalizedZ 0 1 * X 2 ^ 2 -
    C (1 / 2) * normalizedZ 0 1 ^ 2 * X 2 ^ 2 := by
  simpa [P3, normalizedSub3] using congrArg normalizedSub3 naturalP3_expansion

/--
@isnad1 id=eq.0h0v.s10.452f54bbd087 from=translated src=- shape=3d03a271 vocab=9c2f0fa9
-/
theorem P4_expansion : P4 = normalizedW 0 1 - normalizedW 0 1 * normalizedZ 0 1 +
    normalizedW 2 3 + normalizedW 0 1 * normalizedZ 2 3 -
    normalizedW 0 1 * normalizedZ 0 1 * normalizedZ 2 3 +
    normalizedW 2 3 * normalizedZ 2 3 := by
  simpa [P4, normalizedSub4] using congrArg normalizedSub4 naturalP4_expansion

/--
@isnad1 id=eq.0h4v.s7.d3ddf45bc77e from=translated src=- shape=b46443b4 vocab=cfab9532
-/
@[simp] theorem eval_normalizedZ {n : ℕ} (i j : Fin n) (x : Fin n → ℂ) :
    eval x (normalizedZ i j) = (x i + Complex.I * x j) / (Real.sqrt 2 : ℂ) := by
  simp [normalizedZ, normalization, div_eq_mul_inv, mul_comm]

/--
@isnad1 id=eq.0h4v.s7.95d74ba89a87 from=translated src=- shape=b46443b4 vocab=79451f15
-/
@[simp] theorem eval_normalizedW {n : ℕ} (i j : Fin n) (x : Fin n → ℂ) :
    eval x (normalizedW i j) = (x i - Complex.I * x j) / (Real.sqrt 2 : ℂ) := by
  simp [normalizedW, normalization, div_eq_mul_inv, mul_comm]

/--
@isnad1 id=eq.0h4v.s7.e0f9aee27e24 from=translated src=- shape=f8f3aecb vocab=d6cdd489
-/
theorem eval_normalizedW_conj {n : ℕ} (i j : Fin n) (x : Fin n → ℝ) :
    eval (fun k => (x k : ℂ)) (normalizedW i j) =
      star (eval (fun k => (x k : ℂ)) (normalizedZ i j)) := by
  simp [sub_eq_add_neg]

/-- Linear substitutions do not increase total degree.
@isnad1 id=le.1h4v.s8.cdc25b267272 from=translated src=- shape=84c4db36 vocab=f044de59
-/
theorem totalDegree_aeval_linear {n k : ℕ}
    (f : Fin n → MvPolynomial (Fin k) ℂ) (hf : ∀ i, (f i).totalDegree ≤ 1)
    (P : MvPolynomial (Fin n) ℂ) : (aeval f P).totalDegree ≤ P.totalDegree := by
  classical
  conv_lhs => rw [P.as_sum, map_sum]
  apply totalDegree_finsetSum_le
  intro d hd
  rw [aeval_monomial, algebraMap_eq]
  apply (totalDegree_mul _ _).trans
  rw [totalDegree_C, zero_add]
  apply le_trans (totalDegree_finsetProd d.support (fun i => f i ^ d i))
  apply le_trans _ (le_totalDegree hd)
  apply Finset.sum_le_sum
  intro i hi
  exact (totalDegree_pow (f i) (d i)).trans (by simpa using Nat.mul_le_mul_left (d i) (hf i))

/--
@isnad1 id=le.0h3v.s4.8964484f682a from=translated src=- shape=dadbe8e5 vocab=dbac8e8f
-/
lemma totalDegree_normalizedZ {n : ℕ} (i j : Fin n) : (normalizedZ i j).totalDegree ≤ 1 := by
  unfold normalizedZ
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_add _ _).trans
  apply max_le
  · simp
  · exact (totalDegree_mul _ _).trans (by simp)

/--
@isnad1 id=le.0h3v.s4.c1db568be927 from=translated src=- shape=dadbe8e5 vocab=76b65796
-/
lemma totalDegree_normalizedW {n : ℕ} (i j : Fin n) : (normalizedW i j).totalDegree ≤ 1 := by
  unfold normalizedW
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  apply (totalDegree_sub _ _).trans
  apply max_le
  · simp
  · exact (totalDegree_mul _ _).trans (by simp)

/--
@isnad1 id=le.0h4v.s7.6e38d46cdd18 from=translated src=- shape=0584ff82 vocab=9f890db9
-/
lemma totalDegree_linear_pair {n : ℕ} (c : ℂ) (i j : Fin n) :
    (C c * (X i + X j) : MvPolynomial (Fin n) ℂ).totalDegree ≤ 1 := by
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact (totalDegree_add _ _).trans (by simp)

/--
@isnad1 id=le.0h4v.s7.ae4c52ebb662 from=translated src=- shape=0584ff82 vocab=4fbfa48c
-/
lemma totalDegree_linear_pair_sub {n : ℕ} (c : ℂ) (i j : Fin n) :
    (C c * (X i - X j) : MvPolynomial (Fin n) ℂ).totalDegree ≤ 1 := by
  apply (totalDegree_mul _ _).trans
  simp only [totalDegree_C, zero_add]
  exact (totalDegree_sub _ _).trans (by simp)

/--
@isnad1 id=eq.0h1v.s8.3a0942249dd7 from=translated src=- shape=6c5c5665 vocab=7687bf3c
-/
theorem totalDegree_normalizedSub3 (P : MvPolynomial (Fin 3) ℂ) :
    (normalizedSub3 P).totalDegree = P.totalDegree := by
  apply Nat.le_antisymm
  · apply totalDegree_aeval_linear
    intro i; fin_cases i <;> simp [totalDegree_normalizedW, totalDegree_normalizedZ]
  · have hinv := totalDegree_aeval_linear
      ![C normalization * (X (0 : Fin 3) + X 1),
        C (Complex.I * normalization) * (X 0 - X 1), X 2]
      (by
        intro i
        fin_cases i
        · exact totalDegree_linear_pair _ _ _
        · exact totalDegree_linear_pair_sub _ _ _
        · exact (totalDegree_X (R := ℂ) (2 : Fin 3)).le)
      (normalizedSub3 P)
    have h := congrArg (fun f : MvPolynomial (Fin 3) ℂ →ₐ[ℂ] MvPolynomial (Fin 3) ℂ => f P)
      inverseSub3_normalizedSub3
    change inverseSub3 (normalizedSub3 P) = P at h
    change (inverseSub3 (normalizedSub3 P)).totalDegree ≤ _ at hinv
    rwa [h] at hinv

/--
@isnad1 id=eq.0h1v.s8.5e8a5fbd0fbf from=translated src=- shape=6c5c5665 vocab=5c31670f
-/
theorem totalDegree_normalizedSub4 (P : MvPolynomial (Fin 4) ℂ) :
    (normalizedSub4 P).totalDegree = P.totalDegree := by
  apply Nat.le_antisymm
  · apply totalDegree_aeval_linear
    intro i; fin_cases i <;> simp [totalDegree_normalizedW, totalDegree_normalizedZ]
  · have hinv := totalDegree_aeval_linear
      ![C normalization * (X (0 : Fin 4) + X 1),
        C (Complex.I * normalization) * (X 0 - X 1),
        C normalization * (X 2 + X 3), C (Complex.I * normalization) * (X 2 - X 3)]
      (by
        intro i
        fin_cases i
        · exact totalDegree_linear_pair _ _ _
        · exact totalDegree_linear_pair_sub _ _ _
        · exact totalDegree_linear_pair _ _ _
        · exact totalDegree_linear_pair_sub _ _ _)
      (normalizedSub4 P)
    have h := congrArg (fun f : MvPolynomial (Fin 4) ℂ →ₐ[ℂ] MvPolynomial (Fin 4) ℂ => f P)
      inverseSub4_normalizedSub4
    change inverseSub4 (normalizedSub4 P) = P at h
    change (inverseSub4 (normalizedSub4 P)).totalDegree ≤ _ at hinv
    rwa [h] at hinv

/--
@isnad1 id=eq.0h0v.s4.b0d424a1bb47 from=translated src=- shape=ca51c511 vocab=17c06ed1
-/
theorem P3_totalDegree : P3.totalDegree = 4 := by
  rw [P3, totalDegree_normalizedSub3, naturalP3_totalDegree]

/--
@isnad1 id=eq.0h0v.s4.cde204b8fa0b from=translated src=- shape=ca51c511 vocab=41e21994
-/
theorem P4_totalDegree : P4.totalDegree = 3 := by
  rw [P4, totalDegree_normalizedSub4, naturalP4_totalDegree]

end GaussianMomentsCounterexamples
