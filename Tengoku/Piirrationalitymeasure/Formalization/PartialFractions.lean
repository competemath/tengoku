import Tengoku.Piirrationalitymeasure.Formalization.PolynomialPart
import Tengoku.Seed.Algebra.Polynomial.PartialFractions

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
Partial fractions at the two poles. We first use the monic, coprime linear
factors over `Q` in a denominator-cleared polynomial identity.
-/

namespace PiIrrationality

open Polynomial

theorem two_pole_polynomial_decomposition (F : Polynomial ℚ) (m : ℕ) :
    ∃ (Q : Polynomial ℚ) (a b : Fin m → ℚ),
      F = Q * ((X + C 5) ^ m * (X - C 5) ^ m) +
        (∑ i : Fin m, C (a i) * (X + C 5) ^ i.val * (X - C 5) ^ m) +
        (∑ i : Fin m, C (b i) * (X - C 5) ^ i.val * (X + C 5) ^ m) := by
  let poles : Bool → ℚ := fun b => if b then 5 else -5
  let g : Bool → Polynomial ℚ := fun b => X - C (poles b)
  have hg : ∀ b ∈ (Finset.univ : Finset Bool), (g b).Monic :=
    fun b _ => monic_X_sub_C _
  have hinj : Function.Injective poles := by
    intro b c h
    cases b <;> cases c <;> simp_all [poles] <;> norm_num at h
  have hgg : Set.Pairwise (↑(Finset.univ : Finset Bool))
      (fun b c => IsCoprime (g b) (g c)) := by
    intro b _ c _ hbc
    exact pairwise_coprime_X_sub_C hinj hbc
  obtain ⟨Q, r, hr, hf⟩ :=
    eq_quo_mul_prod_pow_add_sum_rem_mul_prod_pow F hg hgg (fun _ => m)
  have hrC (b : Bool) (i : Fin m) : r b i = C ((r b i).coeff 0) := by
    apply eq_C_of_natDegree_eq_zero
    by_cases hzero : r b i = 0
    · simp [hzero]
    have h := hr b (Finset.mem_univ b) i
    rw [show g b = X - C (poles b) from rfl, degree_X_sub_C] at h
    have h' : (r b i).natDegree < 1 :=
      (natDegree_lt_iff_degree_lt hzero).mpr h
    omega
  refine ⟨Q, fun i => (r false i).coeff 0, fun i => (r true i).coeff 0, ?_⟩
  have hrepl (b : Bool) :
      (∑ i : Fin m, r b i * g b ^ i.val * ∏ k ∈ Finset.univ.erase b, g k ^ m) =
      ∑ i : Fin m, C ((r b i).coeff 0) * g b ^ i.val *
        ∏ k ∈ Finset.univ.erase b, g k ^ m := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun P : Polynomial ℚ => P * g b ^ i.val *
      ∏ k ∈ Finset.univ.erase b, g k ^ m) (hrC b i)
  simp_rw [hrepl] at hf
  simp only [Fintype.prod_bool, Fintype.sum_bool,
    show (Finset.univ : Finset Bool).erase false = {true} by decide,
    show (Finset.univ : Finset Bool).erase true = {false} by decide,
    Finset.prod_singleton] at hf
  simp [g, poles] at hf
  convert hf using 1 <;> ring

theorem two_pole_remainder_natDegree_le
    (m : ℕ) (a b : Fin m → ℚ) :
    ((∑ i : Fin m, C (a i) * (X + C 5) ^ i.val * (X - C 5) ^ m) +
      (∑ i : Fin m, C (b i) * (X - C 5) ^ i.val * (X + C 5) ^ m)).natDegree ≤
      2 * m - 1 := by
  apply natDegree_add_le_of_degree_le
  · apply natDegree_sum_le_of_forall_le
    intro i _
    apply (natDegree_mul_le).trans
    apply (add_le_add natDegree_mul_le le_rfl).trans
    simp only [natDegree_C, natDegree_pow, natDegree_X_add_C, natDegree_X_sub_C,
      mul_one, zero_add]
    omega
  · apply natDegree_sum_le_of_forall_le
    intro i _
    apply (natDegree_mul_le).trans
    apply (add_le_add natDegree_mul_le le_rfl).trans
    simp only [natDegree_C, natDegree_pow, natDegree_X_add_C, natDegree_X_sub_C,
      mul_one, zero_add]
    omega

theorem two_pole_quotient_eq_divByMonic
    (F Q : Polynomial ℚ) (m : ℕ) (hm : 0 < m) (a b : Fin m → ℚ)
    (hF : F = Q * ((X + C 5) ^ m * (X - C 5) ^ m) +
      (∑ i : Fin m, C (a i) * (X + C 5) ^ i.val * (X - C 5) ^ m) +
      (∑ i : Fin m, C (b i) * (X - C 5) ^ i.val * (X + C 5) ^ m)) :
    F /ₘ (X ^ 2 - C 25) ^ m = Q := by
  let S : Polynomial ℚ :=
    (∑ i : Fin m, C (a i) * (X + C 5) ^ i.val * (X - C 5) ^ m) +
      (∑ i : Fin m, C (b i) * (X - C 5) ^ i.val * (X + C 5) ^ m)
  have hmonic : ((X ^ 2 - C 25 : Polynomial ℚ) ^ m).Monic :=
    (monic_X_pow_sub_C 25 (by decide)).pow _
  apply (div_modByMonic_unique Q S hmonic ?_).1
  constructor
  · have hpoles : (X + C 5) * (X - C 5) = (X ^ 2 - C 25 : Polynomial ℚ) := by
      rw [show (X + C 5) * (X - C 5) = (X ^ 2 - (C 5 : Polynomial ℚ) ^ 2) by ring,
        ← C_pow]
      norm_num
    rw [← mul_pow, hpoles] at hF
    dsimp [S]
    linear_combination -hF
  · calc
      S.degree ≤ (2 * m - 1 : ℕ) :=
        degree_le_of_natDegree_le (two_pole_remainder_natDegree_le m a b)
      _ < ((X ^ 2 - C 25 : Polynomial ℚ) ^ m).degree := by
        rw [degree_eq_natDegree hmonic.ne_zero, natDegree_pow,
          natDegree_X_pow_sub_C, Nat.cast_lt]
        omega

def TwoPoleDecomposition (n : ℕ) (a b : Fin (5570 * n + 1) → ℚ) : Prop :=
      ((infinityNumeratorY n).comp (X ^ 2)).map (Int.castRingHom ℚ) =
        (polynomialPart n).map (Int.castRingHom ℚ) *
          ((X + C 5) ^ (5570 * n + 1) * (X - C 5) ^ (5570 * n + 1)) +
        (∑ i : Fin (5570 * n + 1),
          C (a i) * (X + C 5) ^ i.val * (X - C 5) ^ (5570 * n + 1)) +
        (∑ i : Fin (5570 * n + 1),
          C (b i) * (X - C 5) ^ i.val * (X + C 5) ^ (5570 * n + 1))

theorem polynomialPart_two_pole_decomposition (n : ℕ) :
    ∃ a b : Fin (5570 * n + 1) → ℚ, TwoPoleDecomposition n a b := by
  obtain ⟨Q, a, b, h⟩ := two_pole_polynomial_decomposition
    (((infinityNumeratorY n).comp (X ^ 2)).map (Int.castRingHom ℚ)) (5570 * n + 1)
  have hQ := two_pole_quotient_eq_divByMonic _ Q _ (by omega) a b h
  rw [polynomialPart_map_eq_divByMonic] at hQ
  refine ⟨a, b, ?_⟩
  unfold TwoPoleDecomposition
  exact hQ ▸ h

theorem int_square_comp_reflect (P : Polynomial ℤ) :
    ((P.comp (X ^ 2)).map (Int.castRingHom ℚ)).comp (-X) =
      (P.comp (X ^ 2)).map (Int.castRingHom ℚ) := by
  simp only [Polynomial.map_comp, Polynomial.map_pow, Polynomial.map_X,
    comp_assoc, pow_comp, X_comp, neg_sq]

theorem TwoPoleDecomposition.reflect
    (n : ℕ) (a b : Fin (5570 * n + 1) → ℚ) (hF : TwoPoleDecomposition n a b) :
    TwoPoleDecomposition n
      (fun i => (-1 : ℚ) ^ (i.val + (5570 * n + 1)) * b i)
      (fun i => (-1 : ℚ) ^ (i.val + (5570 * n + 1)) * a i) := by
  unfold TwoPoleDecomposition at hF ⊢
  have h := congrArg (fun P : Polynomial ℚ => P.comp (-X)) hF
  rw [int_square_comp_reflect, add_comp, add_comp, mul_comp,
    show ((polynomialPart n).map (Int.castRingHom ℚ)).comp (-X) =
      (polynomialPart n).map (Int.castRingHom ℚ) from int_square_comp_reflect _] at h
  simp only [mul_comp, pow_comp, sum_comp, C_comp, X_comp, add_comp, sub_comp] at h
  have hplus : (-X + C 5 : Polynomial ℚ) = -(X - C 5) := by ring
  have hminus : (-X - C 5 : Polynomial ℚ) = -(X + C 5) := by ring
  rw [hplus, hminus] at h
  have hden : (-(X - C 5) : Polynomial ℚ) ^ (5570 * n + 1) *
      (-(X + C 5)) ^ (5570 * n + 1) =
      (X + C 5) ^ (5570 * n + 1) * (X - C 5) ^ (5570 * n + 1) := by
    rw [← mul_pow, neg_mul_neg, mul_comm, mul_pow]
  rw [hden] at h
  have hterm (u v : Polynomial ℚ) (z : ℚ) (i m : ℕ) :
      C z * (-u) ^ i * (-v) ^ m = C ((-1 : ℚ) ^ (i + m) * z) * u ^ i * v ^ m := by
    rw [neg_pow u i, neg_pow v m]
    simp only [pow_add, map_mul, map_pow, map_neg, map_one]
    ring
  simp_rw [hterm] at h
  linear_combination h

theorem TwoPoleDecomposition.eval {K : Type*} [Field K] [Algebra ℚ K]
    (n : ℕ) (a b : Fin (5570 * n + 1) → ℚ) (hF : TwoPoleDecomposition n a b) (t : K) :
    -(5 * t ^ (2 * 1857 * n) * (t ^ 4 + 6 * t ^ 2 + 25) ^ (3714 * n)) =
      aeval t (polynomialPart n) * ((t + 5) ^ (5570 * n + 1) * (t - 5) ^ (5570 * n + 1)) +
      (∑ i : Fin (5570 * n + 1),
        (a i : K) * (t + 5) ^ i.val * (t - 5) ^ (5570 * n + 1)) +
      (∑ i : Fin (5570 * n + 1),
        (b i : K) * (t - 5) ^ i.val * (t + 5) ^ (5570 * n + 1)) := by
  have h := congrArg (aeval t) hF
  simp only [show Int.castRingHom ℚ = algebraMap ℤ ℚ from Subsingleton.elim _ _,
    map_add, map_mul, map_sum, aeval_map_algebraMap ℚ] at h
  simp only [infinityNumeratorY, aeval_comp, map_mul, map_add, map_sub,
    map_pow, aeval_X, aeval_C, map_neg, map_ofNat, ← pow_mul] at h
  have hmap (q : ℚ) : (algebraMap ℚ K) q = (q : K) := map_ratCast _ q
  simp_rw [hmap] at h
  convert h using 1 <;> ring

end PiIrrationality
