import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ArtinL_EulerFactor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ArtinL_hasProd_inv_eval_eulerFactor_of_lSeriesSummable.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ArtinL_hasProd_inv_eval_eulerFactor_of_lSeriesSummable

set_option autoImplicit false

noncomputable section

open Polynomial
open scoped MatrixGroups

namespace ArtinEulerRhoProof

/--
@isnad1 id=eq.2h2v.s8.30e460303f52 from=translated src=- shape=243f6e59 vocab=7ca03062
-/
theorem tsum_coeff_inv_mul_eval (E : ℂ[X]) (hE : E.coeff 0 = 1) (x : ℂ)
    (hsum : Summable fun k : ℕ => ‖PowerSeries.coeff k ((E : PowerSeries ℂ)⁻¹) * x ^ k‖) :
    (∑' k : ℕ, PowerSeries.coeff k ((E : PowerSeries ℂ)⁻¹) * x ^ k) * E.eval x = 1 := by
  set c : ℕ → ℂ := fun k => PowerSeries.coeff k ((E : PowerSeries ℂ)⁻¹) * x ^ k with hc
  set a : ℕ → ℂ := fun j => E.coeff j * x ^ j with ha
  have hE0 : PowerSeries.constantCoeff (E : PowerSeries ℂ) ≠ 0 := by
    rw [Polynomial.constantCoeff_coe, hE]
    exact one_ne_zero
  have ha_zero : ∀ j ∉ Finset.range (E.natDegree + 1), a j = 0 := by
    intro j hj
    rw [Finset.mem_range, not_lt] at hj
    rw [ha]
    dsimp only
    rw [Polynomial.coeff_eq_zero_of_natDegree_lt (Nat.lt_of_succ_le hj), zero_mul]
  have ha_sum : Summable fun j => ‖a j‖ := by
    refine summable_of_ne_finset_zero (s := Finset.range (E.natDegree + 1)) fun j hj => ?_
    rw [ha_zero j hj, norm_zero]
  have heval : E.eval x = ∑' j, a j := by
    rw [tsum_eq_sum ha_zero, Polynomial.eval_eq_sum_range]
  rw [heval, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hsum ha_sum]
  have hinner : ∀ m : ℕ, ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal m, c kl.1 * a kl.2 =
      if m = 0 then 1 else 0 := by
    intro m
    have h1 : ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal m, c kl.1 * a kl.2 =
        (∑ kl ∈ Finset.HasAntidiagonal.antidiagonal m, PowerSeries.coeff kl.1 ((E : PowerSeries ℂ)⁻¹) *
          PowerSeries.coeff kl.2 (E : PowerSeries ℂ)) * x ^ m := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun kl hkl => ?_
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
      rw [hc, ha]
      dsimp only
      rw [Polynomial.coeff_coe, ← hkl, pow_add]
      ring
    rw [h1, ← PowerSeries.coeff_mul, PowerSeries.inv_mul_cancel _ hE0, PowerSeries.coeff_one]
    split_ifs with hm
    · rw [hm, pow_zero, one_mul]
    · rw [zero_mul]
  rw [tsum_congr hinner]
  exact tsum_ite_eq 0 1

/--
@isnad1 id=ne.2h2v.s7.b154d54dc685 from=translated src=- shape=1ded7449 vocab=3f551545
-/
theorem eval_ne_zero_of_summable (E : ℂ[X]) (hE : E.coeff 0 = 1) (x : ℂ)
    (hsum : Summable fun k : ℕ => ‖PowerSeries.coeff k ((E : PowerSeries ℂ)⁻¹) * x ^ k‖) :
    E.eval x ≠ 0 := by
  intro h
  have := tsum_coeff_inv_mul_eval E hE x hsum
  rw [h, mul_zero] at this
  exact zero_ne_one this

/--
@isnad1 id=hassum.2h2v.s8.9486a9d2310d from=translated src=- shape=17b6f7f6 vocab=27353105
-/
theorem hasSum_coeff_inv (E : ℂ[X]) (hE : E.coeff 0 = 1) (x : ℂ)
    (hsum : Summable fun k : ℕ => ‖PowerSeries.coeff k ((E : PowerSeries ℂ)⁻¹) * x ^ k‖) :
    HasSum (fun k : ℕ => PowerSeries.coeff k ((E : PowerSeries ℂ)⁻¹) * x ^ k) (E.eval x)⁻¹ := by
  have h := tsum_coeff_inv_mul_eval E hE x hsum
  have hne := eval_ne_zero_of_summable E hE x hsum
  have heq : ∑' k : ℕ, PowerSeries.coeff k ((E : PowerSeries ℂ)⁻¹) * x ^ k = (E.eval x)⁻¹ :=
    eq_inv_of_mul_eq_one_left h
  rw [← heq]
  exact hsum.of_norm.hasSum

variable {n : ℕ}

local notation "Γℚ" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

/--
@isnad1 id=eq.0h3v.s8.a272549f32b8 from=translated src=- shape=ba1a2ddf vocab=0d4bf0a3
-/
theorem coeffPrimePow_zero (ρ : Γℚ →* GL (Fin n) ℂ) (p : ℕ) : ArtinL.coeffPrimePow ρ p 0 = 1 := by
  unfold ArtinL.coeffPrimePow
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, PowerSeries.constantCoeff_inv,
    Polynomial.constantCoeff_coe, ArtinL.coeff_eulerFactor_zero, inv_one]

/--
@isnad1 id=eq.1h4v.s8.c96f8708b7f8 from=translated src=- shape=bb126597 vocab=3182ddf5
-/
theorem coeff_prime_pow (ρ : Γℚ →* GL (Fin n) ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    ArtinL.coeff ρ (p ^ k) = ArtinL.coeffPrimePow ρ p k := by
  unfold ArtinL.coeff
  rw [ite_eq_right (pow_ne_zero k hp.ne_zero), Nat.Prime.factorization_pow hp,
    Finsupp.prod_single_index (coeffPrimePow_zero ρ p)]

/--
@isnad1 id=eq.1h4v.s8.419adfd4f0d5 from=translated src=- shape=c6e51ed9 vocab=d9ec481e
-/
theorem coeff_mul_of_coprime (ρ : Γℚ →* GL (Fin n) ℂ) {a b : ℕ} (hab : Nat.Coprime a b) :
    ArtinL.coeff ρ (a * b) = ArtinL.coeff ρ a * ArtinL.coeff ρ b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [zero_mul, ArtinL.coeff_zero, zero_mul]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [mul_zero, ArtinL.coeff_zero, mul_zero]
  unfold ArtinL.coeff
  rw [ite_eq_right (Nat.mul_ne_zero ha.ne' hb.ne'), ite_eq_right ha.ne', ite_eq_right hb.ne',
    Nat.factorization_mul ha.ne' hb.ne', Finsupp.prod_add_index_of_disjoint]
  rw [Nat.support_factorization, Nat.support_factorization]
  exact hab.disjoint_primeFactors

/--
@isnad1 id=eq.0h3v.s5.e8bf77b47813 from=translated src=- shape=ab709254 vocab=cb498106
-/
theorem natCast_pow_cpow (m e : ℕ) (z : ℂ) : (((m ^ e : ℕ)) : ℂ) ^ z = ((m : ℂ) ^ z) ^ e := by
  induction e with
  | zero => rw [pow_zero, pow_zero, Nat.cast_one, Complex.one_cpow]
  | succ e ih => rw [pow_succ, Nat.cast_mul, Complex.natCast_mul_natCast_cpow, ih, pow_succ]

/--
@isnad1 id=eq.1h5v.s8.082520380f3a from=translated src=- shape=48ab5fea vocab=089991c8
-/
theorem term_mul_of_coprime (ρ : Γℚ →* GL (Fin n) ℂ) (s : ℂ) {a b : ℕ} (hab : Nat.Coprime a b) :
    LSeries.term (ArtinL.coeff ρ) s (a * b) =
      LSeries.term (ArtinL.coeff ρ) s a * LSeries.term (ArtinL.coeff ρ) s b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · rw [zero_mul, LSeries.term_zero, zero_mul]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · rw [mul_zero, LSeries.term_zero, mul_zero]
  rw [LSeries.term_of_ne_zero (Nat.mul_ne_zero ha.ne' hb.ne'), LSeries.term_of_ne_zero ha.ne',
    LSeries.term_of_ne_zero hb.ne', coeff_mul_of_coprime ρ hab, Nat.cast_mul,
    Complex.natCast_mul_natCast_cpow, mul_div_mul_comm]

/--
@isnad1 id=eq.0h3v.s8.7b95a030e986 from=translated src=- shape=d91ee18d vocab=dd8b6c3d
-/
theorem term_one (ρ : Γℚ →* GL (Fin n) ℂ) (s : ℂ) : LSeries.term (ArtinL.coeff ρ) s 1 = 1 := by
  rw [LSeries.term_of_ne_zero one_ne_zero, ArtinL.coeff_one, Nat.cast_one, Complex.one_cpow,
    div_one]

/--
@isnad1 id=eq.1h5v.s8.2048140e1053 from=translated src=- shape=6ae15649 vocab=e6a68385
-/
theorem term_prime_pow (ρ : Γℚ →* GL (Fin n) ℂ) (s : ℂ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    LSeries.term (ArtinL.coeff ρ) s (p ^ k) =
      ArtinL.coeffPrimePow ρ p k * ((p : ℂ) ^ (-s)) ^ k := by
  rw [LSeries.term_of_ne_zero (pow_ne_zero k hp.ne_zero), coeff_prime_pow ρ hp, div_eq_mul_inv,
    ← Complex.cpow_neg, natCast_pow_cpow]

/--
@isnad1 id=summable.2h4v.s9.46e650b03249 from=translated src=- shape=4e1a8393 vocab=6c6e5c17
-/
theorem summable_norm_coeffPrimePow (ρ : Γℚ →* GL (Fin n) ℂ) {s : ℂ}
    (hsum : LSeriesSummable (ArtinL.coeff ρ) s) {p : ℕ} (hp : p.Prime) :
    Summable fun k : ℕ =>
      ‖PowerSeries.coeff k ((ArtinL.eulerFactor ρ p : PowerSeries ℂ)⁻¹) * ((p : ℂ) ^ (-s)) ^ k‖ := by
  have h := hsum.norm.comp_injective (Nat.pow_right_injective hp.two_le)
  refine h.congr fun k => ?_
  show ‖LSeries.term (ArtinL.coeff ρ) s (p ^ k)‖ = _
  rw [term_prime_pow ρ s hp]
  rfl

/--
@isnad1 id=and.2h4v.s9.4aa1606a3736 from=translated src=- shape=b35139d2 vocab=da6dbbe9
-/
theorem local_part (ρ : Γℚ →* GL (Fin n) ℂ) {s : ℂ} (hsum : LSeriesSummable (ArtinL.coeff ρ) s)
    {p : ℕ} (hp : p.Prime) :
    HasSum (fun e : ℕ => ArtinL.coeffPrimePow ρ p e * ((p : ℂ) ^ (-s)) ^ e)
        ((ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)))⁻¹ ∧
      (ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)) ≠ 0 :=
  ⟨hasSum_coeff_inv _ (ArtinL.coeff_eulerFactor_zero ρ p) _ (summable_norm_coeffPrimePow ρ hsum hp),
    eval_ne_zero_of_summable _ (ArtinL.coeff_eulerFactor_zero ρ p) _
      (summable_norm_coeffPrimePow ρ hsum hp)⟩

/--
@isnad1 id=hasprod.1h3v.s8.1ba9775c5c0f from=translated src=- shape=fa74182e vocab=90bcccf5
-/
theorem global_part (ρ : Γℚ →* GL (Fin n) ℂ) {s : ℂ} (hsum : LSeriesSummable (ArtinL.coeff ρ) s) :
    HasProd (fun p : Nat.Primes => ((ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)))⁻¹)
      (ArtinL.LSeries ρ s) := by
  have h := EulerProduct.eulerProduct_hasProd (f := LSeries.term (ArtinL.coeff ρ) s)
    (term_one ρ s) (fun hmn => term_mul_of_coprime ρ s hmn) hsum.norm (LSeries.term_zero _ _)
  have hfun : (fun p : Nat.Primes => ∑' e : ℕ, LSeries.term (ArtinL.coeff ρ) s (p ^ e)) =
      fun p : Nat.Primes => ((ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)))⁻¹ := by
    funext p
    simp_rw [term_prime_pow ρ s p.2]
    exact (local_part ρ hsum p.2).1.tsum_eq
  rw [hfun] at h
  exact h

end ArtinEulerRhoProof

/--
@isnad1 id=and.1h3v.s9.9936cf95a8e1 from=translated src=- shape=8dfec03b vocab=ec8c273f
-/
theorem solution {n : ℕ}
    (ρ : (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ) →* GL (Fin n) ℂ)
    {s : ℂ} (hsum : LSeriesSummable (ArtinL.coeff ρ) s) :
    (∀ p : ℕ, p.Prime →
      HasSum (fun e : ℕ => ArtinL.coeffPrimePow ρ p e * ((p : ℂ) ^ (-s)) ^ e)
          ((ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)))⁻¹ ∧
        (ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)) ≠ 0) ∧
    HasProd (fun p : Nat.Primes => ((ArtinL.eulerFactor ρ p).eval ((p : ℂ) ^ (-s)))⁻¹)
      (ArtinL.LSeries ρ s) :=
  ⟨fun _ hp => ArtinEulerRhoProof.local_part ρ hsum hp, ArtinEulerRhoProof.global_part ρ hsum⟩

end
