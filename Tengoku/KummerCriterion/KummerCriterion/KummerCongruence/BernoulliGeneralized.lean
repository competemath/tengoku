module

public import Tengoku.Seed.NumberTheory.BernoulliPolynomials
public import Tengoku.KummerCriterion.KummerCriterion.KummerCongruence.Characters
import Tengoku.Seed.CategoryTheory.Category.Init

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Generalized Bernoulli numbers `B_{n, χ}`

Let `N: ℕ` be a positive modulus and `χ: DirichletCharacter R N` a
Dirichlet character valued in a commutative `ℚ`-algebra `R`. The
*generalized Bernoulli numbers* `B_{n, χ} ∈ R` interpolate classical
Bernoulli numbers in the presence of a character twist, and arise as
values of the Dirichlet `L`-function `L(s, χ)` at non-positive integers.

This file defines `BernoulliGen` via the explicit formula

 `B_{n, χ} = N^{n-1} · ∑_{a: ZMod N} χ(a) · B_n(a/N)`

(Diekmann Prop 45, Washington eq. (4.1)).

## Main definitions

- `BernoulliGen χ n` - the generalized Bernoulli number `B_{n, χ}`.

## References

- Diekmann, *FLT for regular primes* (2023), Definition 27 & Prop 45.
- Washington, *Introduction to Cyclotomic Fields*, §4.1.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace KummerCriterion

variable {N : ℕ} {R : Type*} [CommRing R] [Algebra ℚ R]

/-- The generalized Bernoulli number `B_{n, χ}`, defined by the explicit
formula using Bernoulli polynomials over `ℚ` and base change to `R`.-/
noncomputable def BernoulliGen [NeZero N]
    (χ : DirichletCharacter R N) (n : ℕ) : R :=
  (N : R) ^ (n - 1) *
    ∑ a : ZMod N, χ a *
      algebraMap ℚ R ((Polynomial.bernoulli n).eval ((a.val : ℚ) / N))

/-- Intermediate form: for a non-trivial Dirichlet character `χ`,
the `1/2` constant term in `B_1(a/N) = a/N - 1/2` does not contribute
after summing, because `∑ χ(a) = 0`.-/
lemma BernoulliGen_one_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) :
    BernoulliGen χ 1 =
      ∑ a : ZMod N, χ a * algebraMap ℚ R ((a.val : ℚ) / N) := by
  unfold BernoulliGen
  rw [show (1 - 1 : ℕ) = 0 from rfl, pow_zero, one_mul, Polynomial.bernoulli_one]
  simp_rw [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, map_sub, mul_sub]
  rw [Finset.sum_sub_distrib]
  conv_lhs =>
    rw [show (∑ a : ZMod N, χ a * algebraMap ℚ R (2⁻¹ : ℚ))
          = algebraMap ℚ R (2⁻¹ : ℚ) * ∑ a : ZMod N, χ a from by
      rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _]
  rw [MulChar.sum_eq_zero_of_ne_one hχ, mul_zero, sub_zero]

/-- **Diekmann eq. 24/27**, cleared form: `N · B_{1, χ} = ∑_a χ(a) · a`
for non-trivial `χ`. Cleared of denominators so it holds in any commutative
`ℚ`-algebra.-/
lemma natCast_mul_BernoulliGen_one_of_ne_one [IsDomain R] [NeZero N]
    {χ : DirichletCharacter R N} (hχ : χ ≠ 1) :
    (N : R) * BernoulliGen χ 1 =
      ∑ a : ZMod N, χ a * (a.val : R) := by
  rw [BernoulliGen_one_of_ne_one hχ, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  have hN_R : (N : R) = algebraMap ℚ R (N : ℚ) := by push_cast; rfl
  rw [hN_R, show algebraMap ℚ R ((N : ℚ)) * (χ a * algebraMap ℚ R ((a.val : ℚ) / N)) =
        χ a * (algebraMap ℚ R (N : ℚ) * algebraMap ℚ R ((a.val : ℚ) / N)) from by ring,
    ← map_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (NeZero.ne N))]
  push_cast; rfl

/-- The `ℚ_[p]`-valued Teichmüller character, obtained by post-composing
the `ℤ_[p]`-valued Teichmüller character with the natural embedding
`ℤ_[p] -> ℚ_[p]`.-/
noncomputable def teichmullerCharQp (p : ℕ) [Fact p.Prime] : DirichletCharacter ℚ_[p] p :=
  (teichmullerChar p).ringHomComp PadicInt.Coe.ringHom

variable (p : ℕ) [Fact p.Prime]

lemma teichmullerCharQp_pow_eq_ringHomComp (n : ℕ) :
    (teichmullerCharQp p) ^ n =
      ((teichmullerChar p) ^ n).ringHomComp PadicInt.Coe.ringHom := by
  simpa [teichmullerCharQp] using
    (MulChar.ringHomComp_pow (χ := teichmullerChar p) (f := PadicInt.Coe.ringHom) (n := n))

lemma teichmullerCharQp_pow_sub_one_eq_one :
    (teichmullerCharQp p) ^ (p - 1) = 1 := by
  rw [teichmullerCharQp_pow_eq_ringHomComp (p := p) (n := p - 1)]
  simp [teichmullerChar_pow_sub_one_eq_one (p := p)]

lemma orderOf_teichmullerCharQp :
    orderOf (teichmullerCharQp p) = p - 1 := by
  refine Nat.dvd_antisymm
    (orderOf_dvd_of_pow_eq_one (teichmullerCharQp_pow_sub_one_eq_one (p := p))) ?_
  have hpowQ' :
      ((teichmullerChar p) ^ orderOf (teichmullerCharQp p)).ringHomComp
          PadicInt.Coe.ringHom = 1 := by
    rw [← teichmullerCharQp_pow_eq_ringHomComp (p := p) (n := orderOf (teichmullerCharQp p))]
    simp only [pow_orderOf_eq_one]
  have hpowZ : (teichmullerChar p) ^ orderOf (teichmullerCharQp p) = 1 :=
    (MulChar.ringHomComp_eq_one_iff (f := PadicInt.Coe.ringHom)
      (hf := fun _ _ ↦ PadicInt.ext)).mp hpowQ'
  simpa [orderOf_teichmullerChar (p := p)] using orderOf_dvd_of_pow_eq_one hpowZ

/-- Bernoulli numbers below the boundary `p - 1` are `p`-adic integers.
This is stated as equality with the image of some `z : ℤ_[p]` in `ℚ_[p]`.-/
theorem bernoulli_mem_padicInt_of_lt_sub_one {p : ℕ} [hp : Fact p.Prime]
    (hp_odd : p ≠ 2) (k : ℕ) (hk : k < p - 1) :
    ∃ z : ℤ_[p], (bernoulli k : ℚ_[p]) = (z : ℚ_[p]) := by
  have hp : p.Prime := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  revert hk
  induction k using Nat.strong_induction_on with
  | _ k ih =>
  intro hk
  classical
  rcases Nat.eq_zero_or_pos k with rfl | hk_pos
  · exact ⟨1, by simp [_root_.bernoulli_zero]⟩
  have hkp1_lt : k + 1 < p := by omega
  have h_sum := _root_.sum_bernoulli (k + 1)
  rw [ite_eq_right (by omega : k + 1 ≠ 1), Finset.sum_range_succ] at h_sum
  have h_choose_k : (Nat.choose (k + 1) k : ℚ) = (k + 1 : ℚ) := by
    rw [Nat.choose_succ_self_right]; push_cast; rfl
  rw [h_choose_k] at h_sum
  have h_bern_rat : ((k + 1 : ℕ) : ℚ) * _root_.bernoulli k =
      -∑ j ∈ Finset.range k, (Nat.choose (k + 1) j : ℚ) * _root_.bernoulli j := by
    push_cast; linarith [h_sum]
  have hj_wit : ∀ j, j < k -> ∃ z : ℤ_[p], (bernoulli j : ℚ_[p]) = (z : ℚ_[p]) :=
    fun j hj => ih j hj (Nat.lt_of_lt_of_le hj (Nat.le_of_lt hk))
  let z_of : ℕ -> ℤ_[p] := fun j =>
    if h : j < k then (hj_wit j h).choose else 0
  have hz_of : ∀ j, j < k -> (bernoulli j : ℚ_[p]) = ((z_of j : ℤ_[p]) : ℚ_[p]) := by
    intro j hj; simp only [z_of, dite_eq_left hj]; exact (hj_wit j hj).choose_spec
  let S : ℤ_[p] := ∑ j ∈ Finset.range k, (Nat.choose (k + 1) j : ℤ_[p]) * z_of j
  have hS_coe : (S : ℚ_[p]) =
      ∑ j ∈ Finset.range k, (Nat.choose (k + 1) j : ℚ_[p]) * (bernoulli j : ℚ_[p]) := by
    simp only [S, PadicInt.coe_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [PadicInt.coe_mul, PadicInt.coe_natCast, hz_of j (Finset.mem_range.mp hj)]
  have h_kp1_unit : IsUnit ((k + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (by omega) hkp1_lt)
  refine ⟨-(h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val * S, ?_⟩
  have h_bern_Qp : ((k + 1 : ℕ) : ℚ_[p]) * ((_root_.bernoulli k : ℚ) : ℚ_[p]) =
      -∑ j ∈ Finset.range k,
        (Nat.choose (k + 1) j : ℚ_[p]) * ((_root_.bernoulli j : ℚ) : ℚ_[p]) := by
    have h_cast := congrArg (fun q : ℚ => (q : ℚ_[p])) h_bern_rat
    push_cast at h_cast ⊢
    exact h_cast
  rw [← hS_coe] at h_bern_Qp
  have h_coe_unit : ((h_kp1_unit.unit : ℤ_[p]) : ℚ_[p]) = ((k + 1 : ℕ) : ℚ_[p]) := rfl
  have h_unit_mul_inv : ((h_kp1_unit.unit : ℤ_[p]) : ℚ_[p]) *
      ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p]) = 1 := by
    rw [← PadicInt.coe_mul, ← Units.val_mul, mul_inv_cancel]; rfl
  calc (bernoulli k : ℚ_[p])
      = (1 : ℚ_[p]) * (bernoulli k : ℚ_[p]) := by ring
    _ = (((h_kp1_unit.unit : ℤ_[p]) : ℚ_[p]) *
          ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p])) * (bernoulli k : ℚ_[p]) := by
        rw [h_unit_mul_inv]
    _ = ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p]) *
          (((h_kp1_unit.unit : ℤ_[p]) : ℚ_[p]) * (bernoulli k : ℚ_[p])) := by ring
    _ = ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p]) *
          (((k + 1 : ℕ) : ℚ_[p]) * (bernoulli k : ℚ_[p])) := by rw [h_coe_unit]
    _ = ((h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℚ_[p]) * (- (S : ℚ_[p])) := by
        rw [h_bern_Qp]
    _ = ((-(h_kp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val * S : ℤ_[p]) : ℚ_[p]) := by
        rw [PadicInt.coe_mul, PadicInt.coe_neg]; ring

/-- For indices strictly below the boundary `p - 1`, the denominator of the
classical Bernoulli number is prime to `p`.

This is the denominator form of the p-integrality statement used in the proof
of Diekmann Theorem 42: if `n < p - 1`, then `p ∤ (bernoulli n).den`.-/
theorem prime_not_dvd_bernoulli_den_of_lt_sub_one {p n : ℕ} [hp : Fact p.Prime]
    (hp_odd : p ≠ 2) (hn : n < p - 1) :
    ¬ p ∣ (_root_.bernoulli n).den := by
  obtain ⟨z, hz⟩ := bernoulli_mem_padicInt_of_lt_sub_one hp_odd n hn
  have hnorm : ‖((_root_.bernoulli n : ℚ) : ℚ_[p])‖ ≤ 1 := by rw [hz]; exact z.2
  have hunit : IsUnit (((_root_.bernoulli n).den : ℕ) : ℤ_[p]) :=
    PadicInt.isUnit_den _ hnorm
  rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff] at hunit
  exact hp.out.coprime_iff_not_dvd.mp hunit

lemma bernoulli_factor_mul_den (n : ℕ) (hn : n ≠ 0) :
    ((-(1 / 2 : ℚ)) * (((_root_.bernoulli n : ℚ) / n : ℚ))) *
        (2 * (_root_.bernoulli n).den * n : ℚ) =
      -(_root_.bernoulli n).num := by
  calc
    ((-(1 / 2 : ℚ)) * (((_root_.bernoulli n : ℚ) / n : ℚ))) *
        (2 * (_root_.bernoulli n).den * n : ℚ) =
        -((((_root_.bernoulli n : ℚ) / n : ℚ) * ((_root_.bernoulli n).den * n : ℚ))) := by
          ring
    _ = -((_root_.bernoulli n : ℚ) * ((_root_.bernoulli n).den : ℚ)) := by
      have hnQ : (n : ℚ) ≠ 0 := by exact_mod_cast hn
      field_simp [hnQ]
    _ = -(_root_.bernoulli n).num := by
      simp

end KummerCriterion
