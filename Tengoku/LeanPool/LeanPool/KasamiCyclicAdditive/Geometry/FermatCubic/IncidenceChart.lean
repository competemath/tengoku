/-
Copyright (c) 2026 D.S. McNeil, Gábor P. Nagy, Attila Vajda. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: D.S. McNeil, Gábor P. Nagy, Attila Vajda
-/
module

public import Tengoku.LeanPool.LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.Infinity
import Tengoku.LeanPool.LeanPool.KasamiCyclicAdditive.Geometry.FermatCubic.Frobenius
public import Tengoku

/-!
# Validity of the affine Fermat-incidence chart

This file formalises and verifies the affine Fermat-incidence chart.  Throughout, `K` is a field of
characteristic two (algebraic closedness is nowhere needed), `E` is the Fermat cubic
`X^3+Y^3=Z^3` with origin `O=[1:1:0]`, realised through the Weierstrass model `fer`
(see `FermatCubic.Curve`), `pi` is the Frobenius `x ↦ x^2` and `t3 = (1,0)`.

* `hessD`, `hessX`, `hessY` are the chart denominator and its two numerators;
* `phi` is the map `Q ↦ -(Q + pi^k Q) + t3`;
* `hessDenom_ne_zero` : the Hessian denominator is nonzero;
* `hessCoords_ne_zero` : both affine coordinates are nonzero;
* `exists_twisted_root_equation` produces the twisted root equation.

The Frobenius-twist hypothesis is stated as `pi^n Q = Q + C` with `C = ptInf c` a point at infinity;
the three points at infinity are the three points of `K0 = ker (1+pi)`, cf. `neg_ptInf`.
-/

@[expose] public section

namespace KasamiCyclicAdditive.FermatCubic

open WeierstrassCurve

variable {K : Type*} [Field K] [CharP K 2]

omit [CharP K 2] in
/-- `(1,0)` satisfies the Fermat equation. -/
private lemma t3_fermat : (1 : K) ^ 3 + (0 : K) ^ 3 = 1 := by norm_num

/-- The Frobenius `pi^k` preserves the Fermat equation.
@isnad1 id=eq.1h4v.s8.16bf6392ca1b from=translated src=- shape=4fec828f vocab=3729ae20
-/
lemma frob_fermat {W T : K} (h : W ^ 3 + T ^ 3 = 1) (k : ℕ) :
    (W ^ 2 ^ k) ^ 3 + (T ^ 2 ^ k) ^ 3 = 1 := by
  have : ExpChar K 2 := ExpChar.prime Nat.prime_two
  have := congrArg (fun z : K => z ^ 2 ^ k) h
  simpa [add_pow_char_pow, ← pow_mul, Nat.mul_comm] using this

omit [CharP K 2] in
/-- Cubing commutes with the `2^k`-power Frobenius. -/
private lemma pow_pow_comm (x : K) (k : ℕ) : (x ^ 3) ^ 2 ^ k = (x ^ 2 ^ k) ^ 3 := by
  rw [← pow_mul, ← pow_mul, Nat.mul_comm]

/-! ### The algebra of the Hessian numerators -/

section Algebra

variable {W T A B : K}

/-- With a vanishing Hessian denominator, `N_x * A = N_y * T`.  With `A` and `T`
nonzero this makes the two numerators vanish simultaneously.
@isnad1 id=eq.1h5v.s6.bc32e948bfe9 from=translated src=- shape=2fe47e14 vocab=61e98e21
-/
lemma hess_key (hD : hessD W T A B = 0) : hessX W T A B * A = hessY W T A B * T := by
  simp only [hessX, hessY, hessD] at *
  linear_combination (W * B) * hD + (-(W ^ 2 * B * T)) * CharTwo.two_eq_zero (R := K)

/-- `N_x = 0` and `D0 = 0` force `A^3 = W^3`.
@isnad1 id=eq.3h5v.s7.5aae809d5cb7 from=translated src=- shape=77fd5df6 vocab=4bf51c23
-/
lemma hess_cube_left (hT : T ≠ 0) (hX : hessX W T A B = 0) (hD : hessD W T A B = 0) :
    A ^ 3 = W ^ 3 := by
  simp only [hessX, hessD] at *
  have hstep : T ^ 2 * A ^ 3 = T ^ 2 * W ^ 3 := by
    linear_combination (A ^ 2) * hX + (-(W * (A * B - W * T))) * hD
      + (-(W ^ 3 * T ^ 2)) * CharTwo.two_eq_zero (R := K)
  exact mul_left_cancel₀ (pow_ne_zero 2 hT) hstep

/-- `N_y = 0` and `D0 = 0` force `B^3 = T^3`.
@isnad1 id=eq.3h5v.s7.3241ed109756 from=translated src=- shape=65999f08 vocab=308b6da3
-/
lemma hess_cube_right (hW : W ≠ 0) (hY : hessY W T A B = 0) (hD : hessD W T A B = 0) :
    B ^ 3 = T ^ 3 := by
  simp only [hessY, hessD] at *
  have hstep : W ^ 2 * B ^ 3 = W ^ 2 * T ^ 3 := by
    linear_combination (B ^ 2) * hY + (-(T * (A * B - W * T))) * hD
      + (-(T ^ 3 * W ^ 2)) * CharTwo.two_eq_zero (R := K)
  exact mul_left_cancel₀ (pow_ne_zero 2 hW) hstep

end Algebra

section Group

variable [DecidableEq K]

/-- The `3`-torsion point `t3 = (1,0)`. -/
def t3 (K : Type*) [Field K] [CharP K 2] : (fer K).toAffine.Point :=
  pt 1 0 (by exact t3_fermat)

/-- `t3 = (1,0)` is `3`-torsion.
@isnad1 id=eq.0h1v.s7.ff25fa54dc9a from=translated src=- shape=9545b154 vocab=67d82c7b
-/
lemma three_torsion_t3 : (3 : ℕ) • t3 K = 0 :=
  (three_torsion_pt_iff t3_fermat).mpr (Or.inr rfl)

/-- The chart computation behind the twisted root equation: if `(x/d, y/d)` is an affine Fermat
point with all of `x, y, d` nonzero, then `-(x/d, y/d) + t3 = (x/y, d/y)`.
@isnad1 id=eq.5h4v.s8.9ab7c1ba6622 from=translated src=- shape=78bc7715 vocab=064c4a57
-/
lemma neg_add_t3 {x y d : K} (hx : x ≠ 0) (hy : y ≠ 0) (hd : d ≠ 0)
    (h1 : (x / d) ^ 3 + (y / d) ^ 3 = 1) (h2 : (x / y) ^ 3 + (d / y) ^ 3 = 1) :
    -(pt (x / d) (y / d) h1) + t3 K = pt (x / y) (d / y) h2 := by
  have hD2 : hessD (y / d) (x / d) 1 0 ≠ 0 := by
    simp only [hessD, mul_zero, add_zero]
    exact mul_ne_zero (div_ne_zero hy hd) (div_ne_zero hx hd)
  rw [neg_pt, t3, add_pt _ t3_fermat hD2]
  refine pt_congr _ _ ?_ ?_ <;>
    simp only [hessX, hessY, hessD, one_pow, mul_one, mul_zero, zero_pow, zero_mul,
      add_zero, zero_add, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true] <;>
    field_simp

/-- `phi k Q = -(Q + pi^k Q) + t3`. -/
def phi (k : ℕ) (W T : K) (h : W ^ 3 + T ^ 3 = 1) : (fer K).toAffine.Point :=
  -(pt W T h + pt (W ^ 2 ^ k) (T ^ 2 ^ k) (frob_fermat h k)) + t3 K

/-- If `Q + pi^k Q` is `3`-torsion then so is `Phi_k(Q)`.
@isnad1 id=eq.2h4v.s9.e2917878774f from=translated src=- shape=6e0490cf vocab=9d8cbbda
-/
lemma three_torsion_phi {k : ℕ} {W T : K} (h : W ^ 3 + T ^ 3 = 1)
    (hsum : (3 : ℕ) • (pt W T h + pt (W ^ 2 ^ k) (T ^ 2 ^ k) (frob_fermat h k)) = 0) :
    (3 : ℕ) • phi k W T h = 0 := by
  rw [phi, smul_add, smul_neg, hsum, three_torsion_t3, neg_zero, add_zero]

omit [DecidableEq K] in
/-- With a vanishing Hessian denominator the two numerators vanish together, so
if they do not both vanish then neither does.
@isnad1 id=and.4h5v.s7.9ef47e57e298 from=translated src=- shape=6c98f47f vocab=37a58eb9
-/
lemma hessNum_ne_zero_of_hessD_eq_zero {W T A B : K} (hT : T ≠ 0) (hA : A ≠ 0)
    (hD : hessD W T A B = 0) (hN : ¬(hessX W T A B = 0 ∧ hessY W T A B = 0)) :
    hessX W T A B ≠ 0 ∧ hessY W T A B ≠ 0 := by
  have hkey := hess_key hD
  constructor
  · intro h0
    refine hN ⟨h0, ?_⟩
    rw [h0, zero_mul] at hkey
    exact (mul_eq_zero.mp hkey.symm).resolve_right hT
  · intro h0
    refine hN ⟨?_, h0⟩
    rw [h0, zero_mul] at hkey
    exact (mul_eq_zero.mp hkey).resolve_right hA

omit [DecidableEq K] in
/-- With a vanishing Hessian denominator, `A = T` says that the second point is the
negative of the first. -/
lemma eq_neg_of_hessD_eq_zero {W T A B : K} (h : W ^ 3 + T ^ 3 = 1) (h2 : A ^ 3 + B ^ 3 = 1)
    (hT : T ≠ 0) (hD : hessD W T A B = 0) (hAT : A = T) :
    pt A B h2 = -(pt W T h) := by
  have hprod : W * T + A * B = 0 := hD
  have hB : B = W := by
    rw [hAT] at hprod
    have h0 : T * (B + W) = 0 := by linear_combination hprod
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd h1 hT
    · linear_combination h1 - CharTwo.add_self_eq_zero W
  rw [neg_pt]
  exact pt_congr _ _ hAT hB

omit [DecidableEq K] in
/-- Two points with a vanishing Hessian denominator that are not negatives of one
another have distinct coordinate sums, so the secant denominator does not vanish.
@isnad1 id=ne.3h5v.s6.e4461a4b5a13 from=translated src=- shape=c9110afc vocab=940a5036
-/
lemma add_ne_add_of_hessD_eq_zero {W T A B : K} (hD : hessD W T A B = 0)
    (hXne : hessX W T A B ≠ 0) (hAT : A ≠ T) :
    W + T ≠ A + B := by
  have hprod : W * T + A * B = 0 := hD
  intro hsum
  have hfac : (A + W) * (A + T) = 0 := by
    linear_combination A * hsum + hprod + (A ^ 2) * CharTwo.two_eq_zero (R := K)
  rcases mul_eq_zero.mp hfac with h0 | h0
  · -- `(A,B) = (W,T)`, so both numerators vanish
    have hAW : A = W := by linear_combination h0 - CharTwo.add_self_eq_zero W
    have hBT : B = T := by
      linear_combination -hsum - hAW
    apply hXne
    simp only [hessX, hAW, hBT]
    linear_combination (T ^ 2 * W) * CharTwo.two_eq_zero (R := K)
  · exact hAT (by linear_combination h0 - CharTwo.add_self_eq_zero T)

/-- If the Hessian denominator of two affine Fermat points vanishes while the
numerators do not both vanish, then their sum lies in `E[3]`: it is a point at
infinity `[N_x : N_y : 0]`.
@isnad1 id=eq.6h5v.s9.90e1722e899f from=translated src=- shape=cf5bf54a vocab=93cc1172
-/
theorem three_torsion_add_of_hessD_eq_zero {W T A B : K}
    (h : W ^ 3 + T ^ 3 = 1) (h2 : A ^ 3 + B ^ 3 = 1)
    (hT : T ≠ 0) (hA : A ≠ 0) (hD : hessD W T A B = 0)
    (hN : ¬(hessX W T A B = 0 ∧ hessY W T A B = 0)) :
    (3 : ℕ) • (pt W T h + pt A B h2) = 0 := by
  obtain ⟨hXne, hYne⟩ := hessNum_ne_zero_of_hessD_eq_zero hT hA hD hN
  by_cases hAT : A = T
  · rw [eq_neg_of_hessD_eq_zero h h2 hT hD hAT, add_neg_cancel, smul_zero]
  · have hkey := hess_key hD
    have hS : hessX W T A B + hessY W T A B ≠ 0 := by
      intro h0
      apply hAT
      have heq : hessY W T A B = hessX W T A B := by
        linear_combination h0 - CharTwo.add_self_eq_zero (hessX W T A B)
      rw [heq] at hkey
      exact mul_left_cancel₀ hXne hkey
    have hdd := add_ne_add_of_hessD_eq_zero hD hXne hAT
    have hx := x_ne_of_den_ne (K := K) hdd
    rw [pt, pt, Affine.Point.add_of_X_ne hx, three_torsion_some_iff,
      add_pt_x_eq_zero h h2 hdd hD hS]
    ring

variable {W T : K} {k n : ℕ}

omit [DecidableEq K] in
/-- The Hessian denominator and both numerators cannot vanish together: under the
Frobenius-twist relation with `gcd (k, n) = 1`, that would force `W` or `T` to be
zero.
@isnad1 id=false.8h5v.s9.29f267447614 from=translated src=- shape=fd62817a vocab=bde71b72
-/
theorem not_hess_all_eq_zero (h : W ^ 3 + T ^ 3 = 1) (hW : W ≠ 0) (hT : T ≠ 0)
    (hkn : Nat.gcd k n = 1)
    (hX : hessX W T (W ^ 2 ^ k) (T ^ 2 ^ k) = 0)
    (hY : hessY W T (W ^ 2 ^ k) (T ^ 2 ^ k) = 0)
    (hD : hessD W T (W ^ 2 ^ k) (T ^ 2 ^ k) = 0)
    (hn : ∃ c : K, c ^ 3 = 1 ∧ W ^ 2 ^ n = c * W ∧ T ^ 2 ^ n = c ^ 2 * T) :
    False := by
  -- the `k`-th Frobenius fixes `W^3` and `T^3`
  have hWk : (W ^ 3) ^ 2 ^ k = W ^ 3 := by
    rw [pow_pow_comm]; exact hess_cube_left hT hX hD
  have hTk : (T ^ 3) ^ 2 ^ k = T ^ 3 := by
    rw [pow_pow_comm]; exact hess_cube_right hW hY hD
  -- the `n`-th Frobenius fixes `W^3` and `T^3`
  obtain ⟨c, hc, hcW, hcT⟩ := hn
  have hWn : (W ^ 3) ^ 2 ^ n = W ^ 3 := by
    rw [pow_pow_comm, hcW]
    linear_combination (W ^ 3) * hc
  have hTn : (T ^ 3) ^ 2 ^ n = T ^ 3 := by
    rw [pow_pow_comm, hcT]
    linear_combination (T ^ 3 * (c ^ 3 + 1)) * hc
  -- `W^3, T^3 ∈ F_2`, and `W^3 + T^3 = 1` then forces `W = 0` or `T = 0`
  rcases eq_zero_or_one_of_frobenius_fixed hkn hWk hWn with hw3 | hw3
  · exact hW (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp hw3)
  · rcases eq_zero_or_one_of_frobenius_fixed hkn hTk hTn with ht3 | ht3
    · exact hT (pow_eq_zero_iff (n := 3) (by norm_num) |>.mp ht3)
    · rw [hw3, ht3] at h
      exact one_ne_zero (by linear_combination -h + CharTwo.two_eq_zero (R := K) : (1 : K) = 0)

/-- For an affine Fermat point with both coordinates nonzero, `gcd (k, n) = 1`,
the Frobenius-twist relation `hB3`, and `Phi_k(Q)` not `3`-torsion, the Hessian
denominator `D0` is nonzero.
@isnad1 id=ne.6h5v.s9.2ed2bdd53859 from=translated src=- shape=588ba7d3 vocab=4ec75e88
-/
theorem hessDenom_ne_zero (h : W ^ 3 + T ^ 3 = 1) (hW : W ≠ 0) (hT : T ≠ 0) (hkn : Nat.gcd k n = 1)
    (hB3 : ∃ (c : K) (hc : c ^ 3 = 1),
      pt (W ^ 2 ^ n) (T ^ 2 ^ n) (frob_fermat h n) = pt W T h + ptInf c hc)
    (hB5 : (3 : ℕ) • phi k W T h ≠ 0) :
    hessD W T (W ^ 2 ^ k) (T ^ 2 ^ k) ≠ 0 := by
  intro hD
  by_cases hN : hessX W T (W ^ 2 ^ k) (T ^ 2 ^ k) = 0 ∧ hessY W T (W ^ 2 ^ k) (T ^ 2 ^ k) = 0
  · obtain ⟨c, hc, heq⟩ := hB3
    rw [add_ptInf] at heq
    obtain ⟨hcW, hcT⟩ := pt_inj heq
    exact not_hess_all_eq_zero h hW hT hkn hN.1 hN.2 hD ⟨c, hc, hcW, hcT⟩
  · exact hB5 (three_torsion_phi h
      (three_torsion_add_of_hessD_eq_zero h (frob_fermat h k) hT (pow_ne_zero _ hW) hD hN))

/-- Both affine coordinates of `Q + pi^k Q` are nonzero.
@isnad1 id=and.6h5v.s9.69203ee57340 from=translated src=- shape=9f2fd363 vocab=1a047105
-/
theorem hessCoords_ne_zero (h : W ^ 3 + T ^ 3 = 1) (hW : W ≠ 0) (hT : T ≠ 0) (hkn : Nat.gcd k n = 1)
    (hB3 : ∃ (c : K) (hc : c ^ 3 = 1),
      pt (W ^ 2 ^ n) (T ^ 2 ^ n) (frob_fermat h n) = pt W T h + ptInf c hc)
    (hB5 : (3 : ℕ) • phi k W T h ≠ 0) :
    hessX W T (W ^ 2 ^ k) (T ^ 2 ^ k) ≠ 0 ∧ hessY W T (W ^ 2 ^ k) (T ^ 2 ^ k) ≠ 0 := by
  have hD := hessDenom_ne_zero h hW hT hkn hB3 hB5
  have hsum := add_pt h (frob_fermat h k) hD
  constructor
  · intro h0
    refine hB5 (three_torsion_phi h ?_)
    rw [hsum, three_torsion_pt_iff]
    exact Or.inl (by rw [h0, zero_div])
  · intro h0
    refine hB5 (three_torsion_phi h ?_)
    rw [hsum, three_torsion_pt_iff]
    exact Or.inr (by rw [h0, zero_div])

omit [DecidableEq K] in
/-- The Hessian coordinates, weighted by `W^(2^k+1)` and `T^(2^k+1)`, recombine to
the denominator.
@isnad1 id=eq.1h4v.s9.b9f5fb5b74ce from=translated src=- shape=0bd61ae3 vocab=152a4dc6
-/
theorem hess_weighted_sum_eq_hessD (h : W ^ 3 + T ^ 3 = 1) :
    W ^ (2 ^ k + 1) * hessY W T (W ^ 2 ^ k) (T ^ 2 ^ k)
      + hessX W T (W ^ 2 ^ k) (T ^ 2 ^ k) * T ^ (2 ^ k + 1)
      = hessD W T (W ^ 2 ^ k) (T ^ 2 ^ k) := by
  have h2 := frob_fermat h k
  simp only [hessX, hessY, hessD, pow_succ]
  linear_combination (W ^ 2 ^ k * T ^ 2 ^ k) * h + (W * T) * h2

/-- Under the Frobenius-twist relation, `phi k Q` is the affine point `(p, q)` with
`p = N_x/N_y` and `q = D0/N_y`, both nonzero, and the twisted root equation
`W^(2^k+1) + p*T^(2^k+1) = q` holds.
@isnad1 id=ex.6h5v.s9.d37ada99dc93 from=translated src=- shape=b4519d1b vocab=f607132c
-/
theorem exists_twisted_root_equation (h : W ^ 3 + T ^ 3 = 1) (hW : W ≠ 0) (hT : T ≠ 0)
    (hkn : Nat.gcd k n = 1)
    (hB3 : ∃ (c : K) (hc : c ^ 3 = 1),
      pt (W ^ 2 ^ n) (T ^ 2 ^ n) (frob_fermat h n) = pt W T h + ptInf c hc)
    (hB5 : (3 : ℕ) • phi k W T h ≠ 0) :
    ∃ (p q : K) (hpq : p ^ 3 + q ^ 3 = 1),
      phi k W T h = pt p q hpq ∧ p ≠ 0 ∧ q ≠ 0 ∧
        W ^ (2 ^ k + 1) + p * T ^ (2 ^ k + 1) = q := by
  have hD := hessDenom_ne_zero h hW hT hkn hB3 hB5
  obtain ⟨hX, hY⟩ := hessCoords_ne_zero h hW hT hkn hB3 hB5
  have hcub := hess_cubic h (frob_fermat h k)
  have hp3 : (hessX W T (W ^ 2 ^ k) (T ^ 2 ^ k) / hessY W T (W ^ 2 ^ k) (T ^ 2 ^ k)) ^ 3
      + (hessD W T (W ^ 2 ^ k) (T ^ 2 ^ k) / hessY W T (W ^ 2 ^ k) (T ^ 2 ^ k)) ^ 3 = 1 := by
    field_simp
    linear_combination hcub + (hessD W T (W ^ 2 ^ k) (T ^ 2 ^ k) ^ 3
      - hessY W T (W ^ 2 ^ k) (T ^ 2 ^ k) ^ 3) * CharTwo.two_eq_zero (R := K)
  refine ⟨_, _, hp3, ?_, div_ne_zero hX hY, div_ne_zero hD hY, ?_⟩
  · rw [phi, add_pt h (frob_fermat h k) hD]
    exact neg_add_t3 hX hY hD _ hp3
  · have hB18 := hess_weighted_sum_eq_hessD (k := k) h
    field_simp
    linear_combination hB18

end Group

end KasamiCyclicAdditive.FermatCubic
