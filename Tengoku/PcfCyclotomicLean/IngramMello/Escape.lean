import Tengoku.PcfCyclotomicLean.IngramMello.IngramForms
import Tengoku.PcfCyclotomicLean.IngramMello.Statements

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Escape and local coefficient bounds (Proposition 3 of the paper, non-archimedean part)

Over any field `F` with a valuation `v : F → Γ₀`:

* `val_eval_eq_pow` (escape): if `f` is monic of degree `d ≥ 2` with `v (coeff) ≤ B`,
  `1 ≤ B`, and `B < v z`, then `v (f z) = v z ^ d`.
* `val_iterate_le_of_hasFiniteOrbit`: a point with finite forward orbit has all iterates
  of valuation `≤ B`.
* `exists_local_coeff_bound` (Ingram's Lemma 8 and Proposition 3(i), ultrametric case): there is
  `N = N(d) ≥ 1` such that for every field `F` of characteristic zero with a valuation, every
  monic centred `f` whose critical points and one fixed point lie in `F` and whose critical
  points have finite orbit satisfies `v (N * a_k) ≤ 1` for all coefficients, and
  `v (N * (fⁿ(c) - fᵐ(c))) ≤ 1` for all critical points `c ∈ F`.
-/

namespace IngramMello

open Polynomial

/-! ### Basic facts about `monicCentred` -/

section MonicCentred

variable {R : Type*} [CommRing R]

theorem monicCentred_eq (d : ℕ) (a : Fin (d - 1) → R) :
    monicCentred d a = X ^ d + ∑ i : Fin (d - 1), C (a i) * X ^ (i : ℕ) := rfl

theorem natDegree_monicCentred_sum_le (d : ℕ) (a : Fin (d - 1) → R) :
    (∑ i : Fin (d - 1), C (a i) * X ^ (i : ℕ)).natDegree ≤ d - 2 := by
  refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
  exact (natDegree_C_mul_X_pow_le _ _).trans (by omega)

theorem monicCentred_monic [Nontrivial R] {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → R) :
    (monicCentred d a).Monic := by
  rw [monicCentred_eq]
  apply monic_X_pow_add
  have := natDegree_monicCentred_sum_le d a
  rw [← degree_X_pow (R := R) d]
  exact degree_lt_degree (by rw [natDegree_X_pow]; omega)

theorem monicCentred_natDegree [Nontrivial R] {d : ℕ} (hd : 2 ≤ d) (a : Fin (d - 1) → R) :
    (monicCentred d a).natDegree = d := by
  rw [monicCentred_eq, natDegree_add_eq_left_of_natDegree_lt, natDegree_X_pow]
  rw [natDegree_X_pow]
  have := natDegree_monicCentred_sum_le d a
  omega

theorem monicCentred_coeff_eq_zero {d : ℕ} (a : Fin (d - 1) → R) {k : ℕ} (hk : d - 1 ≤ k)
    (hk' : k < d) : (monicCentred d a).coeff k = 0 := by
  rw [monicCentred_eq, coeff_add, coeff_X_pow, ite_eq_right (by omega), zero_add, finsetSum_coeff]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [coeff_C_mul_X_pow, ite_eq_right]
  have := i.isLt
  omega

theorem monicCentred_eval {d : ℕ} (a : Fin (d - 1) → R) (z : R) :
    (monicCentred d a).eval z = z ^ d + ∑ i : Fin (d - 1), a i * z ^ (i : ℕ) := by
  simp [monicCentred_eq, eval_finsetSum]

theorem critProd_isRoot_iff {F : Type*} [Field F] {n : ℕ} (u : Fin n → F) (r : F) :
    (critProd u).IsRoot r ↔ ∃ i, u i = r := by
  unfold critProd
  rw [IsRoot, eval_prod, Finset.prod_eq_zero_iff]
  simp only [Finset.mem_univ, true_and, eval_sub, eval_X, eval_C, sub_eq_zero]
  exact ⟨fun ⟨i, h⟩ => ⟨i, h.symm⟩, fun ⟨i, h⟩ => ⟨i, h.symm⟩⟩

/-- The critical points of a monic centred polynomial sum to zero.-/
theorem sum_crit_eq_zero {F : Type*} [Field F] [CharZero F] {d : ℕ} (hd : 2 ≤ d)
    (a : Fin (d - 1) → F) (c : Fin (d - 1) → F)
    (hc : derivative (monicCentred d a) = C (d : F) * critProd c) : ∑ i, c i = 0 := by
  have h1 : (derivative (monicCentred d a)).coeff (d - 2) = 0 := by
    rw [coeff_derivative, monicCentred_coeff_eq_zero a (by omega) (by omega), zero_mul]
  rw [hc, coeff_C_mul] at h1
  have h2 : (critProd c).coeff (d - 2) = -∑ i, c i := by
    unfold critProd
    have := prod_X_sub_C_coeff_card_pred (Finset.univ : Finset (Fin (d - 1))) c
      (by simp; omega)
    rw [Finset.card_univ, Fintype.card_fin, show d - 1 - 1 = d - 2 by omega] at this
    exact this
  rw [h2, mul_neg, neg_eq_zero, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact absurd h1 (Nat.cast_ne_zero.mpr (by omega))
  · exact h1

end MonicCentred

/-! ### Bookkeeping: `v (M * x) ≤ 1` -/

section Bdd

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

theorem vbdd_of_dvd {M M' : ℕ} (h : M ∣ M') {x : F} (hx : v ((M : F) * x) ≤ 1) :
    v ((M' : F) * x) ≤ 1 := by
  obtain ⟨t, rfl⟩ := h
  rw [Nat.cast_mul, mul_comm (M : F), mul_assoc, Valuation.map_mul]
  calc v (t : F) * v ((M : F) * x) ≤ 1 * 1 := mul_le_mul' (val_natCast_le_one v t) hx
    _ = 1 := mul_one 1

theorem vbdd_add {M : ℕ} {x y : F} (hx : v ((M : F) * x) ≤ 1) (hy : v ((M : F) * y) ≤ 1) :
    v ((M : F) * (x + y)) ≤ 1 := by
  rw [mul_add]; exact v.map_add_le hx hy

theorem vbdd_neg {M : ℕ} {x : F} (hx : v ((M : F) * x) ≤ 1) : v ((M : F) * (-x)) ≤ 1 := by
  rw [mul_neg, Valuation.map_neg]; exact hx

theorem vbdd_sub {M : ℕ} {x y : F} (hx : v ((M : F) * x) ≤ 1) (hy : v ((M : F) * y) ≤ 1) :
    v ((M : F) * (x - y)) ≤ 1 := by
  rw [sub_eq_add_neg]; exact vbdd_add v hx (vbdd_neg v hy)

theorem vbdd_mul {M M' : ℕ} {x y : F} (hx : v ((M : F) * x) ≤ 1) (hy : v ((M' : F) * y) ≤ 1) :
    v (((M * M' : ℕ) : F) * (x * y)) ≤ 1 := by
  rw [Nat.cast_mul, show (M : F) * M' * (x * y) = ((M : F) * x) * ((M' : F) * y) by ring,
    Valuation.map_mul]
  calc v ((M : F) * x) * v ((M' : F) * y) ≤ 1 * 1 := mul_le_mul' hx hy
    _ = 1 := mul_one 1

theorem vbdd_pow {M : ℕ} {x : F} (hx : v ((M : F) * x) ≤ 1) (n : ℕ) :
    v (((M ^ n : ℕ) : F) * x ^ n) ≤ 1 := by
  rw [Nat.cast_pow, ← mul_pow, Valuation.map_pow]
  exact pow_le_one' hx n

theorem vbdd_sum {M : ℕ} {ι : Type*} (s : Finset ι) {x : ι → F}
    (hx : ∀ i ∈ s, v ((M : F) * x i) ≤ 1) : v ((M : F) * ∑ i ∈ s, x i) ≤ 1 := by
  rw [Finset.mul_sum]; exact v.map_sum_le hx

theorem vbdd_natCast {M : ℕ} (n : ℕ) : v ((M : F) * (n : F)) ≤ 1 := by
  rw [← Nat.cast_mul]; exact val_natCast_le_one v _

theorem vbdd_one_of_le {M : ℕ} {x : F} (hx : v x ≤ 1) : v ((M : F) * x) ≤ 1 := by
  rw [Valuation.map_mul]
  calc v (M : F) * v x ≤ 1 * 1 := mul_le_mul' (val_natCast_le_one v M) hx
    _ = 1 := mul_one 1

/-- `v (M * x) ≤ 1` means `v x ≤ (v M)⁻¹`.-/
theorem le_inv_of_vbdd [CharZero F] {M : ℕ} (hM : 0 < M) {x : F} (hx : v ((M : F) * x) ≤ 1) :
    v x ≤ (v (M : F))⁻¹ := by
  have hM0 : v (M : F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr hM.ne'
  rw [Valuation.map_mul] at hx
  calc v x = (v (M : F))⁻¹ * (v (M : F) * v x) := by rw [inv_mul_cancel_left₀ hM0]
    _ ≤ (v (M : F))⁻¹ * 1 := mul_le_mul_right hx _
    _ = (v (M : F))⁻¹ := mul_one _

theorem vbdd_of_le_inv [CharZero F] {M : ℕ} (hM : 0 < M) {x : F} (hx : v x ≤ (v (M : F))⁻¹) :
    v ((M : F) * x) ≤ 1 := by
  have hM0 : v (M : F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr hM.ne'
  rw [Valuation.map_mul]
  calc v (M : F) * v x ≤ v (M : F) * (v (M : F))⁻¹ := mul_le_mul_right hx _
    _ = 1 := mul_inv_cancel₀ hM0

theorem one_le_inv_val_natCast [CharZero F] {M : ℕ} (hM : 0 < M) : 1 ≤ (v (M : F))⁻¹ := by
  have hM0 : v (M : F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Nat.cast_ne_zero.mpr hM.ne'
  rw [one_le_inv₀ (zero_lt_iff.mpr hM0)]
  exact val_natCast_le_one v M

end Bdd

/-! ### Coefficients of products of monic linear factors -/

section ProdCoeff

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

end ProdCoeff

/-! ### Escape -/

section Escape

variable {F : Type*} [Field F] {Γ₀ : Type*} [LinearOrderedCommGroupWithZero Γ₀]
  (v : Valuation F Γ₀)

/-- **Escape lemma.**-/
theorem val_eval_eq_pow {f : F[X]} (hf : f.Monic) (_hd : 2 ≤ f.natDegree) {B : Γ₀} (hB : 1 ≤ B)
    (hcoef : ∀ k < f.natDegree, v (f.coeff k) ≤ B) {z : F} (hz : B < v z) :
    v (f.eval z) = v z ^ f.natDegree := by
  have h1 : 1 < v z := lt_of_le_of_lt hB hz
  have hz0 : v z ≠ 0 := (zero_lt_one.trans h1).ne'
  rw [eval_eq_sum_range, Finset.sum_range_succ, hf.coeff_natDegree, one_mul]
  rw [Valuation.map_add_eq_of_lt_right, Valuation.map_pow]
  rw [Valuation.map_pow]
  refine v.map_sum_lt (pow_ne_zero _ hz0) fun k hk => ?_
  rw [Finset.mem_range] at hk
  rw [Valuation.map_mul, Valuation.map_pow]
  calc v (f.coeff k) * v z ^ k ≤ B * v z ^ k := mul_le_mul_left (hcoef k hk) _
    _ < v z * v z ^ k := mul_lt_mul_of_pos_right hz (pow_pos (zero_lt_one.trans h1) k)
    _ = v z ^ (k + 1) := (pow_succ' _ _).symm
    _ ≤ v z ^ f.natDegree := pow_le_pow_right' h1.le hk

theorem val_iterate_of_escape {f : F[X]} (hf : f.Monic) (hd : 2 ≤ f.natDegree) {B : Γ₀}
    (hB : 1 ≤ B) (hcoef : ∀ k < f.natDegree, v (f.coeff k) ≤ B) {z : F} (hz : B < v z) :
    ∀ n, B < v ((fun w => f.eval w)^[n] z) ∧
      v ((fun w => f.eval w)^[n] z) < v ((fun w => f.eval w)^[n + 1] z) := by
  intro n
  induction n with
  | zero =>
    refine ⟨hz, ?_⟩
    show v z < v (f.eval z)
    rw [val_eval_eq_pow v hf hd hB hcoef hz]
    have h1 : 1 < v z := lt_of_le_of_lt hB hz
    calc v z = v z * 1 := (mul_one _).symm
      _ < v z * v z ^ (f.natDegree - 1) :=
          mul_lt_mul_of_pos_left (one_lt_pow' h1 (by omega)) (zero_lt_one.trans h1)
      _ = v z ^ f.natDegree := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]
  | succ n ih =>
    have hz' : B < v ((fun w => f.eval w)^[n + 1] z) := ih.1.trans ih.2
    refine ⟨hz', ?_⟩
    rw [Function.iterate_succ_apply' _ (n + 1), val_eval_eq_pow v hf hd hB hcoef hz']
    have h1 : 1 < v ((fun w => f.eval w)^[n + 1] z) := lt_of_le_of_lt hB hz'
    calc v ((fun w => f.eval w)^[n + 1] z) = v ((fun w => f.eval w)^[n + 1] z) * 1 :=
          (mul_one _).symm
      _ < v ((fun w => f.eval w)^[n + 1] z) * v ((fun w => f.eval w)^[n + 1] z) ^ (f.natDegree - 1) :=
          mul_lt_mul_of_pos_left (one_lt_pow' h1 (by omega)) (zero_lt_one.trans h1)
      _ = _ := by rw [← pow_succ', Nat.sub_add_cancel (by omega)]

/-- `z` **escapes** under `f` at `v`: some iterate leaves a ball of radius `B ≥ 1` containing
all coefficients of `f`. By `val_iterate_of_escape` the valuations of the iterates then grow
strictly and the orbit is infinite. The negation says that every admissible `B` bounds the whole
orbit.-/
def Escapes (f : F[X]) (z : F) : Prop :=
  ∃ B : Γ₀, 1 ≤ B ∧ (∀ k < f.natDegree, v (f.coeff k) ≤ B) ∧
    ∃ n : ℕ, B < v ((fun w => f.eval w)^[n] z)

end Escape

/-! ### Conjugation by a fixed point -/

section Conj

variable {F : Type*} [Field F] [CharZero F]

/-- `g = f (X + p) - p`: conjugation of `f` by the translation `z ↦ z + p`.-/
noncomputable def conjFixed (f : F[X]) (p : F) : F[X] := f.comp (X + C p) - C p

theorem conjFixed_eval (f : F[X]) (p w : F) : (conjFixed f p).eval w = f.eval (w + p) - p := by
  simp [conjFixed, eval_comp]

theorem conjFixed_iterate (f : F[X]) (p z : F) (n : ℕ) :
    (fun w => (conjFixed f p).eval w)^[n] (z - p) = (fun w => f.eval w)^[n] z - p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, conjFixed_eval,
      sub_add_cancel]

theorem hasFiniteOrbit_conjFixed (f : F[X]) (p z : F) (hz : HasFiniteOrbit f z) :
    HasFiniteOrbit (conjFixed f p) (z - p) := by
  unfold HasFiniteOrbit at hz ⊢
  refine (hz.image (fun w => w - p)).subset ?_
  rintro _ ⟨n, rfl⟩
  refine ⟨(fun w => aeval w f)^[n] z, ⟨n, rfl⟩, ?_⟩
  simp only [coe_aeval_eq_eval]
  exact (conjFixed_iterate f p z n).symm

end Conj

/-! ### The local coefficient bound -/

section Main

universe u w

end Main

end IngramMello
