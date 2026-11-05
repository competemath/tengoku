module

public import Tengoku.Seed.NumberTheory.Bernoulli
public import Tengoku.Seed.NumberTheory.Padics.PadicIntegers
import Tengoku.KummerCriterion.KummerCriterion.KummerCongruence.VonStaudtClausen
import Tengoku.Seed.Analysis.SpecialFunctions.Pow.NNReal
import Tengoku.Seed.CategoryTheory.Category.Init

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Kummer congruences — Voronoi's congruence (Cohen Prop 9.5.20)

Voronoi's elementary congruence for generalized Bernoulli numbers:

 `(a^k − 1) · B_k ≡ k · a^{k−1} · ∑_{j=0}^{p−1} j^{k−1} · ⌊ja/p⌋ (mod p)`

for `a` coprime to `p`, `k ≥ 2` even with `(p−1) ∤ k` and `p ∤ (k+1)`.

This module exposes the main theorem `voronoi_congruence_mod_p`, built
from three helpers: the polynomial linear approximation, the
multiplicative permutation of residues, and the per-term binomial mod `p²`
bound. See the umbrella `KummerCriterion.KummerCongruence` for how this
combines with Step 2 to prove (Kummer's congruence).
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

/-- **Voronoi polynomial identity** (helper): in any commutative ring `R`,
for `k ≥ 1` and any `x y: R`,
 `(x - p·y)^k = x^k - k · x^{k-1} · p · y + p² · z`
for some `z : R`.-/
lemma voronoi_sub_pow_linear_approx {R : Type*} [CommRing R]
    (p : R) {k : ℕ} (hk : 1 ≤ k) (x y : R) :
    ∃ z : R,
      (x - p * y) ^ k = x ^ k - (k : R) * x ^ (k - 1) * p * y + p ^ 2 * z := by
  induction k with
  | zero => omega
  | succ n ih =>
    by_cases hn : n = 0
    · subst hn; refine ⟨0, ?_⟩; push_cast; ring
    · have hn_pos : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
      obtain ⟨z, hz⟩ := ih hn_pos
      refine ⟨z * x + (n : R) * x ^ (n - 1) * y * y - p * y * z, ?_⟩
      have h_pow_shift : x ^ (n - 1) * x = x ^ n := by
        rw [← pow_succ]; congr 1; omega
      have h_lhs : (x - p * y) ^ (n + 1) =
          (x ^ n - (n : R) * x ^ (n - 1) * p * y + p ^ 2 * z) * (x - p * y) := by
        rw [pow_succ, hz]
      rw [h_lhs, show (n + 1 - 1 : ℕ) = n from by omega, pow_succ x n,
        show ((n + 1 : ℕ) : R) = (n : R) + 1 from by push_cast; ring]
      linear_combination -((n : R) * p * y) * h_pow_shift

/-- **Voronoi permutation** (helper): if `a` is coprime to `p` (odd prime),
then multiplication by `a` permutes residues mod `p`. Hence for any function
`f: ℕ → R` (where `R` is an additive commutative monoid),
 `∑_{j < p} f((j * a) % p) = ∑_{j < p} f(j)`.-/
lemma voronoi_permutation
    {p : ℕ} [hp : Fact p.Prime] {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) :
    ∑ j ∈ Finset.range p, f ((j * a) % p) = ∑ j ∈ Finset.range p, f j := by
  have hp : Nat.Prime p := hp.out
  have ha_coprime_p : Nat.Coprime a p :=
    Nat.Coprime.symm ((hp.coprime_iff_not_dvd).mpr ha_coprime)
  set b : ℕ := ((a : ZMod p)⁻¹).val with hb_def
  have ha_unit : IsUnit ((a : ℕ) : ZMod p) := by
    rw [ZMod.isUnit_iff_coprime]
    exact ha_coprime_p
  have hab : ((a : ZMod p) * (a : ZMod p)⁻¹) = 1 :=
    ZMod.mul_inv_of_unit _ ha_unit
  have hb_zmod : ((b : ℕ) : ZMod p) = (a : ZMod p)⁻¹ := by
    rw [hb_def, ZMod.natCast_val, ZMod.cast_id]
  refine Finset.sum_nbij' (fun i => (i * a) % p) (fun j => (j * b) % p) ?_ ?_ ?_ ?_ ?_
  · intros i _; simp only [Finset.mem_range]; exact Nat.mod_lt _ hp.pos
  · intros j _; simp only [Finset.mem_range]; exact Nat.mod_lt _ hp.pos
  · intros i hi
    simp only [Finset.mem_range] at hi
    rw [show ((i * a) % p * b) % p = (i * a * b) % p by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]]
    have h_zmod : ((i * a * b : ℕ) : ZMod p) = (i : ZMod p) := by
      push_cast; rw [hb_zmod]
      rw [show ((i : ZMod p) * (a : ZMod p) * (a : ZMod p)⁻¹) =
        (i : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) from by ring, hab, mul_one]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod, Nat.mod_eq_of_lt hi]
  · intros j hj
    simp only [Finset.mem_range] at hj
    rw [show ((j * b) % p * a) % p = (j * b * a) % p by
      rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod]]
    have h_zmod : ((j * b * a : ℕ) : ZMod p) = (j : ZMod p) := by
      push_cast; rw [hb_zmod]
      rw [show ((j : ZMod p) * (a : ZMod p)⁻¹ * (a : ZMod p)) =
        (j : ZMod p) * ((a : ZMod p) * (a : ZMod p)⁻¹) from by ring, hab, mul_one]
    rw [(ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod, Nat.mod_eq_of_lt hj]
  · intros i _; dsimp only

/-- **Voronoi sum identity mod p²** (helper): in `ℤ_[p]`, for `k ≥ 1`,
`a` coprime to `p`,
 `(a^k - 1) · ∑_{j<p} j^k - k · a^{k-1} · p · ∑_{j<p} j^{k-1} · ⌊ja/p⌋ ∈ p²·ℤ_p`.
This is the summed binomial approximation after permuting residues.-/
lemma voronoi_sum_mod_p_sq
    {p : ℕ} [hp : Fact p.Prime]
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_pos : 0 < k) :
    ∃ W : ℤ_[p],
      (((a : ℤ_[p]) ^ k - 1) * ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) -
          (k : ℤ_[p]) * ((a : ℤ_[p]) ^ (k - 1)) * (p : ℤ_[p]) *
            ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℤ_[p])) =
        (p : ℤ_[p]) ^ 2 * W := by
  have hp_prime : Nat.Prime p := hp.out
  have h_div_mod : ∀ j : ℕ,
      ((j * a : ℕ) : ℤ_[p]) = ((j * a / p : ℕ) : ℤ_[p]) * (p : ℤ_[p]) +
        ((((j * a) % p : ℕ)) : ℤ_[p]) := fun j => by
    rw [show ((j * a : ℕ) : ℤ_[p]) = (((j * a / p) * p + (j * a) % p : ℕ) : ℤ_[p]) from by
      rw [← (Nat.div_add_mod' _ _).symm]]
    push_cast; ring
  choose wj hwj using (fun (j : ℕ) (_hj : j ∈ Finset.range p) =>
    voronoi_sub_pow_linear_approx (R := ℤ_[p])
      (p := (p : ℤ_[p])) (k := k) hk_pos ((j * a : ℕ) : ℤ_[p])
      (((j * a / p : ℕ)) : ℤ_[p]))
  have h_rj_eq : ∀ j : ℕ, (((((j * a) % p : ℕ)) : ℤ_[p])) =
      ((j * a : ℕ) : ℤ_[p]) - (p : ℤ_[p]) * (((j * a / p : ℕ)) : ℤ_[p]) := fun j => by
    linear_combination -h_div_mod j
  have h_per_j : ∀ (j : ℕ) (hj : j ∈ Finset.range p),
      (((((j * a) % p : ℕ)) : ℤ_[p])) ^ k =
        ((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * wj j hj := fun j hj => by rw [h_rj_eq j]; exact hwj j hj
  have h_perm : ((∑ j ∈ Finset.range p, ((j * a) % p) ^ k : ℕ) : ℤ_[p]) =
      ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) := by
    congr 1; exact voronoi_permutation ha_coprime (fun n : ℕ => n ^ k)
  set w : ℕ → ℤ_[p] := fun j => if h : j ∈ Finset.range p then wj j h else 0 with hw_def
  have hw_eq : ∀ (j : ℕ) (hj : j ∈ Finset.range p), w j = wj j hj := fun j hj => by
    change (if h : j ∈ Finset.range p then wj j h else 0) = wj j hj; simp [hj]
  set W_sum : ℤ_[p] := ∑ j ∈ Finset.range p, w j with hW_sum
  refine ⟨-W_sum, ?_⟩
  have h_sum_binom : (((∑ j ∈ Finset.range p, ((j * a) % p) ^ k : ℕ)) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * w j) := by
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl fun j hj => ?_
    rw [hw_eq j hj, Nat.cast_pow]
    exact h_per_j j hj
  have h_sum_ℤp : ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) =
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * w j) := by
    rw [← h_perm, h_sum_binom]
  have h_ja_pow : ∀ j : ℕ, ((j * a : ℕ) : ℤ_[p]) ^ k =
      ((a : ℤ_[p])) ^ k * ((j : ℕ) : ℤ_[p]) ^ k := fun j => by push_cast; ring
  have h_ja_pow_sub1 : ∀ j : ℕ, ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) =
      ((a : ℤ_[p])) ^ (k - 1) * ((j : ℕ) : ℤ_[p]) ^ (k - 1) := fun j => by push_cast; ring
  have h_sum_rewrite :
      ∑ j ∈ Finset.range p,
        (((j * a : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * ((j * a : ℕ) : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j * a / p : ℕ)) : ℤ_[p]) +
        (p : ℤ_[p]) ^ 2 * w j) =
      ∑ j ∈ Finset.range p,
        ((a : ℤ_[p]) ^ k * ((j : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j : ℕ) : ℤ_[p]) ^ (k - 1) * (((j * a / p : ℕ)) : ℤ_[p])) +
        (p : ℤ_[p]) ^ 2 * w j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [h_ja_pow j, h_ja_pow_sub1 j]; ring
  rw [h_sum_rewrite] at h_sum_ℤp
  have h_three :
      ∑ j ∈ Finset.range p,
        ((a : ℤ_[p]) ^ k * ((j : ℕ) : ℤ_[p]) ^ k -
          (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
            (((j : ℕ) : ℤ_[p]) ^ (k - 1) * (((j * a / p : ℕ)) : ℤ_[p])) +
        (p : ℤ_[p]) ^ 2 * w j) =
      (a : ℤ_[p]) ^ k * (∑ j ∈ Finset.range p, ((j : ℕ) : ℤ_[p]) ^ k) -
      (k : ℤ_[p]) * (a : ℤ_[p]) ^ (k - 1) * (p : ℤ_[p]) *
        (∑ j ∈ Finset.range p,
          ((j : ℕ) : ℤ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℤ_[p])) +
      (p : ℤ_[p]) ^ 2 * W_sum := by
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.mul_sum]
    congr 1; rw [hW_sum, Finset.mul_sum]
  have h_cast1 : (∑ j ∈ Finset.range p, ((j : ℕ) : ℤ_[p]) ^ k) =
      ((∑ j ∈ Finset.range p, j ^ k : ℕ) : ℤ_[p]) := by push_cast; rfl
  have h_cast2 : (∑ j ∈ Finset.range p,
        ((j : ℕ) : ℤ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℤ_[p])) =
      ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℤ_[p]) := by push_cast; rfl
  rw [h_three, h_cast1, h_cast2] at h_sum_ℤp
  linear_combination -h_sum_ℤp

/-- **Voronoi's congruence** (Cohen Prop 9.5.20, specialized to `n = p`).

For `a, p` coprime, `k ≥ 2` even with `(p-1) ∤ k` and `p ∤ (k+1)`:
 `(a^k - 1) · B_k ≡ k · a^{k-1} · ∑_{j=0}^{p-1} j^{k-1} · ⌊ja/p⌋ (mod p)`
in `ℚ_[p]`, with the difference a multiple of `p`.-/
theorem voronoi_congruence_mod_p
    {p : ℕ} [hp : Fact p.Prime] (hp_odd : p ≠ 2)
    {a : ℕ} (ha_coprime : ¬ (p : ℕ) ∣ a)
    {k : ℕ} (hk_two : 2 ≤ k) (hk_even : Even k) (_hk_coprime : ¬ (p - 1) ∣ k)
    (h_p_not_dvd_kPlus : ¬ (p : ℕ) ∣ (k + 1))
    (h_below_k : ∀ j, j ≤ k → ¬ (p : ℕ) ^ 3 ∣ (j + 1)) :
    ∃ z : ℤ_[p],
      ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
          (k : ℚ_[p]) * ((a : ℚ_[p]) ^ (k - 1)) *
            ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) =
        (p : ℚ_[p]) * (z : ℚ_[p]) := by
  have hp : Nat.Prime p := hp.out
  have hp_gt : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp_odd)
  have hk_pos : 0 < k := by omega
  have hpQ_ne : (p : ℚ_[p]) ≠ 0 := by exact_mod_cast hp.ne_zero
  obtain ⟨W, hW⟩ := voronoi_sum_mod_p_sq ha_coprime hk_pos
  obtain ⟨W', hW'⟩ := sum_range_pow_sub_p_mul_bernoulli_weighted hp_odd hk_two hk_even
    (fun j hj hj_two hj_even =>
      p_mul_bernoulli_mem_padicInt_restricted hp_odd hj_two hj_even
        (fun j' hj' => h_below_k j' (Nat.le_trans hj' hj.le)))
  have hkp1_unit : IsUnit ((k + 1 : ℕ) : ℤ_[p]) := by
    rw [PadicInt.isUnit_iff, PadicInt.norm_natCast_eq_one_iff]
    exact hp.coprime_iff_not_dvd.mpr h_p_not_dvd_kPlus
  set u : ℤ_[p] := (hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val with hu_def
  have hu_mul : ((k + 1 : ℕ) : ℤ_[p]) * u = 1 := by
    change ((hkp1_unit.unit * hkp1_unit.unit⁻¹ : (ℤ_[p])ˣ).val : ℤ_[p]) = 1; simp
  have hu_mul_Qp : ((k + 1 : ℕ) : ℚ_[p]) * ((u : ℤ_[p]) : ℚ_[p]) = 1 := by
    simpa using congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hu_mul
  refine ⟨W - ((a : ℤ_[p]) ^ k - 1) * u * W', ?_⟩
  set S1 : ℚ_[p] := ∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ k with hS1_def
  set S2 : ℚ_[p] :=
    ∑ j ∈ Finset.range p, (j : ℚ_[p]) ^ (k - 1) * ((j * a / p : ℕ) : ℚ_[p]) with hS2_def
  have hW_Q : ((a : ℚ_[p]) ^ k - 1) * S1 -
      (k : ℚ_[p]) * (a : ℚ_[p]) ^ (k - 1) * (p : ℚ_[p]) * S2 =
      (p : ℚ_[p]) ^ 2 * ((W : ℤ_[p]) : ℚ_[p]) := by
    have := congrArg (fun x : ℤ_[p] => (x : ℚ_[p])) hW
    simp only [PadicInt.coe_sub, PadicInt.coe_mul, PadicInt.coe_pow,
      PadicInt.coe_natCast, PadicInt.coe_one] at this
    rw [hS1_def, hS2_def]
    push_cast at this
    exact this
  have hkp1Q_ne : ((k + 1 : ℕ) : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have h_S1_sub : S1 - (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) =
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p]) := by
    have h_mul : ((k + 1 : ℕ) : ℚ_[p]) *
        (S1 - (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p])) =
        ((k + 1 : ℕ) : ℚ_[p]) *
        (((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p])) := by
      rw [hS1_def, hW']
      linear_combination -((p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p])) * hu_mul_Qp
    exact mul_left_cancel₀ hkp1Q_ne h_mul
  have hS1_eq : S1 = (p : ℚ_[p]) * ((bernoulli k : ℚ) : ℚ_[p]) +
      ((u : ℤ_[p]) : ℚ_[p]) * (p : ℚ_[p]) ^ 2 * ((W' : ℤ_[p]) : ℚ_[p]) := by
    linear_combination h_S1_sub
  rw [hS1_eq] at hW_Q
  have hS2_cast : ((∑ j ∈ Finset.range p, j ^ (k - 1) * (j * a / p) : ℕ) : ℚ_[p]) = S2 := by
    rw [hS2_def]; push_cast; rfl
  have hX : ((a : ℚ_[p]) ^ k - 1) * ((bernoulli k : ℚ) : ℚ_[p]) -
      (k : ℚ_[p]) * (a : ℚ_[p]) ^ (k - 1) * S2 =
      (p : ℚ_[p]) * (((W : ℤ_[p]) : ℚ_[p]) -
        ((a : ℚ_[p]) ^ k - 1) * ((u : ℤ_[p]) : ℚ_[p]) * ((W' : ℤ_[p]) : ℚ_[p])) :=
    mul_left_cancel₀ hpQ_ne (by linear_combination hW_Q)
  rw [hS2_cast]; push_cast; linear_combination hX

end KummerCriterion
