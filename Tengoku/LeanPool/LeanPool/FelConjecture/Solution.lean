/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/
module

public import Tengoku
/-! # Fel's Conjecture for Numerical Semigroups -/

@[expose] public section
/-- A *numerical semigroup*: an additive submonoid of `ℕ` with finite complement. -/
structure NumericalSemigroup where
  /-- The underlying set of natural numbers comprising the semigroup. -/
  carrier : Set ℕ
  zero_mem : 0 ∈ carrier
  add_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  finite_complement : (carrier)ᶜ.Finite

namespace NumericalSemigroup

-- The gap set (complement of the semigroup in ℕ)
/-- The *gaps* of `S`: the (finite) complement `ℕ \ S` as a `Finset`. -/
noncomputable def gaps (S : NumericalSemigroup) : Finset ℕ := S.finite_complement.toFinset

-- Gap power sum: G_r(S) = sum_{g in Delta} g^r (Definition 3)
/-- The gap power sum `G_r(S) = ∑_{g ∈ Δ} g^r` (Definition 3 in the paper). -/
noncomputable def gapPowerSum (S : NumericalSemigroup) (r : ℕ) : ℚ :=
  ∑ g ∈ S.gaps, (g : ℚ) ^ r

-- Gap polynomial: Phi_S(z) = sum_{g in Delta} z^g (Definition 4)
/-- The gap polynomial `Φ_S(z) = ∑_{g ∈ Δ} z^g` (Definition 4 in the paper). -/
noncomputable def gapPolynomial (S : NumericalSemigroup) : Polynomial ℚ :=
  ∑ g ∈ S.gaps, Polynomial.X ^ g

-- Hilbert series: H_S(z) = sum_{s in S} z^s (Definition 5)
-- Defined as a formal power series
-- We use Classical decidability since membership in S.carrier is not decidable in general
/-- The Hilbert series `H_S(z) = ∑_{s ∈ S} z^s`, expressed as a formal power series. -/
noncomputable def hilbertSeries (S : NumericalSemigroup) : PowerSeries ℚ :=
  PowerSeries.mk fun n => if Classical.propDecidable (n ∈ S.carrier) |>.decide then 1 else 0

/-- The coefficient of the Hilbert series at position n is 1 if n ∈ S.carrier, else 0. -/
lemma hilbertSeries_coeff (S : NumericalSemigroup) (n : ℕ) :
    (PowerSeries.coeff n) S.hilbertSeries =
    if Classical.propDecidable (n ∈ S.carrier) |>.decide then 1 else 0 := by
  simp only [hilbertSeries, PowerSeries.coeff_mk]

/-- The coefficient of the gap polynomial (viewed as a power series) at position n is 1 if n ∈
  S.gaps, else 0. -/
lemma gapPolynomial_coeff (S : NumericalSemigroup) (n : ℕ) :
    (PowerSeries.coeff n) (S.gapPolynomial : PowerSeries ℚ) =
    if n ∈ S.gaps then 1 else 0 := by
  unfold gapPolynomial
  simp_all

/-- For any n, we have n ∈ S.gaps ↔ n ∉ S.carrier. -/
lemma mem_gaps_iff_not_mem_carrier (S : NumericalSemigroup) (n : ℕ) :
    n ∈ S.gaps ↔ n ∉ S.carrier := by
  simp only [gaps, Set.Finite.mem_toFinset, Set.mem_compl_iff]

lemma semigroupGapDecomposition_aux (S : NumericalSemigroup) (n : ℕ) :
    (PowerSeries.coeff n) (S.hilbertSeries + (S.gapPolynomial : PowerSeries ℚ)) =
    (PowerSeries.coeff n) (PowerSeries.mk (1 : ℕ → ℚ)) := by
  rw [map_add]
  rw [hilbertSeries_coeff, gapPolynomial_coeff]
  rw [PowerSeries.coeff_mk]
  simp only [Pi.one_apply]
  by_cases h : n ∈ S.carrier
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    rw [ite_eq_right]
    · ring
    · rw [mem_gaps_iff_not_mem_carrier]; exact not_not.mpr h
  · simp only [decide_eq_true_eq, h, ↓reduceIte]
    rw [ite_eq_left (by rw [mem_gaps_iff_not_mem_carrier]; exact h)]
    ring

theorem semigroupGapDecomposition (S : NumericalSemigroup) :
    S.hilbertSeries + (S.gapPolynomial : PowerSeries ℚ) = PowerSeries.mk (1 : ℕ → ℚ) := by
  apply PowerSeries.ext
  exact semigroupGapDecomposition_aux S

end NumericalSemigroup

/-- A choice of generators for a numerical semigroup `S`: positive integers `d₁, …,
  d_m` with `gcd = 1` whose nonneg-integer combinations recover `S.carrier`. -/
structure NumericalSemigroupGenerators (S : NumericalSemigroup) where
  /-- The number of generators (embedding dimension of `S`). -/
  m : ℕ                           -- number of generators (embedding dimension)
  hm_pos : 0 < m                  -- at least one generator
  /-- The chosen generators `d₁, …, d_m`. -/
  d : Fin m → ℕ                   -- the generators d_1, ..., d_m
  hd_pos : ∀ i, 0 < d i           -- each generator is positive
  hgcd : (Finset.univ.image d).gcd id = 1  -- gcd of generators is 1
  generates : S.carrier = {n : ℕ | ∃ (c : Fin m → ℕ), n = ∑ i, c i * d i}

namespace NumericalSemigroupGenerators

/-- The product of generators `π_m = ∏ᵢ dᵢ` (Definition 6 in the paper). -/
def piM {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) : ℕ :=
  ∏ i : Fin G.m, G.d i

/-- The product polynomial `P_S(z) = ∏ᵢ (1 - z^{dᵢ})` (Definition 6 in the paper). -/
noncomputable def productPolynomial {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    Polynomial ℤ :=
  ∏ i : Fin G.m, (1 - Polynomial.X ^ (G.d i))

/-- Upper bound on the degree of the Hilbert numerator `Q_S(z)`. -/
noncomputable def hilbertNumeratorDegBound {S : NumericalSemigroup} (G :
  NumericalSemigroupGenerators S) :
    ℕ :=
  G.productPolynomial.natDegree + S.gaps.sup id + 1

/-- The Hilbert numerator `Q_S(z)`, computed coefficient-wise from `P_S` and the gaps. -/
noncomputable def hilbertNumerator {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    Polynomial ℤ :=
  let P := G.productPolynomial
  let bound := G.hilbertNumeratorDegBound
  ∑ n ∈ Finset.range bound,
    Polynomial.monomial n
      ((∑ k ∈ Finset.range (n + 1), P.coeff k) -
       (∑ g ∈ S.gaps.filter (· ≤ n), P.coeff (n - g)))

lemma coeff_mul_hilbert_product {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ) :
    (PowerSeries.coeff n) (S.hilbertSeries *
      (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
    ∑ k ∈ Finset.range (n + 1),
      (PowerSeries.coeff k) S.hilbertSeries *
        (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp_all

lemma lhs_eq_sum_over_carrier {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
  :
    ∑ k ∈ Finset.range (n + 1),
      (if (Classical.propDecidable (k ∈ S.carrier)).decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => (Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
  rw [Finset.sum_filter]
  simp_all

lemma partition_sum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => (Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) +
    ∑ k ∈ (Finset.range (n +
      1)).filter (fun k => !(Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
  have h := @Finset.sum_filter_add_sum_filter_not _ _ _ (Finset.range (n + 1))
    (fun k => k ∈ S.carrier) (Classical.decPred _) (fun x => Classical.dec _)
    (fun k => (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)))
  rw [← h]
  congr 1
  · congr 1
    ext k
    simp only [Finset.mem_filter, decide_eq_true_eq]
  · congr 1
    ext k
    simp only [Finset.mem_filter, Bool.not_eq_true', decide_eq_false_iff_not]

lemma filter_not_carrier_eq_gaps {S : NumericalSemigroup} (n : ℕ) :
    (Finset.range (n + 1)).filter (fun k => !(Classical.propDecidable (k ∈ S.carrier)).decide) =
    S.gaps.filter (· ≤ n) := by
  apply Finset.ext
  intro k
  simp only [Finset.mem_filter, Finset.mem_range, NumericalSemigroup.gaps,
    Set.Finite.mem_toFinset, Set.mem_compl_iff]
  constructor
  · simp_all
  · simp_all

lemma carrier_sum_eq_full_minus_gaps {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
  (n : ℕ) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => (Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ Finset.range (n + 1), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) -
    ∑ g ∈ S.gaps.filter (· ≤ n), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - g)) := by
  have hpart := partition_sum G n
  have hfilter := filter_not_carrier_eq_gaps (S := S) n
  simp_all

lemma sum_range_reindex (f : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f (n - k) = ∑ j ∈ Finset.range (n + 1), f j := by
  apply Finset.sum_bij' (fun k _ => n - k) (fun k _ => n - k)
  · intros k hk; rw [Finset.mem_range] at hk ⊢; omega
  · intros k hk; rw [Finset.mem_range] at hk ⊢; omega
  · intros k hk; rw [Finset.mem_range] at hk; omega
  · intros k hk; rw [Finset.mem_range] at hk; omega
  · intros k _; rfl

lemma large_n_both_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (_hn : n ≥ G.hilbertNumeratorDegBound) :
    (∑ k ∈ Finset.range (n + 1),
      (if Classical.propDecidable (k ∈ S.carrier) |>.decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    (Int.castRingHom ℚ) ((∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
     (∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g)))) := by
  rw [lhs_eq_sum_over_carrier]
  rw [carrier_sum_eq_full_minus_gaps]
  rw [sum_range_reindex (fun k => (Int.castRingHom ℚ) (G.productPolynomial.coeff k)) n]
  rw [map_sub, map_sum, map_sum]

lemma coeff_mul_eq_indicator_sum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ) :
    (PowerSeries.coeff n) (S.hilbertSeries *
      (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ)) =
    ∑ k ∈ Finset.range (n + 1),
      (if Classical.propDecidable (k ∈ S.carrier) |>.decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
  rw [coeff_mul_hilbert_product]
  apply Finset.sum_congr rfl
  intro k _
  rw [S.hilbertSeries_coeff]

lemma productPolynomial_eval_one {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    Polynomial.eval 1 G.productPolynomial = 0 := by
  unfold productPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := ⟨0, G.hm_pos⟩) (Finset.mem_univ _)
  simp

lemma sum_coeff_eq_eval_one {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1), G.productPolynomial.coeff k =
    Polynomial.eval 1 G.productPolynomial := by
  have h₁ : ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
    G.productPolynomial.coeff k = G.productPolynomial.eval 1 := by
    rw [Polynomial.eval_eq_sum_range]
    simp [add_comm]
  rw [h₁]

lemma coeff_Ico_eq_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) (_hn : G.productPolynomial.natDegree + 1 ≤ n)
    (k : ℕ) (hk : k ∈ Finset.Ico (G.productPolynomial.natDegree + 1) (n + 1)) :
    G.productPolynomial.coeff k = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  simp_all

lemma sum_coeff_large_eq_sum_coeff_deg {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) (hn : G.productPolynomial.natDegree + 1 ≤ n) :
    ∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k =
    ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1), G.productPolynomial.coeff k := by
  have hsplit := Finset.sum_range_add_sum_Ico (f := fun k => G.productPolynomial.coeff k)
    (m := G.productPolynomial.natDegree + 1) (n := n + 1) (by omega)
  have htail : ∑ k ∈ Finset.Ico (G.productPolynomial.natDegree + 1) (n + 1),
    G.productPolynomial.coeff k = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    exact coeff_Ico_eq_zero G n hn k hk
  linarith [hsplit, htail]

lemma first_sum_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    ∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k = 0 := by
  have h1 : G.productPolynomial.natDegree + 1 ≤ n := by
    unfold hilbertNumeratorDegBound at hn
    omega
  rw [sum_coeff_large_eq_sum_coeff_deg G n h1]
  rw [sum_coeff_eq_eval_one G]
  exact productPolynomial_eval_one G

lemma coeff_n_minus_gap_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n g : ℕ) (hn : n ≥ G.hilbertNumeratorDegBound) (hg : g ∈ S.gaps) (hgn : g ≤ n) :
    G.productPolynomial.coeff (n - g) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hge : g ≤ S.gaps.sup id := Finset.le_sup (f := id) hg
  have hn' : n ≥ G.productPolynomial.natDegree + S.gaps.sup id + 1 := hn
  omega

lemma second_sum_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    ∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g) = 0 := by
  apply Finset.sum_eq_zero
  intro g hg
  rw [Finset.mem_filter] at hg
  exact coeff_n_minus_gap_zero G n g hn hg.1 hg.2

lemma rhs_zero_of_large {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    (∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
     (∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g)) = 0 := by
  rw [first_sum_zero G n hn, second_sum_zero G n hn]
  ring

lemma coeff_eq_zero_of_large {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    (PowerSeries.coeff n) (S.hilbertSeries *
      (G.productPolynomial.map (Int.castRingHom ℚ) : PowerSeries ℚ)) = 0 := by
  rw [coeff_mul_eq_indicator_sum]
  rw [large_n_both_zero G n hn]
  rw [rhs_zero_of_large G n hn]
  simp

/-- The coefficients `cⱼ` in the expansion `Q_S(z) = 1 - ∑_{j ≥ 1} cⱼ z^j`. -/
noncomputable def numeratorCoeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (j : ℕ) : ℤ :=
  if j = 0 then 0 else -G.hilbertNumerator.coeff j

/-- The alternating power sum `C_n(S) = ∑_{j ≥ 1} cⱼ · jⁿ` (Definition 8). -/
noncomputable def alternatingPowerSum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) : ℚ :=
  ∑ j ∈ Finset.range G.hilbertNumeratorDegBound,
    (G.numeratorCoeff j : ℚ) * (j : ℚ) ^ n

/-- The invariant `K_p(S) =
  ((-1)^m · p!) / ((m+p)! · π_m) · C_{m+p}(S)` (Definition 9 in the paper). -/
noncomputable def KInvariant {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (p : ℕ) : ℚ :=
  ((-1 : ℚ) ^ G.m * (p.factorial : ℚ)) / (((G.m + p).factorial : ℚ) * (G.piM : ℚ)) *
    G.alternatingPowerSum (G.m + p)

/-- The single factor `(e^{dᵢ t} -
  1) / (dᵢ t) = ∑_k dᵢ^k · t^k / (k+1)!` of the `A` generating series. -/
noncomputable def scaledExpFactor {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (i : Fin G.m) : PowerSeries ℚ :=
  PowerSeries.mk fun k => (G.d i : ℚ) ^ k / ((k + 1).factorial : ℚ)

/-- The generating series `A(t) = ∏ᵢ (e^{dᵢ t} - 1) / (dᵢ t)` (Definition 10). -/
noncomputable def ASeries {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  ∏ i : Fin G.m, G.scaledExpFactor i

/-- The symbol `T_n(σ) = n! · [t^n] A(t)` (Definition 10). -/
noncomputable def TSigma {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) : ℚ
  :=
  (n.factorial : ℚ) * (PowerSeries.coeff n) (G.ASeries)

/-- The generating series `B(t) = (t / (e^t - 1)) · A(t)` (Definition 11). -/
noncomputable def BSeries {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  bernoulliPowerSeries ℚ * G.ASeries

/-- The symbol `T_n(δ) = (n! / 2^n) · [t^n] B(t)` (Definition 11). -/
noncomputable def TDelta {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) : ℚ
  :=
  (n.factorial : ℚ) / (2 ^ n : ℚ) * (PowerSeries.coeff n) (G.BSeries)

end NumericalSemigroupGenerators

namespace FelsConjectureProof

lemma pi_m_pos {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    0 < G.piM := by
  apply Finset.prod_pos
  intro i _
  exact G.hd_pos i

private lemma pos_of_mem_gaps {S : NumericalSemigroup} {g : ℕ} (hg : g ∈ S.gaps) : 0 < g := by
  rcases Nat.eq_zero_or_pos g with rfl | hpos
  · rw [NumericalSemigroup.gaps, Set.Finite.mem_toFinset, Set.mem_compl_iff] at hg
    exact absurd S.zero_mem hg
  · exact hpos

lemma choose_mul_sub_factorial_eq_div (n r : ℕ) (hr : r ≤ n) :
    ((n.choose r : ℚ) * ((n - r).factorial : ℚ)) = (n.factorial : ℚ) / (r.factorial : ℚ) := by
  have h₁ : (n.choose r : ℚ) * (r.factorial : ℚ) * ((n - r).factorial : ℚ) = (n.factorial : ℚ) := by
    norm_cast
    rw [← Nat.choose_mul_factorial_mul_factorial hr]
  have h₂ : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp [h₂]
  linarith

lemma bernoulli_term_simplify (m p : ℕ) (piM : ℕ) (hpi : 0 < piM)
    (coeff : ℚ) :
    ((-1 : ℚ)^m * (p.factorial : ℚ)) / (((m + p).factorial : ℚ) * (piM : ℚ)) *
      ((-1 : ℚ)^m * (piM : ℚ) * ((m + p).factorial : ℚ) * coeff) =
    (p.factorial : ℚ) * coeff := by
  have hpi' : (piM : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hpi)
  have hfac : ((m + p).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h_neg_sq : ((-1 : ℚ)^(m * 2)) = 1 := by
    simp_all
  field_simp [hpi', hfac]
  ring_nf
  simp_all

lemma outer_factor_cancel {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ)
    (sum_term : ℚ) :
    ((-1 : ℚ)^G.m * (p.factorial : ℚ)) / (((G.m + p).factorial : ℚ) * (G.piM : ℚ)) *
      ((-1 : ℚ)^G.m * (G.piM : ℚ) * sum_term) =
    (p.factorial : ℚ) / ((G.m + p).factorial : ℚ) * sum_term := by
  have hpi : (G.piM : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp (pi_m_pos G))
  have hfac : ((G.m + p).factorial : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero _)
  have h1 : ((-1 : ℚ)^G.m)^2 = 1 := by
    rw [← pow_mul, mul_comm]
    exact Even.neg_one_pow (even_two_mul G.m)
  field_simp
  rw [h1]
  ring

lemma term_simplify (m p r : ℕ) (hr : r ≤ p) (A_coeff G_r : ℚ) :
    (p.factorial : ℚ) / ((m + p).factorial : ℚ) *
      (((m + p).choose r : ℚ) * ((m + p - r).factorial : ℚ) * A_coeff * G_r) =
    (p.factorial : ℚ) / (r.factorial : ℚ) * A_coeff * G_r := by
  have hr_mp : r ≤ m + p := Nat.le_add_left r m |>.trans (Nat.add_le_add_left hr m)
  have h₁ : ((m + p).choose r : ℚ) * ((m + p - r).factorial : ℚ) =
      ((m + p).factorial : ℚ) / (r.factorial : ℚ) := choose_mul_sub_factorial_eq_div (m + p) r hr_mp
  have hfac : ((m + p).factorial : ℚ) ≠ 0 := by positivity
  rw [h₁]
  field_simp

lemma gap_sum_simplify {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ((-1 : ℚ)^G.m * (p.factorial : ℚ)) / (((G.m + p).factorial : ℚ) * (G.piM : ℚ)) *
      ((-1 : ℚ)^G.m * (G.piM : ℚ) *
        ∑ r ∈ Finset.range (p + 1),
          ((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ) *
            (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r) =
    ∑ r ∈ Finset.range (p + 1),
      ((p.factorial : ℚ) / (r.factorial : ℚ)) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by
  rw [outer_factor_cancel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  exact term_simplify G.m p r (Nat.lt_succ_iff.mp hr)
    ((PowerSeries.coeff (p - r)) G.ASeries) (S.gapPowerSum r)

/-- Auxiliary series obtained by evaluating `Q_S` at `t ↦ ∑ jⁿ t^n / n!` per coordinate. -/
noncomputable def QExpSeries {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) •
    (PowerSeries.X ^ (G.m - 1) * G.BSeries +
     PowerSeries.X ^ G.m * G.ASeries *
       PowerSeries.mk fun n => ∑ g ∈ S.gaps, (g : ℚ)^n / (n.factorial : ℚ))

/-- Auxiliary helper: `Q_S` minus its constant term,
  evaluated coefficient-wise on the exponential expansion. -/
noncomputable def hilbertNumeratorExpSub {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (∑ j ∈ Finset.range G.hilbertNumeratorDegBound, (G.hilbertNumerator.coeff j : ℚ) * (j : ℚ)^n) /
      (n.factorial : ℚ)

lemma B_term_coeff_shift {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    (PowerSeries.coeff (G.m + p)) (PowerSeries.X ^ (G.m - 1) * G.BSeries) =
    (PowerSeries.coeff (p + 1)) G.BSeries := by
  have hm_pos : 1 ≤ G.m := G.hm_pos
  have h₁ : (G.m : ℕ) - 1 ≤ G.m + p := by omega
  have h₂ : (G.m + p : ℕ) - (G.m - 1 : ℕ) = p + 1 := by omega
  have h₃ : (PowerSeries.coeff (G.m + p)) (PowerSeries.X ^ (G.m - 1) *
    G.BSeries) = (PowerSeries.coeff ((G.m + p) - (G.m - 1))) G.BSeries := by
    rw [PowerSeries.coeff_X_pow_mul']
    simp [h₁]
  rw [h₃, h₂]

lemma sum_swap_gaps_range {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ∑ r ∈ Finset.range (p + 1), (PowerSeries.coeff (p - r)) G.ASeries * (∑ g ∈ S.gaps,
      (g : ℚ)^r / (r.factorial : ℚ)) =
    ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
      (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ) := by
  have h₁ : ∑ r ∈ Finset.range (p + 1), (PowerSeries.coeff (p - r)) G.ASeries * (∑ g ∈ S.gaps,
    (g : ℚ)^r / (r.factorial : ℚ)) = ∑ r ∈ Finset.range (p + 1), ∑ g ∈ S.gaps,
      (PowerSeries.coeff (p - r)) G.ASeries * ((g : ℚ)^r / (r.factorial : ℚ)) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [Finset.mul_sum]
  rw [h₁]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  apply Finset.sum_congr rfl
  intro r _
  ring

lemma gap_coeff_to_leibniz {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ((G.m + p).factorial : ℚ) *
      ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
        (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ) =
    ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
        ((G.m + p).factorial : ℚ) / (r.factorial : ℚ) *
          (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  have hr_fac : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp [hr_fac]

lemma gap_sum_swap {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
        ((G.m + p).factorial : ℚ) / (r.factorial : ℚ) *
          (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r =
    ∑ r ∈ Finset.range (p + 1),
      ((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hrp : r ≤ p := Nat.lt_succ_iff.mp hr
  have hr_mp : r ≤ G.m + p := Nat.le_add_left r G.m |>.trans (Nat.add_le_add_left hrp G.m)
  have h_choose := choose_mul_sub_factorial_eq_div (G.m + p) r hr_mp
  unfold NumericalSemigroup.gapPowerSum
  rw [Finset.mul_sum]
  simp_all

lemma gap_term_final_form {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    ((G.m + p).factorial : ℚ) *
      ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
        (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ) =
    ∑ r ∈ Finset.range (p + 1),
      ((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by
  rw [gap_coeff_to_leibniz, gap_sum_swap]

/-- For a polynomial `P : ℤ[X]`,
  the formal power series `∑ₙ (P.coeff n : ℚ) · t^n / n!` minus its constant term. -/
noncomputable def expPolySub (P : Polynomial ℤ) : PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℚ) * (j : ℚ)^n) / (n.factorial : ℚ)

lemma exp_poly_sub_sum_extend (P : Polynomial ℤ) (k : ℕ) (n : ℕ) (hk : P.natDegree + 1 ≤ k) :
    ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℚ) * (j : ℚ)^n =
    ∑ j ∈ Finset.range k, (P.coeff j : ℚ) * (j : ℚ)^n := by
  apply Finset.sum_subset (Finset.range_mono hk)
  intro j _ hj'
  simp only [Finset.mem_range, not_lt] at hj'
  rw [show (P.coeff j : ℚ) = 0 by
    exact_mod_cast Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  ring

lemma hilbertNumeratorDegBound_pos {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    0 < G.hilbertNumeratorDegBound := by
  unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound
  omega

lemma Q_exp_series_coeff {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) (QExpSeries G) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) *
      ((PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) +
       (PowerSeries.coeff n) (PowerSeries.X ^ G.m * G.ASeries *
         PowerSeries.mk fun k => ∑ g ∈ S.gaps, (g : ℚ)^k / (k.factorial : ℚ))) := by
  simp only [QExpSeries, PowerSeries.coeff_smul, smul_eq_mul, map_add]

lemma partial_sum_eq_zero_when_large {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (D : ℕ) (hD : G.productPolynomial.natDegree ≤ D) :
    (∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ)) = 0 := by
  have h1 : ∑ k ∈ Finset.range (D + 1), G.productPolynomial.coeff k =
            ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
              G.productPolynomial.coeff k := by
    rcases Nat.eq_or_lt_of_le hD with heq | hlt
    · rw [heq]
    · exact NumericalSemigroupGenerators.sum_coeff_large_eq_sum_coeff_deg G D (by omega)
  have h2 : ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1), G.productPolynomial.coeff k =
            Polynomial.eval 1 G.productPolynomial :=
              NumericalSemigroupGenerators.sum_coeff_eq_eval_one G
  have h3 : Polynomial.eval 1 G.productPolynomial = 0 :=
    NumericalSemigroupGenerators.productPolynomial_eval_one G
  simp only [← Int.cast_sum]
  simp_all

lemma leadingCoeff_one_sub_X_pow (k : ℕ) (hk : 0 < k) :
    (1 - Polynomial.X ^ k : Polynomial ℤ).leadingCoeff = -1 := by
  have h₁ : (1 - Polynomial.X ^ k : Polynomial ℤ) = -(Polynomial.X ^ k - 1 : Polynomial ℤ) :=
    by ring
  have h₂ : (Polynomial.X ^ k - 1 : Polynomial ℤ).Monic := by
    apply Polynomial.monic_X_pow_sub_C
    omega
  simp only [h₁, Polynomial.leadingCoeff_neg, h₂.leadingCoeff]

lemma productPolynomial_leadingCoeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    G.productPolynomial.leadingCoeff = (-1 : ℤ) ^ G.m := by
  unfold NumericalSemigroupGenerators.productPolynomial
  rw [Polynomial.leadingCoeff_prod]
  have h : ∀ i : Fin G.m, (1 - Polynomial.X ^ G.d i : Polynomial ℤ).leadingCoeff = -1 := by
    intro i
    exact leadingCoeff_one_sub_X_pow (G.d i) (G.hd_pos i)
  simpa only [h] using Fin.prod_const G.m (-1 : ℤ)

lemma natDegree_ge_of_gaps_nonempty {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (h : S.gaps.Nonempty) :
    G.productPolynomial.natDegree ≤ G.hilbertNumerator.natDegree := by
  have hge : G.productPolynomial.natDegree + S.gaps.sup id ≤ G.hilbertNumerator.natDegree := by
    apply Polynomial.le_natDegree_of_ne_zero
    unfold NumericalSemigroupGenerators.hilbertNumerator
    simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_monomial]
    rw [Finset.sum_eq_single (G.productPolynomial.natDegree + S.gaps.sup id)]
    · simp only [↓reduceIte, ne_eq, sub_eq_zero]
      intro hcontra
      obtain ⟨gmax, hgmax_mem, hgmax_eq⟩ := Finset.exists_mem_eq_sup S.gaps h id
      simp only [id_eq] at hgmax_eq
      have hfilter : S.gaps.filter (· ≤ G.productPolynomial.natDegree + S.gaps.sup id) = S.gaps :=
        by
        apply Finset.filter_true_of_mem
        intro g hg
        calc g ≤ S.gaps.sup id := Finset.le_sup (f := id) hg
             _ ≤ G.productPolynomial.natDegree + S.gaps.sup id := le_add_self
      have hsum_partial : ∑ k ∈ Finset.range (G.productPolynomial.natDegree + S.gaps.sup id + 1),
          G.productPolynomial.coeff k = 0 := by
        have hge : 1 ≤ S.gaps.sup id := by rw [hgmax_eq]; exact pos_of_mem_gaps hgmax_mem
        have h1 :=
          NumericalSemigroupGenerators.sum_coeff_large_eq_sum_coeff_deg G
            (G.productPolynomial.natDegree + S.gaps.sup id) (by omega)
        rw [h1, NumericalSemigroupGenerators.sum_coeff_eq_eval_one G,
          NumericalSemigroupGenerators.productPolynomial_eval_one G]
      rw [hfilter] at hcontra
      rw [Finset.sum_eq_single_of_mem gmax hgmax_mem] at hcontra
      · have hsub : G.productPolynomial.natDegree +
        S.gaps.sup id - gmax = G.productPolynomial.natDegree := by rw [hgmax_eq, Nat.add_sub_cancel]
        rw [hsub, Polynomial.coeff_natDegree, productPolynomial_leadingCoeff G] at hcontra
        simp_all
      · intro g hg hne
        apply Polynomial.coeff_eq_zero_of_natDegree_lt
        have hle : g ≤ gmax := by
          have := Finset.le_sup (f := id) hg
          simp_all
        have hlt : g < gmax := lt_of_le_of_ne hle hne
        simp only [hgmax_eq]
        omega
    · simp_all
    · intro hn
      simp only [Finset.mem_range, not_lt] at hn
      unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound at hn
      omega
  omega

lemma telescoping_general (D n : ℕ) (P : Polynomial ℤ) :
    (∑ j ∈ Finset.range (D + 1),
      (∑ k ∈ Finset.range (j + 1), (P.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) =
    (∑ k ∈ Finset.range (D + 1), (P.coeff k : ℚ)) * ((D : ℚ) + 1)^n -
    (∑ j ∈ Finset.range (D + 1), (P.coeff j : ℚ) * (j : ℚ)^n) := by
  induction D with
  | zero =>
    simp [Finset.sum_range_succ]
    ring_nf
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    simp [Finset.sum_range_succ, add_assoc] at *
    ring_nf at *

lemma telescoping_sum_gaps_nonempty {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) (hgaps : S.gaps.Nonempty) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) =
    - (∑ j ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) := by
  set D := G.hilbertNumerator.natDegree with hD_def
  set d := G.productPolynomial.natDegree with hd_def
  have htele := telescoping_general D n G.productPolynomial
  have hDge : d ≤ D := natDegree_ge_of_gaps_nonempty G hgaps
  have hSD : ∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ) = 0 :=
    partial_sum_eq_zero_when_large G D hDge
  rw [htele, hSD, zero_mul, zero_sub]
  have hext : ∑ j ∈ Finset.range (d + 1), (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n =
              ∑ j ∈ Finset.range (D + 1), (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n :=
    exp_poly_sub_sum_extend G.productPolynomial (D + 1) n (Nat.add_le_add_right hDge 1)
  rw [← hext]

lemma hilbertNumerator_coeff_eq_partial_sum_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (hgaps : ¬S.gaps.Nonempty) (j : ℕ)
    (hj : j < G.hilbertNumeratorDegBound) :
    G.hilbertNumerator.coeff j = ∑ k ∈ Finset.range (j + 1), G.productPolynomial.coeff k := by
  have h₁ : S.gaps = ∅ := by
    simp_all
  have h₂ : ∀ (n : ℕ), ∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g) = 0 := by
    simp_all
  have h₃ : ∀ (n : ℕ), n < G.hilbertNumeratorDegBound →
      G.hilbertNumerator.coeff n = ∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k := by
    intro n hn
    have h₄ : G.hilbertNumerator.coeff n =
        (∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
        ∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g) := by
      simp only [NumericalSemigroupGenerators.hilbertNumerator]
      simp [Polynomial.coeff_monomial, Finset.mem_range, hn]
    rw [h₄, h₂ n, sub_zero]
  exact h₃ j hj

lemma partial_sum_zero_after_natDegree_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (hgaps : ¬S.gaps.Nonempty) (j : ℕ)
    (hj1 : G.hilbertNumerator.natDegree < j) (hj2 : j < G.hilbertNumeratorDegBound) :
    (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) = 0 := by
  have h_coeff_eq := hilbertNumerator_coeff_eq_partial_sum_gaps_empty G hgaps j hj2
  have h_coeff_zero : G.hilbertNumerator.coeff j = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hj1
  have h_sum_zero : ∑ k ∈ Finset.range (j + 1), G.productPolynomial.coeff k = 0 := by
    rw [← h_coeff_eq, h_coeff_zero]
  rw [← Int.cast_sum]
  simp only [h_sum_zero, Int.cast_zero]

lemma coeff_eq_partial_sum_diff (P : Polynomial ℤ) (n : ℕ) :
    (P.coeff n : ℚ) = (∑ k ∈ Finset.range (n + 1), (P.coeff k : ℚ)) -
                      (∑ k ∈ Finset.range n, (P.coeff k : ℚ)) := by
  have h_sum_split : (∑ k ∈ Finset.range (n + 1), (P.coeff k : ℚ)) =
      (∑ k ∈ Finset.range n, (P.coeff k : ℚ)) + (P.coeff n : ℚ) := by
    rw [Finset.sum_range_succ]
  simp_all

lemma coeff_at_D_plus_one_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (hgaps : ¬S.gaps.Nonempty)
    (hbound : G.hilbertNumerator.natDegree + 1 < G.hilbertNumeratorDegBound) :
    (G.productPolynomial.coeff (G.hilbertNumerator.natDegree + 1) : ℚ) =
    -(∑ k ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ)) := by
  set D := G.hilbertNumerator.natDegree with hD_def
  have h1 : (G.productPolynomial.coeff (D + 1) : ℚ) =
      (∑ k ∈ Finset.range (D + 1 + 1), (G.productPolynomial.coeff k : ℚ)) -
      (∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ)) :=
    coeff_eq_partial_sum_diff G.productPolynomial (D + 1)
  have h2 : (∑ k ∈ Finset.range (D + 1 + 1), (G.productPolynomial.coeff k : ℚ)) = 0 := by
    apply partial_sum_zero_after_natDegree_gaps_empty G hgaps (D + 1)
    · exact Nat.lt_add_one D
    · exact hbound
  rw [h1, h2, zero_sub]

lemma coeff_zero_after_D_plus_one_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (hgaps : ¬S.gaps.Nonempty)
    (_hbound : G.hilbertNumerator.natDegree + 1 < G.hilbertNumeratorDegBound)
    (j : ℕ) (hj_lo : G.hilbertNumerator.natDegree + 2 ≤ j)
    (hj_hi : j ≤ G.productPolynomial.natDegree) :
    (G.productPolynomial.coeff j : ℚ) = 0 := by
  set D := G.hilbertNumerator.natDegree with hD_def
  have hcoeff_rel : (G.productPolynomial.coeff j : ℚ) =
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) -
      (∑ k ∈ Finset.range j, (G.productPolynomial.coeff k : ℚ)) :=
    coeff_eq_partial_sum_diff G.productPolynomial j
  rw [hcoeff_rel]
  have hj_bound : j < G.hilbertNumeratorDegBound := by
    unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound at _hbound ⊢
    omega
  have hjm1_bound : j - 1 < G.hilbertNumeratorDegBound := by omega
  have hj_gt_D : D < j := by omega
  have hjm1_gt_D : D < j - 1 := by omega
  have hS_j_zero : (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) = 0 :=
    partial_sum_zero_after_natDegree_gaps_empty G hgaps j hj_gt_D hj_bound
  have hS_jm1_zero : (∑ k ∈ Finset.range j, (G.productPolynomial.coeff k : ℚ)) = 0 := by
    have heq : j = (j - 1) + 1 := by omega
    rw [heq]
    exact partial_sum_zero_after_natDegree_gaps_empty G hgaps (j - 1) hjm1_gt_D hjm1_bound
  simp_all

lemma sum_tail_eq_zero {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) (hgaps : ¬S.gaps.Nonempty)
    (hbound : G.hilbertNumerator.natDegree + 1 < G.hilbertNumeratorDegBound) :
    (∑ j ∈ Finset.Ico (G.hilbertNumerator.natDegree + 2) (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) = 0 := by
  apply Finset.sum_eq_zero
  intro j hj
  simp only [Finset.mem_Ico] at hj
  have hj_lo : G.hilbertNumerator.natDegree + 2 ≤ j := hj.1
  have hj_hi : j ≤ G.productPolynomial.natDegree := by omega
  have hcoeff_zero : (G.productPolynomial.coeff j : ℚ) = 0 :=
    coeff_zero_after_D_plus_one_gaps_empty G hgaps hbound j hj_lo hj_hi
  simp_all

lemma poly_sum_tail_eq_neg_partial_gaps_empty {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) (hgaps : ¬S.gaps.Nonempty)
    (hbound : G.hilbertNumerator.natDegree + 1 < G.hilbertNumeratorDegBound) :
    (∑ j ∈ Finset.Ico (G.hilbertNumerator.natDegree + 1) (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) =
    -(∑ k ∈ Finset.range (G.hilbertNumerator.natDegree + 1), (G.productPolynomial.coeff k : ℚ)) *
     ((G.hilbertNumerator.natDegree : ℚ) + 1)^n := by
  set D := G.hilbertNumerator.natDegree with hD_def
  set d := G.productPolynomial.natDegree with hd_def
  by_cases hcase : D + 1 > d
  · have hempty : Finset.Ico (D + 1) (d + 1) = ∅ := Finset.Ico_eq_empty_of_le (by omega)
    simp only [hempty, Finset.sum_empty]
    have hDd : d ≤ D := by omega
    have hS_D_zero : (∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ)) = 0 :=
      partial_sum_eq_zero_when_large G D hDd
    simp_all
  · push Not at hcase
    have hsplit : Finset.Ico (D + 1) (d + 1) = {D + 1} ∪ Finset.Ico (D + 2) (d + 1) := by
      ext x
      simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
      constructor
      · intro ⟨hlo, hhi⟩
        by_cases hx : x = D + 1
        · left; exact hx
        · right; constructor <;> omega
      · intro h
        cases h with
        | inl h => rw [h]; constructor <;> omega
        | inr h => obtain ⟨hlo, hhi⟩ := h; constructor <;> omega
    have hdisj : Disjoint ({D + 1} : Finset ℕ) (Finset.Ico (D + 2) (d + 1)) := by
      simp_all
    rw [hsplit, Finset.sum_union hdisj]
    simp only [Finset.sum_singleton]
    rw [sum_tail_eq_zero G n hgaps hbound]
    rw [add_zero]
    rw [coeff_at_D_plus_one_gaps_empty G hgaps hbound]
    simp only [← hD_def, Nat.cast_add, Nat.cast_one, neg_mul]

lemma telescoping_sum_gaps_empty {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) (hgaps : ¬S.gaps.Nonempty) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) =
    - (∑ j ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) := by
  set D := G.hilbertNumerator.natDegree with hD_def
  set d := G.productPolynomial.natDegree with hd_def
  rw [telescoping_general D n G.productPolynomial]
  simp only [Finset.not_nonempty_iff_eq_empty] at hgaps
  have hgaps_sup : S.gaps.sup id = 0 := by rw [hgaps]; simp
  by_cases hbound : D + 1 < G.hilbertNumeratorDegBound
  · have hle : D + 1 ≤ d + 1 := by
      unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound at hbound
      rw [hgaps_sup] at hbound
      omega
    rw [← Finset.sum_range_add_sum_Ico _ hle]
    have hgaps' : ¬S.gaps.Nonempty := by simp [hgaps]
    have htail := poly_sum_tail_eq_neg_partial_gaps_empty G n hgaps' hbound
    rw [htail]
    ring
  · push Not at hbound
    unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound at hbound
    rw [hgaps_sup] at hbound
    have hDge : d ≤ D := Nat.lt_succ_iff.mp (Nat.succ_le_iff.mpr hbound)
    have hS_D_zero : (∑ k ∈ Finset.range (D + 1), (G.productPolynomial.coeff k : ℚ)) = 0 :=
      partial_sum_eq_zero_when_large G D hDge
    have hext := exp_poly_sub_sum_extend G.productPolynomial (D + 1) n (by omega)
    simp_all

lemma telescoping_sum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) =
    - (∑ j ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff j : ℚ) * (j : ℚ)^n) := by
  by_cases hgaps : S.gaps.Nonempty
  · exact telescoping_sum_gaps_nonempty G n hgaps
  · exact telescoping_sum_gaps_empty G n hgaps

/-- Generating function for the partial sums of `P_S.coeff` along `Finset.range`. -/
noncomputable def partialSumGenFunc {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries ℚ :=
  PowerSeries.mk fun n =>
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff k : ℚ)) * (j : ℚ)^n) / (n.factorial : ℚ)

lemma term_factorial_to_choose (Pa Qb : ℚ) (a b k n : ℕ) (hk : k ≤ n) :
    Pa * Qb * (a : ℚ)^k * (b : ℚ)^(n - k) / (k.factorial * (n - k).factorial) =
    Pa * Qb * (a : ℚ)^k * (b : ℚ)^(n - k) * ((n.choose k : ℚ) / (n.factorial : ℚ)) := by
  have h₃ : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) = (n.factorial : ℚ) := by
    norm_cast
    rw [Nat.choose_mul_factorial_mul_factorial hk]
  have h₁ : (1 : ℚ) / (k.factorial * (n - k).factorial) = (n.choose k : ℚ) / (n.factorial : ℚ) := by
    have h₄ : (k.factorial : ℚ) ≠ 0 := by positivity
    have h₅ : ((n - k).factorial : ℚ) ≠ 0 := by positivity
    have h₆ : (n.factorial : ℚ) ≠ 0 := by positivity
    field_simp [h₄, h₅, h₆] at h₃ ⊢
    nlinarith
  rw [div_eq_mul_one_div, h₁]

lemma natDegree_one_sub_X_pow_le (k : ℕ) :
    (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≤ k := by
  refine Polynomial.natDegree_sub_le _ _ |>.trans ?_
  simp [Polynomial.natDegree_pow, Polynomial.natDegree_X]

lemma natDegree_one_sub_X_pow_eq (k : ℕ) (hk : 0 < k) :
    (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree = k := by
  have h₁ : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≤ k := natDegree_one_sub_X_pow_le k
  have h₃ : (1 - Polynomial.X ^ k : Polynomial ℤ).coeff k = -1 := by
    simp [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow]
    cases k <;> simp_all
  refine le_antisymm h₁ (Polynomial.le_natDegree_of_ne_zero ?_)
  simp_all

lemma rhs_coeff_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (i : Fin G.m) :
    (PowerSeries.coeff 0) (-(G.d i : ℚ) • (PowerSeries.X * G.scaledExpFactor i)) = 0 := by
  simp_all

lemma rhs_coeff_pos {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (i : Fin G.m)
    (n : ℕ) (hn : 1 ≤ n) :
    (PowerSeries.coeff n) (-(G.d i : ℚ) • (PowerSeries.X * G.scaledExpFactor i)) =
    -((G.d i : ℚ)^n) / (n.factorial : ℚ) := by
  rw [PowerSeries.coeff_smul]
  obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.one_le_iff_ne_zero.mp hn)
  subst hk
  rw [PowerSeries.coeff_succ_X_mul]
  simp only [NumericalSemigroupGenerators.scaledExpFactor, PowerSeries.coeff_mk]
  simp only [smul_eq_mul, Nat.succ_eq_add_one]
  ring

lemma prod_smul_eq_smul_prod (m : ℕ) (c : Fin m → ℚ) (f : Fin m → PowerSeries ℚ) :
    ∏ i : Fin m, (c i • f i) = (∏ i : Fin m, c i) • (∏ i : Fin m, f i) := by
  simp only [MvPowerSeries.smul_eq_C_mul]
  rw [Finset.prod_mul_distrib]
  rw [← map_prod]

lemma prod_X_mul_eq_X_pow_mul (m : ℕ) (f : Fin m → PowerSeries ℚ) :
    ∏ i : Fin m, (PowerSeries.X * f i) = PowerSeries.X ^ m * ∏ i : Fin m, f i := by
  simp_rw [Finset.prod_mul_distrib, Fin.prod_const]

lemma prod_neg_eq_neg_one_pow_mul (m : ℕ) (c : Fin m → ℚ) :
    ∏ i : Fin m, (-c i) = (-1 : ℚ) ^ m * ∏ i : Fin m, c i := by
  rw [show (fun i => -c i) = fun i => (-1 : ℚ) * c i from by funext i; ring,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

lemma prod_single_factor_eq_final_form {S : NumericalSemigroup} (G : NumericalSemigroupGenerators
  S) :
    ∏ i : Fin G.m, (-(G.d i : ℚ) • (PowerSeries.X * G.scaledExpFactor i)) =
    ((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) := by
  rw [prod_smul_eq_smul_prod]
  rw [prod_X_mul_eq_X_pow_mul]
  have h1 : (∏ i : Fin G.m, -(G.d i : ℚ)) = (-1 : ℚ) ^ G.m * (G.piM : ℚ) := by
    rw [prod_neg_eq_neg_one_pow_mul]
    congr 1
    simp only [NumericalSemigroupGenerators.piM]
    rw [Nat.cast_prod]
  rw [h1]
  rfl

-- productPolynomial_exp_transform: defined later at productPolynomial_exp_transform'

lemma binomial_sum_eq_power (a b n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) = ((a : ℚ) + b)^n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [mul_comm ((n.choose k : ℚ)) _]
  ring

lemma coeff_one_sub_exp (n : ℕ) :
    (PowerSeries.coeff n) (1 - PowerSeries.exp ℚ) =
    if n = 0 then 0 else -1 / (n.factorial : ℚ) := by
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_exp]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs with h
  · simp [h]
  · ring

lemma binomial_sum_minus_j_pow (j n : ℕ) :
    (∑ k ∈ Finset.range (n + 1), if k = 0 then 0 else (n.choose k : ℚ) * (j : ℚ)^(n - k)) =
    ((j : ℚ) + 1)^n - (j : ℚ)^n := by
  have h := add_pow (1 : ℚ) (j : ℚ) n
  simp only [one_pow, add_comm] at h
  rw [Finset.sum_eq_add_sum_sdiff_singleton 0 _
      (fun hnot => absurd (Finset.mem_range.mpr (Nat.zero_lt_succ n)) hnot)]
  simp only [↓reduceIte, zero_add]
  have hne : ∀ x ∈ (Finset.range n.succ \ {0}), x ≠ 0 := by
    simp [Finset.mem_sdiff, Finset.mem_singleton]
  rw [Finset.sum_congr rfl (fun x hx => ite_eq_right (hne x hx))]
  rw [Finset.sum_eq_add_sum_sdiff_singleton 0 _
      (fun hnot => absurd (Finset.mem_range.mpr (Nat.zero_lt_succ n)) hnot)] at h
  simp only [Nat.choose_zero_right, Nat.cast_one, one_mul, Nat.sub_zero] at h
  calc
    ∑ k ∈ Finset.range n.succ \ {0}, (n.choose k : ℚ) * (j : ℚ)^(n - k)
      = ∑ k ∈ Finset.range n.succ \ {0}, (j : ℚ)^(n - k) * (n.choose k : ℚ) := by
        apply Finset.sum_congr rfl; intro k _; ring
    _ = ((j : ℚ) + 1)^n - (j : ℚ)^n := by linarith

lemma factor_neg_choose_div_factorial (D n : ℕ) (coeff : ℕ → ℚ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-(n.choose k : ℚ) / (n.factorial : ℚ)) *
        (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k))) =
    (-1 / (n.factorial : ℚ)) *
    (∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (n.choose k : ℚ) *
        (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k)))) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk0 : k = 0
  · simp [hk0]
  · rw [ite_eq_right hk0, ite_eq_right hk0]
    have hfac : (n.factorial : ℚ) ≠ 0 := by positivity
    field_simp

lemma swap_and_apply_binomial (D n : ℕ) (coeff : ℕ → ℚ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (n.choose k : ℚ) *
        (∑ j ∈ Finset.range (D + 1), coeff j * (j : ℚ)^(n - k))) =
    ∑ j ∈ Finset.range (D + 1), coeff j * (((j : ℚ) + 1)^n - (j : ℚ)^n) := by
  conv_lhs =>
    arg 2
    ext k
    rw [show (if k = 0 then (0 : ℚ) else (n.choose k : ℚ) * ∑ j ∈ Finset.range (D + 1),
      coeff j * (j : ℚ)^(n - k))
           = ∑ j ∈ Finset.range (D + 1),
             (if k = 0 then 0 else (n.choose k : ℚ) * (coeff j * (j : ℚ)^(n - k)))
        by split_ifs with h
           · simp only [Finset.sum_const_zero]
           · rw [Finset.mul_sum]]
  rw [Finset.sum_comm]
  congr 1
  ext j
  conv_lhs =>
    arg 2
    ext k
    rw [show (if k = 0 then (0 : ℚ) else (n.choose k : ℚ) * (coeff j * (j : ℚ)^(n - k)))
           = coeff j * (if k = 0 then 0 else (n.choose k : ℚ) * (j : ℚ)^(n - k))
        by split_ifs <;> ring]
  rw [← Finset.mul_sum]
  rw [binomial_sum_minus_j_pow]

lemma cond_equiv (m n : ℕ) : (m ≤ n + 1) ↔ (m - 1 ≤ n) := by aesop

lemma index_eq (m n : ℕ) (hm : 0 < m) (h : m ≤ n + 1) : (n + 1) - m = n - (m - 1) := by omega

lemma coeff_X_pow_shift {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff (n + 1)) (PowerSeries.X ^ G.m * G.BSeries) =
    (PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  simp only [cond_equiv]
  split_ifs with h
  · rw [index_eq G.m n G.hm_pos (cond_equiv G.m n |>.mpr h)]
  · rfl

lemma gap_le_sup {S : NumericalSemigroup} (g : ℕ) (hg : g ∈ S.gaps) : g ≤ S.gaps.sup id :=
  Finset.le_sup (f := id) hg

lemma neg_neg_one_pow_eq (m : ℕ) : -((-1 : ℤ) ^ m) = (-1 : ℤ) ^ (m + 1) := by ring

lemma neg_one_pow_ne_zero' (m : ℕ) : ((-1 : ℤ) ^ (m + 1)) ≠ 0 := by exact Int.neg_one_pow_ne_zero

lemma binomial_sum_eq_add_pow (a b : ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a^k * b^(n - k) = (a + b)^n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma triple_sum_exchange (gaps : Finset ℕ) (degP : ℕ) (coeff : ℕ → ℚ) (n : ℕ) :
    ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1), ∑ r ∈ Finset.range (n + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    ∑ r ∈ Finset.range (n + 1), ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
  symm
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.sum_comm]

lemma factor_binomial_coeff_from_double_sum (gaps : Finset ℕ) (degP : ℕ) (coeff : ℕ → ℚ) (n r : ℕ) :
    ∑ g ∈ gaps, ∑ k ∈ Finset.range (degP + 1),
      (coeff k) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    (n.choose r : ℚ) * (∑ k ∈ Finset.range (degP + 1), (coeff k) * (k : ℚ)^r) *
      (∑ g ∈ gaps, (g : ℚ)^(n - r)) := by
  conv_rhs => rw [mul_assoc, Finset.sum_mul_sum]
  rw [Finset.mul_sum, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma sum_choose_mul_div_factorial_eq_sum_div_factorials (n : ℕ) (A B : ℕ → ℚ) :
    ∑ r ∈ Finset.range (n + 1), ((n.choose r : ℚ) * A r * B r) / (n.factorial : ℚ) =
    ∑ r ∈ Finset.range (n + 1), (A r / (r.factorial : ℚ)) * (B r / ((n - r).factorial : ℚ)) := by
  apply Finset.sum_congr rfl
  intro r hr
  have h₁ : r ≤ n := by simp only [Finset.mem_range] at hr; omega
  have h₃ : (n.choose r : ℚ) * (r.factorial : ℚ) * ((n - r).factorial : ℚ) = (n.factorial : ℚ) := by
    norm_cast
    rw [Nat.choose_mul_factorial_mul_factorial h₁]
  have h₄ : (n.factorial : ℚ) ≠ 0 := by positivity
  have h₅ : (r.factorial : ℚ) ≠ 0 := by positivity
  have h₆ : ((n - r).factorial : ℚ) ≠ 0 := by positivity
  field_simp
  linear_combination (A r * B r) * h₃

lemma gap_sum_to_coeff {S : NumericalSemigroup} (k : ℕ) :
    (∑ g ∈ S.gaps, (g : ℚ)^k) / (k.factorial : ℚ) =
    (PowerSeries.coeff k) (PowerSeries.mk fun j => ∑ g ∈ S.gaps,
      (g : ℚ)^j / (j.factorial : ℚ)) := by
  simp [PowerSeries.coeff_mk, Finset.sum_div]

lemma coeff_mul_range' {R : Type*} [Semiring R] (φ ψ : PowerSeries R) (n : ℕ) :
    (PowerSeries.coeff n) (φ * ψ) =
    ∑ r ∈ Finset.range (n + 1), (PowerSeries.coeff r) φ * (PowerSeries.coeff (n - r)) ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

lemma sum_factor_scalar' {α : Type*} (s : Finset α) (c : ℚ) (a b : α → ℚ) :
    ∑ r ∈ s, (c * a r) * b r = c * ∑ r ∈ s, a r * b r := by
  simp_rw [mul_assoc, Finset.mul_sum]

lemma bernoulli_coeff_to_T_delta {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p :
  ℕ) :
    (p.factorial : ℚ) * (PowerSeries.coeff (p + 1)) G.BSeries =
    (2 ^ (p + 1) : ℚ) / ((p : ℚ) + 1) * G.TDelta (p + 1) := by
  unfold NumericalSemigroupGenerators.TDelta
  ring_nf
  have h1 : (2 : ℚ)⁻¹ ^ p * 2 ^ p = 1 := by
    simp_all
  rw [mul_assoc, mul_assoc, mul_assoc, h1, mul_one]
  have h2 : (1 + (p : ℚ))⁻¹ * ((1 + p).factorial : ℚ) = (p.factorial : ℚ) := by
    rw [Nat.add_comm 1 p, Nat.factorial_succ, Nat.cast_mul, Nat.cast_succ]
    rw [add_comm]
    field_simp
  rw [h2]
  ring

lemma factorial_div_eq_choose_mul {p r : ℕ} (hr : r ≤ p) :
    (p.factorial : ℚ) / r.factorial = (p.choose r : ℚ) * (p - r).factorial := by
  have h_main : ((p.choose r : ℕ) : ℚ) * (r.factorial : ℚ) *
      ((p - r).factorial : ℚ) = (p.factorial : ℚ) := by
    norm_cast
    rw [← Nat.choose_mul_factorial_mul_factorial hr]
  have h_r_pos : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp [h_r_pos]
  linarith

lemma A_coeff_to_T_sigma {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p r : ℕ)
    (hr : r ≤ p) :
    ((p.factorial : ℚ) / (r.factorial : ℚ)) * (PowerSeries.coeff (p - r)) G.ASeries =
    (p.choose r : ℚ) * G.TSigma (p - r) := by
  have hfact := factorial_div_eq_choose_mul hr
  unfold NumericalSemigroupGenerators.TSigma
  rw [hfact]
  ring

lemma sum_A_coeff_eq_sum_T_sigma {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p :
  ℕ) :
    ∑ r ∈ Finset.range (p + 1),
      ((p.factorial : ℚ) / (r.factorial : ℚ)) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r =
    ∑ r ∈ Finset.range (p + 1),
      (p.choose r : ℚ) * G.TSigma (p - r) * S.gapPowerSum r := by
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.mem_range] at hr
  have hrp : r ≤ p := Nat.lt_succ_iff.mp hr
  rw [A_coeff_to_T_sigma G p r hrp]

end FelsConjectureProof
