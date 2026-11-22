/-
Copyright (c) 2026 Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Evan Chen, Kenny Lau, Ken Ono, Jujian Zhang
-/
module

public import Tengoku.Seed.NumberTheory.Bernoulli

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-! # Fel's Conjecture for Numerical Semigroups -/

@[expose] public section namespace Tengoku.LeanPool end Tengoku.LeanPool open Tengoku.LeanPool
/-- A *numerical semigroup*: an additive submonoid of `ℕ` with finite complement. -/
structure _root_.Tengoku.LeanPool.NumericalSemigroup where
  /-- The underlying set of natural numbers comprising the semigroup. -/
  carrier : Set ℕ
  zero_mem : 0 ∈ carrier
  add_mem : ∀ a b, a ∈ carrier → b ∈ carrier → a + b ∈ carrier
  finite_complement : (carrier)ᶜ.Finite

namespace Tengoku.LeanPool.NumericalSemigroup

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

/-- The coefficient of the Hilbert series at position n is 1 if n ∈ S.carrier, else 0.
@isnad1 id=eq.0h2v.s7.90b5a022d86e from=translated src=- shape=6c31f06e vocab=6b5a3c5d
-/
lemma hilbertSeries_coeff (S : NumericalSemigroup) (n : ℕ) :
    (PowerSeries.coeff n) S.hilbertSeries =
    if Classical.propDecidable (n ∈ S.carrier) |>.decide then 1 else 0 := by
  simp only [hilbertSeries, PowerSeries.coeff_mk]

/-- The coefficient of the gap polynomial (viewed as a power series) at position n is 1 if n ∈
  S.gaps, else 0.
@isnad1 id=eq.0h2v.s6.51a2a916ed82 from=translated src=- shape=42e179c0 vocab=c592298a
-/
lemma gapPolynomial_coeff (S : NumericalSemigroup) (n : ℕ) :
    (PowerSeries.coeff n) (S.gapPolynomial : PowerSeries ℚ) =
    if n ∈ S.gaps then 1 else 0 := by
  unfold gapPolynomial
  simp_all

/-- For any n, we have n ∈ S.gaps ↔ n ∉ S.carrier.
@isnad1 id=iff.0h2v.s4.cba90e668008 from=translated src=- shape=a40f9295 vocab=75100cec
-/
lemma mem_gaps_iff_not_mem_carrier (S : NumericalSemigroup) (n : ℕ) :
    n ∈ S.gaps ↔ n ∉ S.carrier := by
  simp only [gaps, Set.Finite.mem_toFinset, Set.mem_compl_iff]

/--
@isnad1 id=eq.0h2v.s7.bb0b56af0edc from=translated src=- shape=6b116de3 vocab=3ef88ec9
-/
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

/--
@isnad1 id=eq.0h1v.s5.a6b1a8489d8e from=translated src=- shape=958aec4d vocab=47e0fd12
-/
theorem semigroupGapDecomposition (S : NumericalSemigroup) :
    S.hilbertSeries + (S.gapPolynomial : PowerSeries ℚ) = PowerSeries.mk (1 : ℕ → ℚ) := by
  apply PowerSeries.ext
  exact semigroupGapDecomposition_aux S

end Tengoku.LeanPool.NumericalSemigroup

/-- A choice of generators for a numerical semigroup `S`: positive integers `d₁, …,
  d_m` with `gcd = 1` whose nonneg-integer combinations recover `S.carrier`. -/
structure _root_.Tengoku.LeanPool.NumericalSemigroupGenerators (S : NumericalSemigroup) where
  /-- The number of generators (embedding dimension of `S`). -/
  m : ℕ                           -- number of generators (embedding dimension)
  hm_pos : 0 < m                  -- at least one generator
  /-- The chosen generators `d₁, …, d_m`. -/
  d : Fin m → ℕ                   -- the generators d_1, ..., d_m
  hd_pos : ∀ i, 0 < d i           -- each generator is positive
  hgcd : (Finset.univ.image d).gcd id = 1  -- gcd of generators is 1
  generates : S.carrier = {n : ℕ | ∃ (c : Fin m → ℕ), n = ∑ i, c i * d i}

namespace Tengoku.LeanPool.NumericalSemigroupGenerators

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

/--
@isnad1 id=eq.0h3v.s8.c758f9920c2a from=translated src=- shape=8fd17ab5 vocab=98838e73
-/
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

/--
@isnad1 id=eq.1h3v.s6.349f576b0c3d from=translated src=- shape=9f81b6a9 vocab=b500f87f
-/
lemma hilbertNumerator_coeff_lt {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ)
    (hn : n < G.hilbertNumeratorDegBound) :
    G.hilbertNumerator.coeff n =
      (∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
       (∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g)) := by
  unfold hilbertNumerator
  simp only
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  simp_all

/--
@isnad1 id=eq.0h3v.s8.b40abb2ca721 from=translated src=- shape=274a2830 vocab=7de7f359
-/
lemma lhs_eq_sum_over_carrier {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
  :
    ∑ k ∈ Finset.range (n + 1),
      (if (Classical.propDecidable (k ∈ S.carrier)).decide then 1 else 0) *
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => (Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) := by
  rw [Finset.sum_filter]
  simp_all

/--
@isnad1 id=eq.0h3v.s8.728af33c09e4 from=translated src=- shape=defdc0fc vocab=09a8c50b
-/
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

/--
@isnad1 id=eq.0h2v.s6.32748b810946 from=translated src=- shape=136e6ac8 vocab=df5f3965
-/
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

/--
@isnad1 id=eq.0h3v.s8.85571dc658b0 from=translated src=- shape=14924db2 vocab=0be100d6
-/
lemma carrier_sum_eq_full_minus_gaps {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
  (n : ℕ) :
    ∑ k ∈ (Finset.range (n + 1)).filter (fun k => (Classical.propDecidable (k ∈ S.carrier)).decide),
      (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) =
    ∑ k ∈ Finset.range (n + 1), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - k)) -
    ∑ g ∈ S.gaps.filter (· ≤ n), (Int.castRingHom ℚ) (G.productPolynomial.coeff (n - g)) := by
  have hpart := partition_sum G n
  have hfilter := filter_not_carrier_eq_gaps (S := S) n
  simp_all

/--
@isnad1 id=eq.0h2v.s5.7cede44bba02 from=translated src=- shape=531a709e vocab=0c092b01
-/
lemma sum_range_reindex (f : ℕ → ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), f (n - k) = ∑ j ∈ Finset.range (n + 1), f j := by
  apply Finset.sum_bij' (fun k _ => n - k) (fun k _ => n - k)
  · intros k hk; rw [Finset.mem_range] at hk ⊢; omega
  · intros k hk; rw [Finset.mem_range] at hk ⊢; omega
  · intros k hk; rw [Finset.mem_range] at hk; omega
  · intros k hk; rw [Finset.mem_range] at hk; omega
  · intros k _; rfl

/--
@isnad1 id=eq.1h3v.s8.79440183e194 from=translated src=- shape=8ddfe03d vocab=21f9532d
-/
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

/--
@isnad1 id=eq.0h3v.s8.419501a56892 from=translated src=- shape=1cc6ee06 vocab=3e0a0752
-/
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

/--
@isnad1 id=eq.0h2v.s4.a39c6317ed53 from=translated src=- shape=d9fc4a15 vocab=8f0846f4
-/
lemma productPolynomial_eval_one {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    Polynomial.eval 1 G.productPolynomial = 0 := by
  unfold productPolynomial
  rw [Polynomial.eval_prod]
  apply Finset.prod_eq_zero (i := ⟨0, G.hm_pos⟩) (Finset.mem_univ _)
  simp

/--
@isnad1 id=eq.0h2v.s5.77b77c7815d7 from=translated src=- shape=b2406632 vocab=743a1a4d
-/
lemma sum_coeff_eq_eval_one {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1), G.productPolynomial.coeff k =
    Polynomial.eval 1 G.productPolynomial := by
  have h₁ : ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
    G.productPolynomial.coeff k = G.productPolynomial.eval 1 := by
    rw [Polynomial.eval_eq_sum_range]
    simp [add_comm]
  rw [h₁]

/--
@isnad1 id=eq.2h4v.s6.f97d9015a623 from=translated src=- shape=95889140 vocab=9fb737ed
-/
lemma coeff_Ico_eq_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n : ℕ) (_hn : G.productPolynomial.natDegree + 1 ≤ n)
    (k : ℕ) (hk : k ∈ Finset.Ico (G.productPolynomial.natDegree + 1) (n + 1)) :
    G.productPolynomial.coeff k = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  simp_all

/--
@isnad1 id=eq.1h3v.s6.55c01e61bc56 from=translated src=- shape=5ae55778 vocab=679c2deb
-/
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

/--
@isnad1 id=eq.1h3v.s5.73de22b8ad29 from=translated src=- shape=1c356c94 vocab=a6298def
-/
lemma first_sum_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    ∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k = 0 := by
  have h1 : G.productPolynomial.natDegree + 1 ≤ n := by
    unfold hilbertNumeratorDegBound at hn
    omega
  rw [sum_coeff_large_eq_sum_coeff_deg G n h1]
  rw [sum_coeff_eq_eval_one G]
  exact productPolynomial_eval_one G

/--
@isnad1 id=eq.3h4v.s5.294881be17ff from=translated src=- shape=a83bb7b9 vocab=42c0a1f2
-/
lemma coeff_n_minus_gap_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (n g : ℕ) (hn : n ≥ G.hilbertNumeratorDegBound) (hg : g ∈ S.gaps) (hgn : g ≤ n) :
    G.productPolynomial.coeff (n - g) = 0 := by
  apply Polynomial.coeff_eq_zero_of_natDegree_lt
  have hge : g ≤ S.gaps.sup id := Finset.le_sup (f := id) hg
  have hn' : n ≥ G.productPolynomial.natDegree + S.gaps.sup id + 1 := hn
  omega

/--
@isnad1 id=eq.1h3v.s5.1cb7cf292a0c from=translated src=- shape=65ed476a vocab=c6fde14a
-/
lemma second_sum_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    ∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g) = 0 := by
  apply Finset.sum_eq_zero
  intro g hg
  rw [Finset.mem_filter] at hg
  exact coeff_n_minus_gap_zero G n g hn hg.1 hg.2

/--
@isnad1 id=eq.1h3v.s6.498dbc8be08d from=translated src=- shape=85943a84 vocab=b51c13a5
-/
lemma rhs_zero_of_large {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
    (hn : n ≥ G.hilbertNumeratorDegBound) :
    (∑ k ∈ Finset.range (n + 1), G.productPolynomial.coeff k) -
     (∑ g ∈ S.gaps.filter (· ≤ n), G.productPolynomial.coeff (n - g)) = 0 := by
  rw [first_sum_zero G n hn, second_sum_zero G n hn]
  ring

/--
@isnad1 id=eq.1h3v.s7.aed44fdfe1f3 from=translated src=- shape=e3631f52 vocab=2c20b8dc
-/
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

end Tengoku.LeanPool.NumericalSemigroupGenerators

namespace FelsConjectureProof

/--
@isnad1 id=lt.0h2v.s4.4a20b8593e0a from=translated src=- shape=9363a417 vocab=d8704a06
-/
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

/--
@isnad1 id=eq.1h2v.s5.9ac8a037383a from=translated src=- shape=145801d5 vocab=8a39cd7a
-/
lemma choose_mul_sub_factorial_eq_div (n r : ℕ) (hr : r ≤ n) :
    ((n.choose r : ℚ) * ((n - r).factorial : ℚ)) = (n.factorial : ℚ) / (r.factorial : ℚ) := by
  have h₁ : (n.choose r : ℚ) * (r.factorial : ℚ) * ((n - r).factorial : ℚ) = (n.factorial : ℚ) := by
    norm_cast
    rw [← Nat.choose_mul_factorial_mul_factorial hr]
  have h₂ : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp [h₂]
  linarith

/--
@isnad1 id=eq.1h4v.s7.03a6ce9137f1 from=translated src=- shape=16f5ad22 vocab=02dc29ad
-/
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

/--
@isnad1 id=eq.0h4v.s7.385b83f12b84 from=translated src=- shape=984d57f2 vocab=610fec55
-/
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

/--
@isnad1 id=eq.1h5v.s7.0b32f389d9e3 from=translated src=- shape=e024177d vocab=0034bd5b
-/
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

/--
@isnad1 id=eq.0h3v.s8.c2c020899aa5 from=translated src=- shape=ac29cbfd vocab=7e1c8ebc
-/
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

/--
@isnad1 id=eq.0h3v.s7.0ec690017561 from=translated src=- shape=196d419c vocab=2671b286
-/
lemma hilbertNumerator_exp_sub_coeff {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) (hilbertNumeratorExpSub G) =
      (∑ j ∈ Finset.range G.hilbertNumeratorDegBound,
        (G.hilbertNumerator.coeff j : ℚ) * (j : ℚ)^n) /
        (n.factorial : ℚ) := by
  simp only [hilbertNumeratorExpSub, PowerSeries.coeff_mk]

/--
@isnad1 id=eq.1h3v.s6.108315622d60 from=translated src=- shape=99c9472e vocab=af451798
-/
lemma alternatingPowerSum_eq_neg_sum {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) (hn : 1 ≤ n) :
    G.alternatingPowerSum n =
      -(∑ j ∈ Finset.range G.hilbertNumeratorDegBound,
        (G.hilbertNumerator.coeff j : ℚ) * (j : ℚ)^n) := by
  unfold NumericalSemigroupGenerators.alternatingPowerSum
    NumericalSemigroupGenerators.numeratorCoeff
  have hn_ne : n ≠ 0 := Nat.one_le_iff_ne_zero.mp hn
  have h0_pow : (0 : ℚ) ^ n = 0 := zero_pow hn_ne
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  simp_all

/--
@isnad1 id=eq.1h3v.s6.4f37f9bc5a40 from=translated src=- shape=e93cc281 vocab=19b58072
-/
lemma alternatingPowerSum_eq_coeff_hilbert_exp {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) (hn : 1 ≤ n) :
    G.alternatingPowerSum n =
      -((n.factorial : ℚ) * (PowerSeries.coeff n) (hilbertNumeratorExpSub G)) := by
  rw [hilbertNumerator_exp_sub_coeff, alternatingPowerSum_eq_neg_sum G n hn]
  congr 1
  have hfact : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

/--
@isnad1 id=eq.0h3v.s8.1f386f2b746b from=translated src=- shape=69a01a85 vocab=e523831b
-/
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

/--
@isnad1 id=eq.0h3v.s8.a1bc673c46bc from=translated src=- shape=e2b9ab5d vocab=b394cf7e
-/
lemma coeff_A_mul_E {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    (PowerSeries.coeff p) (G.ASeries * PowerSeries.mk fun n => ∑ g ∈ S.gaps,
      (g : ℚ)^n / (n.factorial : ℚ)) =
    ∑ r ∈ Finset.range (p + 1), (PowerSeries.coeff (p - r)) G.ASeries * (∑ g ∈ S.gaps,
      (g : ℚ)^r / (r.factorial : ℚ)) := by
  rw [PowerSeries.coeff_mul]
  refine Eq.symm (Finset.sum_bij (fun (r : ℕ) _ => (⟨p - r, r⟩ : ℕ × ℕ)) ?_ ?_ ?_ ?_)
  · simp_all
  · simp_all
  · rintro ⟨a, b⟩ hab
    rw [Finset.mem_antidiagonal] at hab
    refine ⟨b, Finset.mem_range.mpr (by omega), ?_⟩
    simp only [Prod.mk.injEq, and_true]
    omega
  · simp_all

/--
@isnad1 id=eq.0h3v.s8.0d9c68520a92 from=translated src=- shape=14d70a55 vocab=dee69829
-/
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

/--
@isnad1 id=eq.0h3v.s8.4faad2593296 from=translated src=- shape=a19e0c2a vocab=9d90c0a6
-/
lemma gap_term_coeff_shift {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    (PowerSeries.coeff (G.m + p)) (PowerSeries.X ^ G.m * G.ASeries *
       PowerSeries.mk fun n => ∑ g ∈ S.gaps, (g : ℚ)^n / (n.factorial : ℚ)) =
    ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
      (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ) := by
  have h1 : PowerSeries.X ^ G.m * G.ASeries *
            (PowerSeries.mk fun n => ∑ g ∈ S.gaps, (g : ℚ)^n / (n.factorial : ℚ)) =
            PowerSeries.X ^ G.m * (G.ASeries *
            (PowerSeries.mk fun n => ∑ g ∈ S.gaps, (g : ℚ)^n / (n.factorial : ℚ))) := by ring
  rw [h1]
  rw [add_comm]
  rw [PowerSeries.coeff_X_pow_mul]
  rw [coeff_A_mul_E]
  exact sum_swap_gaps_range G p

/--
@isnad1 id=eq.0h3v.s8.0491354533a6 from=translated src=- shape=97850161 vocab=9a60b9ed
-/
lemma Q_exp_coeff_at_m_plus_p {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ)
  :
    (PowerSeries.coeff (G.m + p)) (QExpSeries G) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) *
      ((PowerSeries.coeff (p + 1)) G.BSeries +
       ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
         (PowerSeries.coeff (p - r)) G.ASeries * (g : ℚ)^r / (r.factorial : ℚ)) := by
  unfold QExpSeries
  rw [PowerSeries.coeff_smul]
  rw [map_add]
  rw [B_term_coeff_shift, gap_term_coeff_shift]
  simp only [smul_eq_mul]

/--
@isnad1 id=eq.0h3v.s8.5232c57cd811 from=translated src=- shape=138c0013 vocab=65392ec7
-/
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

/--
@isnad1 id=eq.0h3v.s8.d7ae765b794e from=translated src=- shape=4c658e5c vocab=8b4dc329
-/
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

/--
@isnad1 id=eq.0h3v.s8.2fea4e41f335 from=translated src=- shape=0ad54612 vocab=8b4dc329
-/
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

/--
@isnad1 id=eq.0h2v.s7.27684ca9480b from=translated src=- shape=f872e4e0 vocab=8f1196f9
-/
lemma exp_poly_sub_coeff (P : Polynomial ℤ) (n : ℕ) :
    (PowerSeries.coeff n) (expPolySub P) =
    (∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℚ) * (j : ℚ)^n) / (n.factorial : ℚ) := by
  simp only [expPolySub, PowerSeries.coeff_mk]

/--
@isnad1 id=eq.1h3v.s6.9e46729a6b04 from=translated src=- shape=f35da458 vocab=da656500
-/
lemma exp_poly_sub_sum_extend (P : Polynomial ℤ) (k : ℕ) (n : ℕ) (hk : P.natDegree + 1 ≤ k) :
    ∑ j ∈ Finset.range (P.natDegree + 1), (P.coeff j : ℚ) * (j : ℚ)^n =
    ∑ j ∈ Finset.range k, (P.coeff j : ℚ) * (j : ℚ)^n := by
  apply Finset.sum_subset (Finset.range_mono hk)
  intro j _ hj'
  simp only [Finset.mem_range, not_lt] at hj'
  rw [show (P.coeff j : ℚ) = 0 by
    exact_mod_cast Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  ring

/--
@isnad1 id=le.0h2v.s4.8b857b5ca149 from=translated src=- shape=be7d486e vocab=1a01ec34
-/
lemma hilbertNumerator_natDegree_le_pred_bound {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    G.hilbertNumerator.natDegree ≤ G.hilbertNumeratorDegBound - 1 := by
  unfold NumericalSemigroupGenerators.hilbertNumerator
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro n hn
  calc ((Polynomial.monomial n) _).natDegree
      ≤ n := Polynomial.natDegree_monomial_le _
    _ ≤ G.hilbertNumeratorDegBound - 1 := by
        rw [Finset.mem_range] at hn
        omega

/--
@isnad1 id=lt.0h2v.s4.d71b7cbcb17c from=translated src=- shape=9363a417 vocab=d2f52f71
-/
lemma hilbertNumeratorDegBound_pos {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    0 < G.hilbertNumeratorDegBound := by
  unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound
  omega

/--
@isnad1 id=le.0h2v.s4.e8a8bb7d9264 from=translated src=- shape=fc498f5f vocab=52751f23
-/
lemma hilbertNumerator_natDegree_lt_bound {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    G.hilbertNumerator.natDegree + 1 ≤ G.hilbertNumeratorDegBound := by
  have h := hilbertNumerator_natDegree_le_pred_bound G
  have hpos := hilbertNumeratorDegBound_pos G
  omega

/--
@isnad1 id=eq.0h2v.s3.99a57f93eadc from=translated src=- shape=6579c946 vocab=2f282dd5
-/
lemma hilbertNumerator_exp_sub_eq_exp_poly_sub {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    hilbertNumeratorExpSub G = expPolySub G.hilbertNumerator := by
  apply PowerSeries.ext
  intro n
  simp only [hilbertNumeratorExpSub, expPolySub, PowerSeries.coeff_mk]
  congr 1
  exact (exp_poly_sub_sum_extend G.hilbertNumerator G.hilbertNumeratorDegBound n
    (hilbertNumerator_natDegree_lt_bound G)).symm

/--
@isnad1 id=eq.0h3v.s8.bb3eeb490295 from=translated src=- shape=d97aaa54 vocab=3cffcc6e
-/
lemma Q_exp_series_coeff {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) (QExpSeries G) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) *
      ((PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) +
       (PowerSeries.coeff n) (PowerSeries.X ^ G.m * G.ASeries *
         PowerSeries.mk fun k => ∑ g ∈ S.gaps, (g : ℚ)^k / (k.factorial : ℚ))) := by
  simp only [QExpSeries, PowerSeries.coeff_smul, smul_eq_mul, map_add]

/--
@isnad1 id=lt.1h3v.s5.b9a356ee18aa from=translated src=- shape=906b1e80 vocab=9f356ad8
-/
lemma j_lt_bound_of_mem_range_natDegree {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (j : ℕ)
    (hj : j ∈ Finset.range (G.hilbertNumerator.natDegree + 1)) :
    j < G.hilbertNumeratorDegBound := by
  have hj_lt := Finset.mem_range.mp hj
  exact Nat.lt_of_lt_of_le hj_lt (hilbertNumerator_natDegree_lt_bound G)

/--
@isnad1 id=eq.0h3v.s7.031070b71c61 from=translated src=- shape=37f984c7 vocab=a28e019a
-/
lemma hilbert_sum_decomposition_natDegree {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (G.hilbertNumerator.coeff j : ℚ) * (j : ℚ)^n =
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) * (j : ℚ)^n) -
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hj_lt : j < G.hilbertNumeratorDegBound := j_lt_bound_of_mem_range_natDegree G j hj
  have coeff_eq := NumericalSemigroupGenerators.hilbertNumerator_coeff_lt G j hj_lt
  simp only [coeff_eq, Int.cast_sub, Int.cast_sum]
  ring

/--
@isnad1 id=eq.1h3v.s5.2035ea836875 from=translated src=- shape=d186cb7e vocab=c2ae3290
-/
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

/--
@isnad1 id=eq.1h1v.s6.03d4e7ba8a0f from=translated src=- shape=3f34287d vocab=a5cb0db7
-/
lemma leadingCoeff_one_sub_X_pow (k : ℕ) (hk : 0 < k) :
    (1 - Polynomial.X ^ k : Polynomial ℤ).leadingCoeff = -1 := by
  have h₁ : (1 - Polynomial.X ^ k : Polynomial ℤ) = -(Polynomial.X ^ k - 1 : Polynomial ℤ) :=
    by ring
  have h₂ : (Polynomial.X ^ k - 1 : Polynomial ℤ).Monic := by
    apply Polynomial.monic_X_pow_sub_C
    omega
  simp only [h₁, Polynomial.leadingCoeff_neg, h₂.leadingCoeff]

/--
@isnad1 id=eq.0h2v.s5.194ddd5b86f1 from=translated src=- shape=6bcc889b vocab=7a17d725
-/
lemma productPolynomial_leadingCoeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    G.productPolynomial.leadingCoeff = (-1 : ℤ) ^ G.m := by
  unfold NumericalSemigroupGenerators.productPolynomial
  rw [Polynomial.leadingCoeff_prod]
  have h : ∀ i : Fin G.m, (1 - Polynomial.X ^ G.d i : Polynomial ℤ).leadingCoeff = -1 := by
    intro i
    exact leadingCoeff_one_sub_X_pow (G.d i) (G.hd_pos i)
  simpa only [h] using Fin.prod_const G.m (-1 : ℤ)

/--
@isnad1 id=le.1h2v.s4.2aa78e571884 from=translated src=- shape=036f639d vocab=46222de4
-/
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

/--
@isnad1 id=eq.0h3v.s7.06bc3729c8d9 from=translated src=- shape=f22bd5e7 vocab=48c1ea53
-/
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

/--
@isnad1 id=eq.1h3v.s7.0d4402207ed1 from=translated src=- shape=07e68b36 vocab=def535b8
-/
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

/--
@isnad1 id=eq.2h3v.s5.00f77b2d794d from=translated src=- shape=7871c63f vocab=13f34666
-/
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

/--
@isnad1 id=eq.3h3v.s6.0c6aff19c442 from=translated src=- shape=581d3a6b vocab=aed78cab
-/
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

/--
@isnad1 id=eq.0h2v.s6.1881f5b03e0b from=translated src=- shape=c99120ea vocab=bc78f71b
-/
lemma coeff_eq_partial_sum_diff (P : Polynomial ℤ) (n : ℕ) :
    (P.coeff n : ℚ) = (∑ k ∈ Finset.range (n + 1), (P.coeff k : ℚ)) -
                      (∑ k ∈ Finset.range n, (P.coeff k : ℚ)) := by
  have h_sum_split : (∑ k ∈ Finset.range (n + 1), (P.coeff k : ℚ)) =
      (∑ k ∈ Finset.range n, (P.coeff k : ℚ)) + (P.coeff n : ℚ) := by
    rw [Finset.sum_range_succ]
  simp_all

/--
@isnad1 id=eq.2h2v.s6.0d11d2c708f4 from=translated src=- shape=f639c96b vocab=a86cb6ce
-/
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

/--
@isnad1 id=eq.4h3v.s6.519cfa0f0005 from=translated src=- shape=4d76e712 vocab=0b443cb4
-/
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

/--
@isnad1 id=eq.2h3v.s6.56669eef31f1 from=translated src=- shape=c5641f0d vocab=76454722
-/
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

/--
@isnad1 id=eq.2h3v.s7.e3e60cd5dc3d from=translated src=- shape=07193784 vocab=99b38731
-/
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

/--
@isnad1 id=eq.1h3v.s7.ce078abf7a1e from=translated src=- shape=624168e5 vocab=def535b8
-/
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

/--
@isnad1 id=eq.0h3v.s7.806e83648db7 from=translated src=- shape=84f3f0c7 vocab=acac346c
-/
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

/--
@isnad1 id=eq.0h3v.s7.944ac48f42d0 from=translated src=- shape=ee5f4463 vocab=536fbe52
-/
lemma partialSumGenFunc_coeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
  :
    (PowerSeries.coeff n) (partialSumGenFunc G) =
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff k : ℚ)) * (j : ℚ)^n) / (n.factorial : ℚ) := by
  simp only [partialSumGenFunc, PowerSeries.coeff_mk]

/--
@isnad1 id=eq.0h0v.s4.270245974fb8 from=translated src=- shape=6b6a19fe vocab=892ef813
-/
lemma exp_poly_sub_one : expPolySub 1 = 1 := by
  ext n
  simp only [expPolySub, PowerSeries.coeff_mk, PowerSeries.coeff_one]
  simp only [Polynomial.natDegree_one, Polynomial.coeff_one]
  rw [Finset.range_one, Finset.sum_singleton]
  simp only [↓reduceIte, CharP.cast_eq_zero]
  cases n with
  | zero => simp
  | succ n => simp [zero_pow (Nat.succ_ne_zero n)]

/--
@isnad1 id=eq.0h3v.s8.804d11ca7192 from=translated src=- shape=d990754c vocab=325726d0
-/
lemma coeff_mul_expand (P Q : Polynomial ℤ) (n : ℕ) :
    (PowerSeries.coeff n) (expPolySub P * expPolySub Q) =
    ∑ k ∈ Finset.range (n + 1),
      ((∑ a ∈ Finset.range (P.natDegree + 1), (P.coeff a : ℚ) * (a : ℚ)^k) / k.factorial) *
      ((∑ b ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff b : ℚ) * (b : ℚ)^(n - k)) / (n - k).factorial) := by
  rw [PowerSeries.coeff_mul]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  congr 1
  ext k
  simp only [expPolySub, PowerSeries.coeff_mk]

/--
@isnad1 id=eq.0h3v.s8.3fd1403dc20e from=translated src=- shape=6bb90906 vocab=683af083
-/
lemma lhs_to_triple_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ((∑ a ∈ Finset.range (P.natDegree + 1), (P.coeff a : ℚ) * (a : ℚ)^k) / k.factorial) *
      ((∑ b ∈ Finset.range (Q.natDegree + 1),
        (Q.coeff b : ℚ) * (b : ℚ)^(n - k)) / (n - k).factorial) =
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) / (k.factorial *
            (n - k).factorial) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [div_mul_div_comm, Finset.sum_mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro b _
  ring

/--
@isnad1 id=eq.1h6v.s7.b11d7388b999 from=translated src=- shape=b17d2e98 vocab=e75e9be8
-/
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

/--
@isnad1 id=le.0h1v.s6.c7cdc566bbbc from=translated src=- shape=66112e13 vocab=6d6033e0
-/
lemma natDegree_one_sub_X_pow_le (k : ℕ) :
    (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≤ k := by
  refine Polynomial.natDegree_sub_le _ _ |>.trans ?_
  simp [Polynomial.natDegree_pow, Polynomial.natDegree_X]

/--
@isnad1 id=eq.1h1v.s6.2648bdceba45 from=translated src=- shape=36c2c909 vocab=b4578a36
-/
lemma sum_coeff_one_sub_X_pow (k : ℕ) (_hk : 0 < k) :
    ∑ j ∈ Finset.range (k + 1), ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff j : ℚ) = 0 := by
  aesop

/--
@isnad1 id=eq.1h1v.s7.fc94b9d33571 from=translated src=- shape=a6b42620 vocab=d3a58cc7
-/
lemma exp_poly_sub_one_sub_X_pow_coeff_zero (k : ℕ) (hk : 0 < k) :
    (PowerSeries.coeff 0) (expPolySub (1 - Polynomial.X ^ k)) = 0 := by
  unfold expPolySub
  rw [PowerSeries.coeff_mk]
  simp only [pow_zero, mul_one, Nat.factorial_zero, Nat.cast_one, div_one]
  have h_deg : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≤ k := natDegree_one_sub_X_pow_le k
  have h_sum := sum_coeff_one_sub_X_pow k hk
  convert h_sum using 1
  apply Finset.sum_subset
  · simp_all
  · intro j hj hj_not
    simp only [Finset.mem_range] at hj hj_not
    have : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree < j := by omega
    simpa only [Int.cast_eq_zero] using Polynomial.coeff_eq_zero_of_natDegree_lt this

/--
@isnad1 id=eq.1h1v.s6.219346c2fa28 from=translated src=- shape=ff64396d vocab=17804858
-/
lemma natDegree_one_sub_X_pow_eq (k : ℕ) (hk : 0 < k) :
    (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree = k := by
  have h₁ : (1 - Polynomial.X ^ k : Polynomial ℤ).natDegree ≤ k := natDegree_one_sub_X_pow_le k
  have h₃ : (1 - Polynomial.X ^ k : Polynomial ℤ).coeff k = -1 := by
    simp [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow]
    cases k <;> simp_all
  refine le_antisymm h₁ (Polynomial.le_natDegree_of_ne_zero ?_)
  simp_all

/--
@isnad1 id=eq.4h3v.s7.04c4bd213310 from=translated src=- shape=cad7949e vocab=2aa419b4
-/
lemma one_sub_X_pow_term_eq_zero (k n j : ℕ) (_hk : 0 < k) (hn : 1 ≤ n)
    (_hj_mem : j ∈ Finset.range (k + 1)) (hj_ne : j ≠ k) :
    ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff j : ℚ) * (j : ℚ)^n = 0 := by
  by_cases h : j = 0
  · subst h
    simp [zero_pow (by omega : n ≠ 0)]
  · have h₈ : (1 - Polynomial.X ^ k : Polynomial ℤ).coeff j = 0 := by
      simp only [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow,
        ite_eq_right h, ite_eq_right hj_ne, sub_self]
    simp_all

/--
@isnad1 id=eq.1h2v.s6.d855cb61bd19 from=translated src=- shape=b8889749 vocab=fe015d29
-/
lemma one_sub_X_pow_term_at_k (k n : ℕ) (hk : 0 < k) :
    ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff k : ℚ) * (k : ℚ)^n = -((k : ℚ)^n) := by
  have h₁ : (1 - Polynomial.X ^ k : Polynomial ℤ).coeff k = (-1 : ℤ) := by
    simp [Polynomial.coeff_sub, Polynomial.coeff_one, Polynomial.coeff_X_pow]
    cases k <;> simp_all
  simp_all

/--
@isnad1 id=eq.2h2v.s7.4d954482497c from=translated src=- shape=bceb8d48 vocab=30a9ff8e
-/
lemma one_sub_X_pow_sum_eq (k n : ℕ) (hk : 0 < k) (hn : 1 ≤ n) :
    ∑ j ∈ Finset.range ((1 - Polynomial.X ^ k : Polynomial ℤ).natDegree + 1),
      ((1 - Polynomial.X ^ k : Polynomial ℤ).coeff j : ℚ) * (j : ℚ)^n = -((k : ℚ)^n) := by
  rw [natDegree_one_sub_X_pow_eq k hk]
  have hk_mem : k ∈ Finset.range (k + 1) := Finset.mem_range.mpr (Nat.lt_succ_self k)
  rw [Finset.sum_eq_single_of_mem k hk_mem]
  · exact one_sub_X_pow_term_at_k k n hk
  · intro j hj_mem hj_ne
    exact one_sub_X_pow_term_eq_zero k n j hk hn hj_mem hj_ne

/--
@isnad1 id=eq.2h2v.s7.3b073f3d0572 from=translated src=- shape=53451e71 vocab=d529115f
-/
lemma exp_poly_sub_one_sub_X_pow_coeff_pos (k n : ℕ) (hk : 0 < k) (hn : 1 ≤ n) :
    (PowerSeries.coeff n) (expPolySub (1 -
      Polynomial.X ^ k)) = -((k : ℚ)^n) / (n.factorial : ℚ) := by
  rw [exp_poly_sub_coeff]
  rw [one_sub_X_pow_sum_eq k n hk hn]

/--
@isnad1 id=eq.0h3v.s7.419cbdde2f92 from=translated src=- shape=20da4b37 vocab=30e9287d
-/
lemma rhs_coeff_zero {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (i : Fin G.m) :
    (PowerSeries.coeff 0) (-(G.d i : ℚ) • (PowerSeries.X * G.scaledExpFactor i)) = 0 := by
  simp_all

/--
@isnad1 id=eq.1h4v.s7.f1adff990a87 from=translated src=- shape=1ab4e719 vocab=f24f1cfd
-/
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

/--
@isnad1 id=eq.0h3v.s7.6d16b71357b1 from=translated src=- shape=2a182c63 vocab=8e14138d
-/
lemma single_factor_exp_transform {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (i : Fin G.m) :
    expPolySub (1 - Polynomial.X ^ (G.d i)) =
    -(G.d i : ℚ) • (PowerSeries.X * G.scaledExpFactor i) := by
  apply PowerSeries.ext
  intro n
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [exp_poly_sub_one_sub_X_pow_coeff_zero (G.d i) (G.hd_pos i)]
    rw [rhs_coeff_zero G i]
  · rw [exp_poly_sub_one_sub_X_pow_coeff_pos (G.d i) n (G.hd_pos i) hn]
    rw [rhs_coeff_pos G i n hn]

/--
@isnad1 id=eq.0h3v.s7.952c3ca3e0b9 from=translated src=- shape=85298730 vocab=2faa4be3
-/
lemma prod_smul_eq_smul_prod (m : ℕ) (c : Fin m → ℚ) (f : Fin m → PowerSeries ℚ) :
    ∏ i : Fin m, (c i • f i) = (∏ i : Fin m, c i) • (∏ i : Fin m, f i) := by
  simp only [MvPowerSeries.smul_eq_C_mul]
  rw [Finset.prod_mul_distrib]
  rw [← map_prod]

/--
@isnad1 id=eq.0h2v.s6.1dd0ef59ed12 from=translated src=- shape=4779e612 vocab=337bd899
-/
lemma prod_X_mul_eq_X_pow_mul (m : ℕ) (f : Fin m → PowerSeries ℚ) :
    ∏ i : Fin m, (PowerSeries.X * f i) = PowerSeries.X ^ m * ∏ i : Fin m, f i := by
  simp_rw [Finset.prod_mul_distrib, Fin.prod_const]

/--
@isnad1 id=eq.0h2v.s6.6a8dec7bca94 from=translated src=- shape=ed5e4dd6 vocab=225b6038
-/
lemma prod_neg_eq_neg_one_pow_mul (m : ℕ) (c : Fin m → ℚ) :
    ∏ i : Fin m, (-c i) = (-1 : ℚ) ^ m * ∏ i : Fin m, c i := by
  rw [show (fun i => -c i) = fun i => (-1 : ℚ) * c i from by funext i; ring,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/--
@isnad1 id=eq.0h2v.s7.9ba8a14adcbf from=translated src=- shape=7357e2f1 vocab=9a95a289
-/
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

/--
@isnad1 id=eq.0h3v.s8.486c465ea18e from=translated src=- shape=8f9e5db8 vocab=b855fe45
-/
lemma triple_sum_factorial_to_choose (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) / (k.factorial *
            (n - k).factorial) =
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) *
            ((n.choose k : ℚ) / (n.factorial : ℚ)) := by
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  exact term_factorial_to_choose (P.coeff a : ℚ) (Q.coeff b : ℚ) a b k n hkn

/--
@isnad1 id=eq.0h3v.s8.71a7cd1f6ecc from=translated src=- shape=91086323 vocab=b855fe45
-/
lemma factor_out_factorial (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) *
            ((n.choose k : ℚ) / (n.factorial : ℚ)) =
    (1 / n.factorial) * ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/--
@isnad1 id=eq.0h3v.s8.dfa5bf405695 from=translated src=- shape=5dcdb662 vocab=bfb0c785
-/
lemma sum_rearrange (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      ∑ a ∈ Finset.range (P.natDegree + 1),
        ∑ b ∈ Finset.range (Q.natDegree + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (n + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.sum_comm]

/--
@isnad1 id=eq.0h3v.s8.ee257831031c from=translated src=- shape=680e5201 vocab=bfb0c785
-/
lemma factor_coeffs_from_inner_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        ∑ k ∈ Finset.range (n + 1),
          (P.coeff a : ℚ) * (Q.coeff b : ℚ) * (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/--
@isnad1 id=eq.0h3v.s6.e216879cd1a4 from=translated src=- shape=e2f54934 vocab=7aa6ef92
-/
lemma binomial_sum_eq_power (a b n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) = ((a : ℚ) + b)^n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  simp only [mul_comm ((n.choose k : ℚ)) _]
  ring

/--
@isnad1 id=eq.0h3v.s8.702645a7fad9 from=translated src=- shape=00730553 vocab=bfb0c785
-/
lemma apply_binomial_to_inner_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) *
        ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * (a : ℚ)^k * (b : ℚ)^(n - k) =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  rw [binomial_sum_eq_power]

/--
@isnad1 id=eq.0h3v.s7.987e6b3f60fa from=translated src=- shape=8ab2300c vocab=8f1196f9
-/
lemma exp_poly_sub_mul_coeff_eq (P Q : Polynomial ℤ) (n : ℕ) :
    (PowerSeries.coeff n) (expPolySub P * expPolySub Q) =
    (∑ a ∈ Finset.range (P.natDegree + 1),
     ∑ b ∈ Finset.range (Q.natDegree + 1),
       (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n) / (n.factorial : ℚ) := by
  rw [coeff_mul_expand]
  rw [lhs_to_triple_sum]
  rw [triple_sum_factorial_to_choose]
  rw [factor_out_factorial]
  rw [sum_rearrange]
  rw [factor_coeffs_from_inner_sum]
  rw [apply_binomial_to_inner_sum]
  ring

/--
@isnad1 id=eq.0h3v.s7.db0680425d58 from=translated src=- shape=dc11d0e8 vocab=469e9704
-/
lemma convolution_sum_eq (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range ((P * Q).natDegree + 1), ((P * Q).coeff j : ℚ) * (j : ℚ)^n =
    ∑ j ∈ Finset.range (P.natDegree + Q.natDegree + 1),
      ∑ ab ∈ Finset.antidiagonal j,
        (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n := by
  have h_deg : (P * Q).natDegree ≤ P.natDegree + Q.natDegree := Polynomial.natDegree_mul_le
  rw [exp_poly_sub_sum_extend (P * Q) (P.natDegree + Q.natDegree + 1) n (by omega)]
  apply Finset.sum_congr rfl
  intro j hj
  have hj' : j < P.natDegree + Q.natDegree + 1 := Finset.mem_range.mp hj
  have h1 : ((P * Q).coeff j : ℚ) = ∑ k ∈ Finset.range (j + 1),
    (P.coeff k : ℚ) * (Q.coeff (j - k) : ℚ) := by
    rw [Polynomial.coeff_mul]
    simp only [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    norm_cast
  rw [h1]
  have h2 : (∑ k ∈ Finset.range (j + 1), (P.coeff k : ℚ) * (Q.coeff (j - k) : ℚ)) * (j : ℚ) ^ n =
      ∑ k ∈ Finset.range (j + 1), (P.coeff k : ℚ) * (Q.coeff (j - k) : ℚ) * (j : ℚ) ^ n := by
    rw [Finset.sum_mul]
  rw [h2]
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  apply Finset.sum_congr rfl
  simp_all

/--
@isnad1 id=le.0h2v.s6.dd5765216d38 from=translated src=- shape=97313b44 vocab=f573af58
-/
lemma rectangle_subset_triangle (P Q : Polynomial ℤ) :
    Finset.range (P.natDegree + 1) ×ˢ Finset.range (Q.natDegree + 1) ⊆
    (Finset.range (P.natDegree + Q.natDegree + 1)).biUnion Finset.antidiagonal := by
  intro ab hab
  simp only [Finset.mem_product, Finset.mem_range] at hab
  simp only [Finset.mem_biUnion, Finset.mem_range, Finset.mem_antidiagonal]
  refine ⟨ab.1 + ab.2, ?_, rfl⟩
  omega

/--
@isnad1 id=eq.2h4v.s7.b9f4bc7678ed from=translated src=- shape=e6481510 vocab=204fb170
-/
lemma term_vanishes_outside_rectangle (P Q : Polynomial ℤ) (n : ℕ) (ab : ℕ × ℕ)
    (_h_in_tri : ab ∈ (Finset.range (P.natDegree + Q.natDegree + 1)).biUnion Finset.antidiagonal)
    (h_not_rect : ab ∉ Finset.range (P.natDegree + 1) ×ˢ Finset.range (Q.natDegree + 1)) :
    (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n = 0 := by
  have h₁ : ab.1 > P.natDegree ∨ ab.2 > Q.natDegree := by
    by_contra! h
    exact h_not_rect (by simp [Finset.mem_product, Finset.mem_range]; omega)
  rcases h₁ with h₁ | h₁
  · rw [show (P.coeff ab.1 : ℚ) = 0 by
      exact_mod_cast Polynomial.coeff_eq_zero_of_natDegree_lt h₁]
    ring
  · rw [show (Q.coeff ab.2 : ℚ) = 0 by
      exact_mod_cast Polynomial.coeff_eq_zero_of_natDegree_lt h₁]
    ring

/--
@isnad1 id=pairwise.0h1v.s4.46d7a3a394c4 from=translated src=- shape=c0c4a345 vocab=d9b6cbc1
-/
lemma pairwiseDisjoint_antidiagonal (s : Finset ℕ) :
    (s : Set ℕ).PairwiseDisjoint Finset.antidiagonal := by
  intro j₁ _ j₂ _ hne
  rw [Function.onFun, Finset.disjoint_left]
  simp_all

/--
@isnad1 id=eq.0h3v.s7.b220271f4d1c from=translated src=- shape=a46b8a94 vocab=3705736b
-/
lemma nested_sum_eq_biUnion_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range (P.natDegree + Q.natDegree + 1),
      ∑ ab ∈ Finset.antidiagonal j,
        (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n =
    ∑ ab ∈ (Finset.range (P.natDegree + Q.natDegree + 1)).biUnion Finset.antidiagonal,
      (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n := by
  exact (Finset.sum_biUnion (pairwiseDisjoint_antidiagonal _)).symm

/--
@isnad1 id=eq.0h3v.s7.da6f67ed5916 from=translated src=- shape=30cc1d51 vocab=834e8835
-/
lemma product_sum_eq_nested (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ ab ∈ Finset.range (P.natDegree + 1) ×ˢ Finset.range (Q.natDegree + 1),
      (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n := by
  rw [Finset.sum_product]

/--
@isnad1 id=eq.0h3v.s7.7f911f4a95f3 from=translated src=- shape=a430b334 vocab=469e9704
-/
lemma triangular_to_rectangular_sum (P Q : Polynomial ℤ) (n : ℕ) :
    ∑ j ∈ Finset.range (P.natDegree + Q.natDegree + 1),
      ∑ ab ∈ Finset.antidiagonal j,
        (P.coeff ab.1 : ℚ) * (Q.coeff ab.2 : ℚ) * ((ab.1 : ℚ) + ab.2)^n =
    ∑ a ∈ Finset.range (P.natDegree + 1),
      ∑ b ∈ Finset.range (Q.natDegree + 1),
        (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n := by
  rw [nested_sum_eq_biUnion_sum]
  rw [← product_sum_eq_nested]
  symm
  apply Finset.sum_subset (rectangle_subset_triangle P Q)
  intro ab h_in_tri h_not_rect
  exact term_vanishes_outside_rectangle P Q n ab h_in_tri h_not_rect

/--
@isnad1 id=eq.0h3v.s7.d991803725cd from=translated src=- shape=bca201bf vocab=8f1196f9
-/
lemma exp_poly_sub_prod_coeff_eq (P Q : Polynomial ℤ) (n : ℕ) :
    (PowerSeries.coeff n) (expPolySub (P * Q)) =
    (∑ a ∈ Finset.range (P.natDegree + 1),
     ∑ b ∈ Finset.range (Q.natDegree + 1),
       (P.coeff a : ℚ) * (Q.coeff b : ℚ) * ((a : ℚ) + b)^n) / (n.factorial : ℚ) := by
  rw [exp_poly_sub_coeff]
  rw [convolution_sum_eq]
  rw [triangular_to_rectangular_sum]

/--
@isnad1 id=eq.0h2v.s5.8698bc287620 from=translated src=- shape=735a947b vocab=2372be1c
-/
lemma exp_poly_sub_mul (P Q : Polynomial ℤ) :
    expPolySub (P * Q) = expPolySub P * expPolySub Q := by
  apply PowerSeries.ext
  intro n
  rw [exp_poly_sub_prod_coeff_eq, exp_poly_sub_mul_coeff_eq]

/--
@isnad1 id=eq.0h2v.s6.91d258fa6507 from=translated src=- shape=ee1f16b3 vocab=8dc2409f
-/
lemma exp_poly_sub_prod' {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    expPolySub G.productPolynomial =
    ∏ i : Fin G.m, expPolySub (1 - Polynomial.X ^ (G.d i)) := by
  unfold NumericalSemigroupGenerators.productPolynomial
  have h := Finset.prod_hom_rel (s := Finset.univ) (r := fun P F => expPolySub P = F)
    (f := fun i : Fin G.m => (1 - Polynomial.X ^ (G.d i)))
    (g := fun i : Fin G.m => expPolySub (1 - Polynomial.X ^ (G.d i)))
  rw [h]
  · exact exp_poly_sub_one
  · intro a b c hbc
    rw [exp_poly_sub_mul, hbc]

/--
@isnad1 id=eq.0h2v.s6.577c509af5bb from=translated src=- shape=92fb9ef3 vocab=814340e4
-/
lemma productPolynomial_exp_transform {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
  :
    expPolySub G.productPolynomial =
    ((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) := by
  rw [exp_poly_sub_prod']
  conv_lhs => arg 2; ext i; rw [single_factor_exp_transform]
  exact prod_single_factor_eq_final_form G

/--
@isnad1 id=eq.0h1v.s7.990f08ec44fd from=translated src=- shape=5dc4502c vocab=dd13bb07
-/
lemma coeff_one_sub_exp (n : ℕ) :
    (PowerSeries.coeff n) (1 - PowerSeries.exp ℚ) =
    if n = 0 then 0 else -1 / (n.factorial : ℚ) := by
  rw [map_sub, PowerSeries.coeff_one, PowerSeries.coeff_exp]
  simp only [Algebra.algebraMap_self, RingHom.id_apply]
  split_ifs with h
  · simp [h]
  · ring

/--
@isnad1 id=eq.0h2v.s6.9386862e36df from=translated src=- shape=450c00ae vocab=52d7e501
-/
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

/--
@isnad1 id=eq.0h3v.s8.01782e1f622a from=translated src=- shape=30bef3e0 vocab=d5b62eda
-/
lemma coeff_mul_as_range_sum {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) ((1 - PowerSeries.exp ℚ) * partialSumGenFunc G) =
    ∑ k ∈ Finset.range (n + 1),
      (PowerSeries.coeff k) (1 - PowerSeries.exp ℚ) *
      (PowerSeries.coeff (n - k)) (partialSumGenFunc G) := by
  rw [PowerSeries.coeff_mul]
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun k m => (PowerSeries.coeff k) (1 - PowerSeries.exp ℚ) *
      (PowerSeries.coeff m) (partialSumGenFunc G)) n

/--
@isnad1 id=eq.0h3v.s8.473a86e18865 from=translated src=- shape=a5772985 vocab=c7ef9dfd
-/
lemma coeff_sum_substitute {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (PowerSeries.coeff k) (1 - PowerSeries.exp ℚ) *
      (PowerSeries.coeff (n - k)) (partialSumGenFunc G) =
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else -1 / (k.factorial : ℚ)) *
      ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
        (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
       ((n - k).factorial : ℚ)) := by
  apply Finset.sum_congr rfl
  intro k _
  rw [coeff_one_sub_exp, partialSumGenFunc_coeff]

/--
@isnad1 id=eq.0h3v.s8.30f71a7a4588 from=translated src=- shape=98588231 vocab=591f1799
-/
lemma drop_k_eq_zero_term {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else -1 / (k.factorial : ℚ)) *
      ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
        (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
       ((n - k).factorial : ℚ)) =
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-1 / (k.factorial : ℚ)) *
        ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
          (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
         ((n - k).factorial : ℚ))) := by
  simp_all

/--
@isnad1 id=eq.2h4v.s8.87c443350eea from=translated src=- shape=30a2d17d vocab=5e4239d4
-/
lemma summand_eq_for_pos {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n k : ℕ)
    (_hk_pos : k ≠ 0) (hk_le : k ≤ n) :
    (-1 / (k.factorial : ℚ)) *
      ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
        (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
       ((n - k).factorial : ℚ)) =
    (-(n.choose k : ℚ) / (n.factorial : ℚ)) *
      (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
        (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) := by
  have h₁₂ : (n.choose k : ℚ) * (k.factorial : ℚ) * ((n - k).factorial : ℚ) =
      (n.factorial : ℚ) := by
    norm_cast
    rw [← Nat.choose_mul_factorial_mul_factorial hk_le]
  have hk5 : (k.factorial : ℚ) ≠ 0 := by positivity
  have hk6 : ((n - k).factorial : ℚ) ≠ 0 := by positivity
  have h₈ : (n.choose k : ℚ) / (n.factorial : ℚ) =
      1 / (k.factorial : ℚ) / ((n - k).factorial : ℚ) := by
    field_simp
    nlinarith [h₁₂]
  set S := ∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
    (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)
  rw [neg_div, neg_div, h₈]
  ring

/--
@isnad1 id=eq.0h3v.s8.3a2fc2054efd from=translated src=- shape=1ea6232c vocab=b7bce1e3
-/
lemma apply_factorial_identity {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-1 / (k.factorial : ℚ)) *
        ((∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
          (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k)) /
         ((n - k).factorial : ℚ))) =
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-(n.choose k : ℚ) / (n.factorial : ℚ)) *
        (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
          (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k))) := by
  apply Finset.sum_congr rfl
  intro k hk
  split_ifs with hk_zero
  · rfl
  · have hk_le : k ≤ n := by
      simp_all
    exact summand_eq_for_pos G n k hk_zero hk_le

/--
@isnad1 id=eq.0h3v.s8.3155831e65eb from=translated src=- shape=e07d4bab vocab=2534705c
-/
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

/--
@isnad1 id=eq.0h3v.s7.0963c1b11cf4 from=translated src=- shape=f336ff0f vocab=52d7e501
-/
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

/--
@isnad1 id=eq.0h3v.s8.d92e8e4f97a0 from=translated src=- shape=e195b969 vocab=b7bce1e3
-/
lemma factor_and_apply_binomial {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n :
  ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (if k = 0 then 0 else
        (-(n.choose k : ℚ) / (n.factorial : ℚ)) *
        (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
          (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) * (j : ℚ)^(n - k))) =
    (-1 / (n.factorial : ℚ)) *
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) := by
  have step1 := factor_neg_choose_div_factorial G.hilbertNumerator.natDegree n
    (fun j => ∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ))
  have step2 := swap_and_apply_binomial G.hilbertNumerator.natDegree n
    (fun j => ∑ m ∈ Finset.range (j + 1), (G.productPolynomial.coeff m : ℚ))
  rw [step1, step2]

/--
@isnad1 id=eq.0h3v.s8.98b5efaa95d9 from=translated src=- shape=90e48683 vocab=7988d77b
-/
lemma coeff_lhs_expand {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) ((1 - PowerSeries.exp ℚ) * partialSumGenFunc G) =
    (-1 / (n.factorial : ℚ)) *
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1), (G.productPolynomial.coeff k : ℚ)) *
      (((j : ℚ) + 1)^n - (j : ℚ)^n)) := by
  rw [coeff_mul_as_range_sum]
  rw [coeff_sum_substitute]
  rw [drop_k_eq_zero_term]
  rw [apply_factorial_identity]
  rw [factor_and_apply_binomial]

/--
@isnad1 id=eq.0h3v.s7.25740be46f94 from=translated src=- shape=5a467bbb vocab=0b1c9bfb
-/
lemma coeff_lhs_eq_rhs {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) ((1 - PowerSeries.exp ℚ) * partialSumGenFunc G) =
    (PowerSeries.coeff n) (expPolySub G.productPolynomial) := by
  rw [coeff_lhs_expand, telescoping_sum, exp_poly_sub_coeff]
  ring

/--
@isnad1 id=eq.0h2v.s6.3a9543fd1412 from=translated src=- shape=1e6b3ec3 vocab=bf88d037
-/
lemma partialSumGenFunc_mul_one_sub_exp {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    (1 - PowerSeries.exp ℚ) * partialSumGenFunc G = expPolySub G.productPolynomial := by
  ext n
  exact coeff_lhs_eq_rhs G n

/--
@isnad1 id=eq.0h2v.s7.c56e08af25f1 from=translated src=- shape=e94c4dca vocab=6a53aeeb
-/
lemma partialSumGenFunc_identity {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) :
    PowerSeries.X * partialSumGenFunc G =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.BSeries) := by
  have h1 : (1 - PowerSeries.exp ℚ) * partialSumGenFunc G = expPolySub G.productPolynomial :=
    partialSumGenFunc_mul_one_sub_exp G
  have h2 : expPolySub G.productPolynomial =
      ((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) :=
    productPolynomial_exp_transform G
  have h3 : (1 - PowerSeries.exp ℚ) * partialSumGenFunc G =
      ((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) := h1.trans h2
  have h4 : (PowerSeries.exp ℚ - 1) * partialSumGenFunc G =
      ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries) := by
    have neg_eq : PowerSeries.exp ℚ - 1 = -(1 - PowerSeries.exp ℚ) := by ring
    rw [neg_eq, neg_mul, h3]
    rw [show -(((-1 : ℚ)^G.m * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.ASeries)) =
        (-((-1 : ℚ)^G.m * (G.piM : ℚ))) • (PowerSeries.X ^ G.m * G.ASeries)
        from (neg_smul _ _).symm]
    congr 1
    ring
  have h5 : bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) * partialSumGenFunc G =
      bernoulliPowerSeries ℚ * (((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m *
        G.ASeries)) := by
    rw [mul_assoc, h4]
  have h6 : bernoulliPowerSeries ℚ * (PowerSeries.exp ℚ - 1) = PowerSeries.X :=
    bernoulliPowerSeries_mul_exp_sub_one ℚ
  rw [h6] at h5
  have h7 : bernoulliPowerSeries ℚ * (((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m *
    G.ASeries)) =
      ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m * G.BSeries) := by
    simp only [NumericalSemigroupGenerators.BSeries, mul_smul_comm]
    ring_nf
  simp_all

/--
@isnad1 id=iff.0h2v.s5.95f8cf016e6b from=translated src=- shape=af196f4c vocab=8577ebb4
-/
lemma cond_equiv (m n : ℕ) : (m ≤ n + 1) ↔ (m - 1 ≤ n) := by aesop

/--
@isnad1 id=eq.2h2v.s6.59149416ee40 from=translated src=- shape=5fa57758 vocab=327f97a7
-/
lemma index_eq (m n : ℕ) (hm : 0 < m) (h : m ≤ n + 1) : (n + 1) - m = n - (m - 1) := by omega

/--
@isnad1 id=eq.0h3v.s8.247af5868092 from=translated src=- shape=eb8195ef vocab=e523831b
-/
lemma coeff_X_pow_shift {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff (n + 1)) (PowerSeries.X ^ G.m * G.BSeries) =
    (PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) := by
  rw [PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_X_pow_mul']
  simp only [cond_equiv]
  split_ifs with h
  · rw [index_eq G.m n G.hm_pos (cond_equiv G.m n |>.mpr h)]
  · rfl

/--
@isnad1 id=eq.0h3v.s8.c8847b0c1c29 from=translated src=- shape=cdd3fd62 vocab=fc6a6a89
-/
lemma partialSumGenFunc_coeff_eq_bernoulli_term {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (PowerSeries.coeff n) (partialSumGenFunc G) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) *
      (PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) := by
  have h_identity := partialSumGenFunc_identity G
  have h_coeff : (PowerSeries.coeff (n + 1)) (PowerSeries.X * partialSumGenFunc G) =
      (PowerSeries.coeff (n + 1)) (((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) • (PowerSeries.X ^ G.m *
        G.BSeries)) := by
    rw [h_identity]
  rw [PowerSeries.coeff_succ_X_mul] at h_coeff
  rw [PowerSeries.coeff_smul] at h_coeff
  rw [coeff_X_pow_shift G n] at h_coeff
  simp_all

/--
@isnad1 id=eq.0h3v.s8.9bef96c5a92f from=translated src=- shape=48b43555 vocab=ba7e7a4d
-/
lemma sum_part_equals_bernoulli_term_natDegree {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ k ∈ Finset.range (j + 1),
        (G.productPolynomial.coeff k : ℚ)) * (j : ℚ)^n) / (n.factorial : ℚ) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) *
      (PowerSeries.coeff n) (PowerSeries.X ^ (G.m - 1) * G.BSeries) := by
  rw [← partialSumGenFunc_coeff, partialSumGenFunc_coeff_eq_bernoulli_term]

/--
@isnad1 id=le.1h2v.s5.2d7b0cfad88c from=translated src=- shape=39a52ad1 vocab=a50cdee1
-/
lemma gap_le_sup {S : NumericalSemigroup} (g : ℕ) (hg : g ∈ S.gaps) : g ≤ S.gaps.sup id :=
  Finset.le_sup (f := id) hg

/--
@isnad1 id=eq.0h1v.s5.80ca9c85e2ef from=translated src=- shape=1e9389ef vocab=9d237249
-/
lemma neg_neg_one_pow_eq (m : ℕ) : -((-1 : ℤ) ^ m) = (-1 : ℤ) ^ (m + 1) := by ring

/--
@isnad1 id=eq.1h2v.s7.a4a7705dd858 from=translated src=- shape=92c7bae2 vocab=c7abc8e5
-/
lemma gap_sum_at_jstar {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (hnonempty : S.gaps.Nonempty) :
    ∑ g ∈ S.gaps.filter (· ≤ G.productPolynomial.natDegree + S.gaps.sup id),
      G.productPolynomial.coeff (G.productPolynomial.natDegree + S.gaps.sup id - g) =
    (-1) ^ G.m := by
  obtain ⟨gmax, hgmax_mem, hgmax_eq⟩ := Finset.exists_mem_eq_sup S.gaps hnonempty id
  simp only [id_eq] at hgmax_eq
  have hfilter : S.gaps.filter (· ≤ G.productPolynomial.natDegree + S.gaps.sup id) = S.gaps := by
    apply Finset.filter_true_of_mem
    intro g hg
    calc g ≤ S.gaps.sup id := Finset.le_sup (f := id) hg
         _ ≤ G.productPolynomial.natDegree + S.gaps.sup id := le_add_self
  rw [hfilter]
  rw [Finset.sum_eq_single_of_mem gmax hgmax_mem]
  · have hsub : G.productPolynomial.natDegree +
    S.gaps.sup id - gmax = G.productPolynomial.natDegree := by rw [hgmax_eq, Nat.add_sub_cancel]
    rw [hsub, Polynomial.coeff_natDegree, productPolynomial_leadingCoeff G]
  · intro g hg hne
    apply Polynomial.coeff_eq_zero_of_natDegree_lt
    have hle : g ≤ gmax := by
      have := Finset.le_sup (f := id) hg
      simp_all
    have hlt : g < gmax := lt_of_le_of_ne hle hne
    simp only [hgmax_eq]
    omega

/--
@isnad1 id=eq.1h2v.s6.5318abfac33b from=translated src=- shape=84722e3c vocab=a3cd0a2f
-/
lemma hilbertNumerator_coeff_at_jstar {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S)
    (hnonempty : S.gaps.Nonempty) :
    G.hilbertNumerator.coeff (G.productPolynomial.natDegree + S.gaps.sup id) = (-1 : ℤ) ^ (G.m +
      1) := by
  set jstar := G.productPolynomial.natDegree + S.gaps.sup id with hjstar_def
  have hjstar_bound : jstar < G.hilbertNumeratorDegBound := by
    unfold NumericalSemigroupGenerators.hilbertNumeratorDegBound
    omega
  have hcoeff : G.hilbertNumerator.coeff jstar =
      (∑ k ∈ Finset.range (jstar + 1), G.productPolynomial.coeff k) -
      (∑ g ∈ S.gaps.filter (· ≤ jstar), G.productPolynomial.coeff (jstar - g)) := by
    simp only [NumericalSemigroupGenerators.hilbertNumerator]
    simp [Polynomial.coeff_monomial, Finset.mem_range, hjstar_bound]
  have h1 : ∑ k ∈ Finset.range (jstar + 1), G.productPolynomial.coeff k = 0 := by
    have hge : 1 ≤ S.gaps.sup id := by
      obtain ⟨gmax, hgmax_mem, hgmax_eq⟩ := Finset.exists_mem_eq_sup S.gaps hnonempty id
      simp only [id_eq] at hgmax_eq
      rw [hgmax_eq]; exact pos_of_mem_gaps hgmax_mem
    have h1 := NumericalSemigroupGenerators.sum_coeff_large_eq_sum_coeff_deg G jstar (by omega)
    rw [h1, NumericalSemigroupGenerators.sum_coeff_eq_eval_one G,
      NumericalSemigroupGenerators.productPolynomial_eval_one G]
  rw [hcoeff, h1, zero_sub]
  have hgap := gap_sum_at_jstar G hnonempty
  rw [hgap, neg_neg_one_pow_eq]

/--
@isnad1 id=ne.0h1v.s5.e2b1cc33b85e from=translated src=- shape=ef809ff9 vocab=9d237249
-/
lemma neg_one_pow_ne_zero' (m : ℕ) : ((-1 : ℤ) ^ (m + 1)) ≠ 0 := by exact Int.neg_one_pow_ne_zero

/--
@isnad1 id=le.1h2v.s5.a7f45f26c72f from=translated src=- shape=3b9ea3d4 vocab=56488a92
-/
lemma hilbertNumerator_natDegree_ge_jstar {S : NumericalSemigroup} (G :
  NumericalSemigroupGenerators S)
    (hnonempty : S.gaps.Nonempty) :
    G.productPolynomial.natDegree + S.gaps.sup id ≤ G.hilbertNumerator.natDegree := by
  apply Polynomial.le_natDegree_of_ne_zero
  rw [hilbertNumerator_coeff_at_jstar G hnonempty]
  exact neg_one_pow_ne_zero' G.m

/--
@isnad1 id=le.1h3v.s5.9a99da806ec0 from=translated src=- shape=0a428f32 vocab=58e161c5
-/
lemma hilbertNumerator_natDegree_ge_prod_plus_gap {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g : ℕ) (hg : g ∈ S.gaps) :
    G.productPolynomial.natDegree + g ≤ G.hilbertNumerator.natDegree := by
  have hnonempty : S.gaps.Nonempty := ⟨g, hg⟩
  have hle : g ≤ S.gaps.sup id := gap_le_sup g hg
  calc G.productPolynomial.natDegree + g
      ≤ G.productPolynomial.natDegree + S.gaps.sup id := by omega
    _ ≤ G.hilbertNumerator.natDegree := hilbertNumerator_natDegree_ge_jstar G hnonempty

/--
@isnad1 id=mem.1h4v.s6.f1f14bf24c91 from=translated src=- shape=3ba2baf8 vocab=600f1a46
-/
lemma forward_map_mem {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g j : ℕ)
    (hj : j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·)) :
    j - g ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g) := by
  simp only [Finset.mem_filter, Finset.mem_range] at hj ⊢
  omega

/--
@isnad1 id=mem.1h4v.s6.992800aa35f5 from=translated src=- shape=d249565b vocab=600f1a46
-/
lemma inverse_map_mem {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g k : ℕ)
    (hk : k ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g)) :
    k + g ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·) := by
  simp only [Finset.mem_filter, Finset.mem_range] at hk ⊢
  omega

/--
@isnad1 id=eq.1h4v.s7.e2732168e69b from=translated src=- shape=afe65323 vocab=fc7e2cb0
-/
lemma inner_sum_reindex {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n g : ℕ) (_hg : g ∈ S.gaps) :
    ∑ j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·),
      (G.productPolynomial.coeff (j - g) : ℚ) * (j : ℚ)^n =
    ∑ k ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n := by
  apply Finset.sum_bij'
    (i := fun j _ => j - g)
    (j := fun k _ => k + g)
    (hi := fun j hj => forward_map_mem G g j hj)
    (hj := fun k hk => inverse_map_mem G g k hk)
  · simp_all
  · simp_all
  · simp_all

/--
@isnad1 id=le.1h3v.s6.242b181f02d1 from=translated src=- shape=b547d805 vocab=7a59af7c
-/
lemma range_subset_from_degree_bound' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g : ℕ) (hg : g ∈ S.gaps) :
    Finset.range (G.productPolynomial.natDegree + 1) ⊆
    Finset.range (G.hilbertNumerator.natDegree + 1 - g) := by
  rw [Finset.range_subset_range]
  have h := hilbertNumerator_natDegree_ge_prod_plus_gap G g hg
  omega

/--
@isnad1 id=eq.2h5v.s7.bc7c09f8dfb1 from=translated src=- shape=0eb9c0a7 vocab=c8ff54a9
-/
lemma summand_zero_beyond_degree' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (g n k : ℕ)
    (_hk : k ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g))
    (hk_not : k ∉ Finset.range (G.productPolynomial.natDegree + 1)) :
    (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n = 0 := by
  simp only [Finset.mem_range, not_lt] at hk_not
  rw [show (G.productPolynomial.coeff k : ℚ) = 0 by
    exact_mod_cast Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
  ring

/--
@isnad1 id=eq.1h4v.s7.9d799b5ba4fe from=translated src=- shape=80ea71e9 vocab=9d6cb93d
-/
lemma inner_sum_extend_range' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n g : ℕ) (hg : g ∈ S.gaps) :
    ∑ k ∈ Finset.range (G.hilbertNumerator.natDegree + 1 - g),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n =
    ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n := by
  symm
  apply Finset.sum_subset (range_subset_from_degree_bound' G g hg)
  intro k hk hk_not
  exact summand_zero_beyond_degree' G g n k hk hk_not

/--
@isnad1 id=eq.0h4v.s7.a7dc4c194818 from=translated src=- shape=9bab1e07 vocab=2e3bb719
-/
lemma distribute_j_pow_into_sum {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n j : ℕ) :
    (∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n =
    ∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ) * (j : ℚ)^n := by
  rw [Finset.sum_mul]

/--
@isnad1 id=iff.0h4v.s6.0f87e92154bc from=translated src=- shape=c7645a9b vocab=41368cae
-/
lemma sum_exchange_condition' {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    ∀ (j : ℕ) (g : ℕ),
      (j ∈ Finset.range (G.hilbertNumerator.natDegree + 1) ∧
       g ∈ S.gaps.filter (· ≤ j)) ↔
      (j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·) ∧
       g ∈ S.gaps) := by
  aesop

/--
@isnad1 id=eq.0h3v.s7.aa6b990024cf from=translated src=- shape=f22f3122 vocab=a28e019a
-/
lemma distribute_and_swap_sums {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n =
    ∑ g ∈ S.gaps, ∑ j ∈ (Finset.range (G.hilbertNumerator.natDegree + 1)).filter (g ≤ ·),
      (G.productPolynomial.coeff (j - g) : ℚ) * (j : ℚ)^n := by
  conv_lhs =>
    congr
    · skip
    · ext j
      rw [distribute_j_pow_into_sum G n j]
  exact Finset.sum_comm' (sum_exchange_condition' G)

/--
@isnad1 id=eq.0h3v.s7.60a7e94a4cb7 from=translated src=- shape=556be4e2 vocab=a28e019a
-/
lemma gap_sum_exchange {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) :
    ∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ g ∈ S.gaps.filter (· ≤ j), (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n =
    ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n := by
  rw [distribute_and_swap_sums]
  apply Finset.sum_congr rfl
  intro g hg
  rw [inner_sum_reindex G n g hg, inner_sum_extend_range' G n g hg]

/--
@isnad1 id=eq.0h3v.s6.3572d4280354 from=translated src=- shape=3d99b7a0 vocab=7aa6ef92
-/
lemma binomial_sum_eq_add_pow (a b : ℚ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (n.choose k : ℚ) * a^k * b^(n - k) = (a + b)^n := by
  rw [add_pow]
  apply Finset.sum_congr rfl
  intro k _
  ring

/--
@isnad1 id=eq.0h4v.s7.eabea8eb3c2c from=translated src=- shape=846831e3 vocab=ca826c6f
-/
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

/--
@isnad1 id=eq.0h5v.s7.0f95beac4d0e from=translated src=- shape=64a99c9b vocab=ca826c6f
-/
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

/--
@isnad1 id=eq.0h3v.s7.0822e5717db7 from=translated src=- shape=d5261dec vocab=a6dad5fe
-/
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

/--
@isnad1 id=eq.0h3v.s7.1a7296f452c7 from=translated src=- shape=c480b5bc vocab=a5b6cf13
-/
lemma gap_sum_binomial_expand {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ)
  :
    (∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n) / (n.factorial : ℚ) =
    ∑ r ∈ Finset.range (n + 1),
      ((∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) / (r.factorial : ℚ)) *
      ((∑ g ∈ S.gaps, (g : ℚ)^(n - r)) / ((n - r).factorial : ℚ)) := by
  have binom_expand : ∀ (k g : ℕ),
      ((k : ℚ) + (g : ℚ))^n = ∑ r ∈ Finset.range (n + 1),
        (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
    intro k g
    exact (binomial_sum_eq_add_pow k g n).symm
  have step1 : ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * ((k : ℚ) + (g : ℚ))^n =
    ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      ∑ r ∈ Finset.range (n + 1),
        (G.productPolynomial.coeff k : ℚ) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
    congr 1
    ext g
    congr 1
    ext k
    rw [binom_expand k g]
    rw [Finset.mul_sum]
    congr 1
    ext r
    ring
  have step2 : ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      ∑ r ∈ Finset.range (n + 1),
        (G.productPolynomial.coeff k : ℚ) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    ∑ r ∈ Finset.range (n + 1), ∑ g ∈ S.gaps,
      ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) := by
    exact triple_sum_exchange S.gaps G.productPolynomial.natDegree (fun k =>
      (G.productPolynomial.coeff k : ℚ)) n
  have step3 : ∀ r, ∑ g ∈ S.gaps, ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * (n.choose r : ℚ) * (k : ℚ)^r * (g : ℚ)^(n - r) =
    (n.choose r : ℚ) * (∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) *
      (∑ g ∈ S.gaps, (g : ℚ)^(n - r)) := by
    intro r
    exact factor_binomial_coeff_from_double_sum S.gaps G.productPolynomial.natDegree
      (fun k => (G.productPolynomial.coeff k : ℚ)) n r
  rw [step1, step2]
  simp_rw [step3]
  rw [Finset.sum_div]
  exact sum_choose_mul_div_factorial_eq_sum_div_factorials n
    (fun r => ∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r)
    (fun r => ∑ g ∈ S.gaps, (g : ℚ)^(n - r))

/--
@isnad1 id=eq.0h3v.s7.ff62b1c17815 from=translated src=- shape=59b2158d vocab=d59222ec
-/
lemma P_sum_to_exp_coeff {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (r : ℕ) :
    (∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) / (r.factorial : ℚ) =
    ((-1 : ℚ)^G.m * (G.piM : ℚ)) * (PowerSeries.coeff r) (PowerSeries.X ^ G.m * G.ASeries) := by
  rw [← exp_poly_sub_coeff]
  rw [productPolynomial_exp_transform]
  simp only [map_smul, smul_eq_mul]

/--
@isnad1 id=eq.0h2v.s7.f9da2793e283 from=translated src=- shape=c6e3f9ed vocab=19078530
-/
lemma gap_sum_to_coeff {S : NumericalSemigroup} (k : ℕ) :
    (∑ g ∈ S.gaps, (g : ℚ)^k) / (k.factorial : ℚ) =
    (PowerSeries.coeff k) (PowerSeries.mk fun j => ∑ g ∈ S.gaps,
      (g : ℚ)^j / (j.factorial : ℚ)) := by
  simp [PowerSeries.coeff_mk, Finset.sum_div]

/--
@isnad1 id=eq.0h4v.s8.b8f865697a56 from=translated src=- shape=0cd570a2 vocab=2383e521
-/
lemma coeff_mul_range' {R : Type*} [Semiring R] (φ ψ : PowerSeries R) (n : ℕ) :
    (PowerSeries.coeff n) (φ * ψ) =
    ∑ r ∈ Finset.range (n + 1), (PowerSeries.coeff r) φ * (PowerSeries.coeff (n - r)) ψ := by
  rw [PowerSeries.coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/--
@isnad1 id=eq.0h5v.s6.bf24ffe613d7 from=translated src=- shape=41ec7e89 vocab=f1f138c6
-/
lemma sum_factor_scalar' {α : Type*} (s : Finset α) (c : ℚ) (a b : α → ℚ) :
    ∑ r ∈ s, (c * a r) * b r = c * ∑ r ∈ s, a r * b r := by
  simp_rw [mul_assoc, Finset.mul_sum]

/--
@isnad1 id=eq.0h3v.s8.b27d862e5984 from=translated src=- shape=4b64ec20 vocab=9d2c19a3
-/
lemma binomial_sum_to_convolution {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n
  : ℕ) :
    ∑ r ∈ Finset.range (n + 1),
      ((∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
        (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) / (r.factorial : ℚ)) *
      ((∑ g ∈ S.gaps, (g : ℚ)^(n - r)) / ((n - r).factorial : ℚ)) =
    ((-1 : ℚ)^G.m * (G.piM : ℚ)) *
      (PowerSeries.coeff n) (PowerSeries.X ^ G.m * G.ASeries *
        PowerSeries.mk fun k => ∑ g ∈ S.gaps, (g : ℚ)^k / (k.factorial : ℚ)) := by
  have h1 : ∀ r, (∑ k ∈ Finset.range (G.productPolynomial.natDegree + 1),
      (G.productPolynomial.coeff k : ℚ) * (k : ℚ)^r) / (r.factorial : ℚ) =
      ((-1 : ℚ)^G.m * (G.piM : ℚ)) * (PowerSeries.coeff r) (PowerSeries.X ^ G.m * G.ASeries) :=
    fun r => P_sum_to_exp_coeff G r
  have h2 : ∀ r, (∑ g ∈ S.gaps, (g : ℚ)^r) / (r.factorial : ℚ) =
      (PowerSeries.coeff r) (PowerSeries.mk fun j => ∑ g ∈ S.gaps, (g : ℚ)^j / (j.factorial : ℚ)) :=
    fun r => gap_sum_to_coeff r
  conv_lhs => arg 2; ext r; rw [h1 r, h2 (n - r)]
  rw [sum_factor_scalar']
  congr 1
  rw [← coeff_mul_range']

/--
@isnad1 id=eq.0h3v.s8.f478ba7d8916 from=translated src=- shape=eecfbace vocab=47bf0a5d
-/
lemma gap_part_equals_gap_term_natDegree {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) (n : ℕ) :
    (∑ j ∈ Finset.range (G.hilbertNumerator.natDegree + 1),
      (∑ g ∈ S.gaps.filter (· ≤ j),
        (G.productPolynomial.coeff (j - g) : ℚ)) * (j : ℚ)^n) / (n.factorial : ℚ) =
    ((-1 : ℚ)^(G.m + 1) * (G.piM : ℚ)) * (-(PowerSeries.coeff n) (PowerSeries.X ^ G.m *
      G.ASeries *
         PowerSeries.mk fun k => ∑ g ∈ S.gaps, (g : ℚ)^k / (k.factorial : ℚ))) := by
  rw [gap_sum_exchange]
  rw [gap_sum_binomial_expand]
  rw [binomial_sum_to_convolution]
  ring

/--
@isnad1 id=eq.0h2v.s3.dab5175f43de from=translated src=- shape=74e016e8 vocab=bd1efbb8
-/
lemma exp_poly_sub_hilbertNumerator_eq {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    expPolySub G.hilbertNumerator = QExpSeries G := by
  ext n
  rw [exp_poly_sub_coeff, Q_exp_series_coeff]
  rw [hilbert_sum_decomposition_natDegree]
  rw [sub_div]
  rw [sum_part_equals_bernoulli_term_natDegree, gap_part_equals_gap_term_natDegree]
  ring

/--
@isnad1 id=eq.0h2v.s3.700ed5ab6483 from=translated src=- shape=2421c1eb vocab=e62f9f44
-/
lemma hilbertNumerator_exp_eq_Q_exp {S : NumericalSemigroup}
    (G : NumericalSemigroupGenerators S) :
    hilbertNumeratorExpSub G = QExpSeries G := by
  rw [hilbertNumerator_exp_sub_eq_exp_poly_sub, exp_poly_sub_hilbertNumerator_eq]

/--
@isnad1 id=eq.1h3v.s6.6c550402893d from=translated src=- shape=e93cc281 vocab=ba509090
-/
lemma alternatingPowerSum_eq_neg_factorial_coeff
    {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (n : ℕ) (hn : 1 ≤ n) :
    G.alternatingPowerSum n = -((n.factorial : ℚ) * (PowerSeries.coeff n) (QExpSeries G)) := by
  rw [alternatingPowerSum_eq_coeff_hilbert_exp G n hn, hilbertNumerator_exp_eq_Q_exp]

/--
@isnad1 id=eq.0h3v.s8.e91c82001a3b from=translated src=- shape=ba1d8672 vocab=228fa1d6
-/
lemma C_m_plus_p_formula {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    G.alternatingPowerSum (G.m + p) =
    ((-1 : ℚ)^G.m * (G.piM : ℚ) * ((G.m + p).factorial : ℚ) *
      (PowerSeries.coeff (p + 1)) G.BSeries) +
    ((-1 : ℚ)^G.m * (G.piM : ℚ) *
      ∑ r ∈ Finset.range (p + 1),
        ((G.m + p).choose r : ℚ) * ((G.m + p - r).factorial : ℚ) *
          (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r) := by
  have hmp : 1 ≤ G.m + p := Nat.le_add_right 1 p |>.trans (Nat.add_le_add_right G.hm_pos p)
  rw [alternatingPowerSum_eq_neg_factorial_coeff G (G.m + p) hmp]
  rw [Q_exp_coeff_at_m_plus_p]
  have h_gap := gap_term_final_form G p
  calc -((↑(G.m + p).factorial : ℚ) *
          ((-1) ^ (G.m + 1) * ↑G.piM *
            ((PowerSeries.coeff (p + 1)) G.BSeries +
             ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
               (PowerSeries.coeff (p - r)) G.ASeries * (↑g) ^ r / (↑r.factorial))))
      = (-1) ^ G.m * ↑G.piM * ↑(G.m + p).factorial * (PowerSeries.coeff (p + 1)) G.BSeries +
        (-1) ^ G.m * ↑G.piM * (↑(G.m + p).factorial *
          ∑ g ∈ S.gaps, ∑ r ∈ Finset.range (p + 1),
            (PowerSeries.coeff (p - r)) G.ASeries * (↑g) ^ r / (↑r.factorial)) := by ring
    _ = (-1) ^ G.m * ↑G.piM * ↑(G.m + p).factorial * (PowerSeries.coeff (p + 1)) G.BSeries +
        (-1) ^ G.m * ↑G.piM *
          ∑ r ∈ Finset.range (p + 1),
            ↑((G.m + p).choose r) * ↑(G.m + p - r).factorial *
              (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by rw [h_gap]

/--
@isnad1 id=eq.0h3v.s8.36fe2e43f063 from=translated src=- shape=45fc5bd3 vocab=4485b52d
-/
lemma K_invariant_expanded {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    G.KInvariant p =
    (p.factorial : ℚ) * (PowerSeries.coeff (p + 1)) G.BSeries +
    ∑ r ∈ Finset.range (p + 1),
      ((p.factorial : ℚ) / (r.factorial : ℚ)) *
        (PowerSeries.coeff (p - r)) G.ASeries * S.gapPowerSum r := by
  unfold NumericalSemigroupGenerators.KInvariant
  rw [C_m_plus_p_formula, mul_add]
  have hpi : 0 < G.piM := pi_m_pos G
  rw [bernoulli_term_simplify G.m p G.piM hpi, gap_sum_simplify]

/--
@isnad1 id=eq.0h3v.s7.d7eda4973a8d from=translated src=- shape=a2ab12b3 vocab=62da925f
-/
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

/--
@isnad1 id=eq.1h2v.s5.2ccf67d6290f from=translated src=- shape=668e55cd vocab=8a39cd7a
-/
lemma factorial_div_eq_choose_mul {p r : ℕ} (hr : r ≤ p) :
    (p.factorial : ℚ) / r.factorial = (p.choose r : ℚ) * (p - r).factorial := by
  have h_main : ((p.choose r : ℕ) : ℚ) * (r.factorial : ℚ) *
      ((p - r).factorial : ℚ) = (p.factorial : ℚ) := by
    norm_cast
    rw [← Nat.choose_mul_factorial_mul_factorial hr]
  have h_r_pos : (r.factorial : ℚ) ≠ 0 := by positivity
  field_simp [h_r_pos]
  linarith

/--
@isnad1 id=eq.1h4v.s7.82ae4f01db98 from=translated src=- shape=75ebb7f1 vocab=a9382721
-/
lemma A_coeff_to_T_sigma {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p r : ℕ)
    (hr : r ≤ p) :
    ((p.factorial : ℚ) / (r.factorial : ℚ)) * (PowerSeries.coeff (p - r)) G.ASeries =
    (p.choose r : ℚ) * G.TSigma (p - r) := by
  have hfact := factorial_div_eq_choose_mul hr
  unfold NumericalSemigroupGenerators.TSigma
  rw [hfact]
  ring

/--
@isnad1 id=eq.0h3v.s7.d8c8d7c3d66f from=translated src=- shape=c4b7be2b vocab=56c168b6
-/
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

/--
@isnad1 id=eq.0h3v.s7.716d2de3139a from=translated src=- shape=43e6224c vocab=20a748a4
-/
lemma fels_conjecture_main {S : NumericalSemigroup} (G : NumericalSemigroupGenerators S) (p : ℕ) :
    G.KInvariant p =
      ∑ r ∈ Finset.range (p + 1),
        (p.choose r : ℚ) * G.TSigma (p - r) * S.gapPowerSum r +
      (2 ^ (p + 1) : ℚ) / ((p : ℚ) + 1) * G.TDelta (p + 1) := by
  rw [K_invariant_expanded]
  rw [bernoulli_coeff_to_T_delta]
  rw [sum_A_coeff_eq_sum_T_sigma]
  ring

end FelsConjectureProof

/--
@isnad1 id=eq.0h3v.s7.716d2de3139a from=translated src=- shape=43e6224c vocab=20a748a4
-/
theorem _root_.Tengoku.LeanPool.fels_conjecture (S : NumericalSemigroup) (G : NumericalSemigroupGenerators S) (p : ℕ) :
    G.KInvariant p =
      ∑ r ∈ Finset.range (p + 1),
        (p.choose r : ℚ) * G.TSigma (p - r) * S.gapPowerSum r +
      (2 ^ (p + 1) : ℚ) / ((p : ℚ) + 1) * G.TDelta (p + 1) :=
  FelsConjectureProof.fels_conjecture_main G p
-- Tengoku: root names of this library moved to Tengoku.LeanPool so they do not collide with other libraries (generated)
