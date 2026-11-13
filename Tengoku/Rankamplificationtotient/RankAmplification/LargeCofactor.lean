import Tengoku.Rankamplificationtotient.RankAmplification.SmoothFactorPairs
import Tengoku.Rankamplificationtotient.RankAmplification.MertensComparison
import Tengoku.Rankamplificationtotient.RankAmplification.ShiftedCoprime

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The large-cofactor provider sum This module formalizes the finite algebra and counting reductions in (4.3)--(4.6). -/

namespace RankAmplification

open scoped BigOperators

noncomputable section

/-- Smoothness is inherited by a positive divisor.
@isnad1 id=issmooth.3h3v.s4.dfafa5da0486 from=translated src=- shape=dd668470 vocab=1bbfea8e
-/
theorem IsSmooth.of_dvd {R m n : ℕ} (hn : IsSmooth R n) (hm : m ∣ n) (hm0 : m ≠ 0) :
    IsSmooth R m := by
  refine ⟨hm0, fun p hp ↦ hn.2 p ?_⟩
  exact Nat.primeFactors_mono hm hn.1 hp

/-- The exact finite reciprocal sum over positive `R`-smooth integers at most `X`.-/
def finiteSmoothReciprocalSum (R X : ℕ) : ℝ :=
  ∑ k ∈ finiteSmoothSet R X, (k : ℝ)⁻¹

/-- A finite smooth reciprocal sum is bounded by the complete Euler product.
@isnad1 id=le.0h2v.s3.51070f815450 from=translated src=- shape=685c8dd1 vocab=7e5ead67
-/
theorem finiteSmoothReciprocalSum_le_mertensProduct (R X : ℕ) :
    finiteSmoothReciprocalSum R X ≤ mertensProduct R := by
  let e : {m : ℕ // m ∈ finiteSmoothSet R X} ↪ (R + 1).smoothNumbers :=
    { toFun := fun m ↦
        ⟨m.1, isSmooth_iff_mem_smoothNumbers_succ.mp
          (mem_finiteSmoothSet.mp m.2).2.2⟩
      inj' := fun a b hab ↦ Subtype.ext <|
        congrArg (fun z : (R + 1).smoothNumbers ↦ (z : ℕ)) hab }
  let A : Finset ((R + 1).smoothNumbers) := Finset.univ.map e
  have hsmooth := (summable_and_hasSum_smooth_reciprocals R).2
  have hle : (∑ m ∈ A, ((m.1 : ℝ)⁻¹)) ≤ mertensProduct R := by
    calc
      (∑ m ∈ A, ((m.1 : ℝ)⁻¹)) ≤
          ∑' m : (R + 1).smoothNumbers, ((m.1 : ℝ)⁻¹) :=
        hsmooth.summable.sum_le_tsum A (fun m _ ↦ inv_nonneg.mpr (Nat.cast_nonneg m.1))
      _ = mertensProduct R := hsmooth.tsum_eq
  have hfinite : finiteSmoothReciprocalSum R X =
      ∑ m : {m : ℕ // m ∈ finiteSmoothSet R X}, ((m.1 : ℝ)⁻¹) := by
    rw [finiteSmoothReciprocalSum, ← Finset.sum_attach, Finset.attach_eq_univ]
  have hmap :
      (∑ m : {m : ℕ // m ∈ finiteSmoothSet R X}, ((m.1 : ℝ)⁻¹)) =
        ∑ m ∈ A, ((m.1 : ℝ)⁻¹) := by
    change (∑ m : {m : ℕ // m ∈ finiteSmoothSet R X}, ((m.1 : ℝ)⁻¹)) =
      ∑ m ∈ Finset.univ.map e, ((m.1 : ℝ)⁻¹)
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro m _
    rfl
  rw [hfinite, hmap]
  exact hle

/-- The finite sum of reciprocal provider forms `kp+1`.-/
def finiteProviderReciprocalSum (p X : ℕ) : ℝ :=
  ∑ k ∈ finiteSmoothSet p X, ((k * p + 1 : ℕ) : ℝ)⁻¹

/-- Dropping the `+1` in a provider form produces the factor `1/p`.
@isnad1 id=le.1h2v.s5.7a2cc4fdd0e2 from=translated src=- shape=9b91eef5 vocab=eb62246f
-/
theorem finiteProviderReciprocalSum_le (p X : ℕ) (hp : 0 < p) :
    finiteProviderReciprocalSum p X ≤ (p : ℝ)⁻¹ * finiteSmoothReciprocalSum p X := by
  unfold finiteProviderReciprocalSum finiteSmoothReciprocalSum
  calc
    (∑ k ∈ finiteSmoothSet p X, ((k * p + 1 : ℕ) : ℝ)⁻¹) ≤
        ∑ k ∈ finiteSmoothSet p X, (p : ℝ)⁻¹ * (k : ℝ)⁻¹ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkpos : 0 < k := (mem_finiteSmoothSet.mp hk).1
      have hden : (0 : ℝ) < (k * p : ℕ) := by positivity
      calc
        (((k * p + 1 : ℕ) : ℝ)⁻¹) ≤ (((k * p : ℕ) : ℝ)⁻¹) := by
          exact inv_anti₀ hden (by exact_mod_cast Nat.le_add_right (k * p) 1)
        _ = (p : ℝ)⁻¹ * (k : ℝ)⁻¹ := by
          norm_num [mul_inv_rev, mul_comm]
    _ = (p : ℝ)⁻¹ * ∑ k ∈ finiteSmoothSet p X, (k : ℝ)⁻¹ := by
      rw [Finset.mul_sum]

/-- Mertens' product controls the complete finite provider reciprocal sum.
@isnad1 id=le.1h2v.s5.6657b6b6e407 from=translated src=- shape=6aec6afa vocab=950d2ca3
-/
theorem finiteProviderReciprocalSum_le_mertensProduct (p X : ℕ) (hp : 0 < p) :
    finiteProviderReciprocalSum p X ≤ (p : ℝ)⁻¹ * mertensProduct p := by
  exact (finiteProviderReciprocalSum_le p X hp).trans
    (mul_le_mul_of_nonneg_left (finiteSmoothReciprocalSum_le_mertensProduct p X)
      (inv_nonneg.mpr (Nat.cast_nonneg p)))

/-- Explicit version of the inner estimate used in (4.5).
@isnad1 id=le.1h2v.s6.1d1d89be5bc5 from=translated src=- shape=75adeecb vocab=c783d833
-/
theorem finiteProviderReciprocalSum_le_log (p X : ℕ) (hp : 3 ≤ p) :
    finiteProviderReciprocalSum p X ≤
      (p : ℝ)⁻¹ * (Real.exp (4 * Real.log 4) * (1 + Real.log p)) := by
  exact (finiteProviderReciprocalSum_le_mertensProduct p X (by omega)).trans
    (mul_le_mul_of_nonneg_left (mertensProduct_le_log p hp)
      (inv_nonneg.mpr (Nat.cast_nonneg p)))

/-- The reciprocal part of the pair majorant in (4.3).-/
def smoothProviderPairReciprocalSum (p X : ℕ) : ℝ :=
  ∑ k ∈ smoothFactorPairSet p X,
    (((k.1 * p + 1) * (k.2 * p + 1) : ℕ) : ℝ)⁻¹

/-- Every smooth factor pair lies in the Cartesian square of the one-variable smooth set.
@isnad1 id=le.0h2v.s5.a43a6ef88a43 from=translated src=- shape=605117e0 vocab=da5b4a65
-/
theorem smoothFactorPairSet_subset_product (R X : ℕ) :
    smoothFactorPairSet R X ⊆ finiteSmoothSet R X ×ˢ finiteSmoothSet R X := by
  intro k hk
  obtain ⟨hk₁, hk₂, hkprod, hsmooth⟩ := mem_smoothFactorPairSet.mp hk
  have hk₁le : k.1 ≤ X := by
    calc
      k.1 = k.1 * 1 := (Nat.mul_one k.1).symm
      _ ≤ k.1 * k.2 := Nat.mul_le_mul_left k.1 hk₂
      _ ≤ X := hkprod
  have hk₂le : k.2 ≤ X := by
    calc
      k.2 = 1 * k.2 := (Nat.one_mul k.2).symm
      _ ≤ k.1 * k.2 := Nat.mul_le_mul_right k.2 hk₁
      _ ≤ X := hkprod
  have hsmooth₁ : IsSmooth R k.1 :=
    hsmooth.of_dvd (dvd_mul_right k.1 k.2) (Nat.one_le_iff_ne_zero.mp hk₁)
  have hsmooth₂ : IsSmooth R k.2 :=
    hsmooth.of_dvd (dvd_mul_left k.2 k.1) (Nat.one_le_iff_ne_zero.mp hk₂)
  exact Finset.mem_product.mpr
    ⟨mem_finiteSmoothSet.mpr ⟨hk₁, hk₁le, hsmooth₁⟩,
      mem_finiteSmoothSet.mpr ⟨hk₂, hk₂le, hsmooth₂⟩⟩

/-- Enlarging to the Cartesian square factorizes the reciprocal provider sum.
@isnad1 id=le.0h2v.s4.846309e4022b from=translated src=- shape=c1d68589 vocab=9853c60e
-/
theorem smoothProviderPairReciprocalSum_le_sq (p X : ℕ) :
    smoothProviderPairReciprocalSum p X ≤ (finiteProviderReciprocalSum p X) ^ 2 := by
  let term : ℕ × ℕ → ℝ := fun k ↦
    (((k.1 * p + 1) * (k.2 * p + 1) : ℕ) : ℝ)⁻¹
  have hnonneg : ∀ k ∈ finiteSmoothSet p X ×ˢ finiteSmoothSet p X, 0 ≤ term k := by
    intro k _
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  calc
    smoothProviderPairReciprocalSum p X =
        ∑ k ∈ smoothFactorPairSet p X, term k := rfl
    _ ≤ ∑ k ∈ finiteSmoothSet p X ×ˢ finiteSmoothSet p X, term k :=
      Finset.sum_le_sum_of_subset_of_nonneg (smoothFactorPairSet_subset_product p X)
        (fun k hk _ ↦ hnonneg k hk)
    _ = (finiteProviderReciprocalSum p X) ^ 2 := by
      rw [Finset.sum_product, finiteProviderReciprocalSum, pow_two]
      simp only [term, Nat.cast_mul, mul_inv_rev]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k₁ hk₁
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k₂ hk₂
      rw [mul_comm]

/-- The complete per-prime finite majorant, before estimating either summand.-/
def smoothProviderPairMajorant (x p X : ℕ) : ℝ :=
  ∑ k ∈ smoothFactorPairSet p X,
    ((x : ℝ) / ((k.1 * p + 1) * (k.2 * p + 1)) + 1)

/-- Exact split of the per-prime majorant into (4.3) and (4.4).
@isnad1 id=eq.0h3v.s5.762c0723c251 from=translated src=- shape=6725dc4b vocab=3c1b0bd7
-/
theorem smoothProviderPairMajorant_eq (x p X : ℕ) :
    smoothProviderPairMajorant x p X =
      (x : ℝ) * smoothProviderPairReciprocalSum p X +
        finiteDivisorWeightedSmoothCount p X := by
  rw [smoothProviderPairMajorant, smoothProviderPairReciprocalSum,
    ← card_smoothFactorPairSet_cast_eq]
  simp only [div_eq_mul_inv, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    norm_num
  · simp

/-- Finite (4.3)--(4.6): the reciprocal term is bounded by a square, while the number of admissible pairs is exactly the divisor-weighted smooth census.
@isnad1 id=le.0h3v.s5.c639fe5b80eb from=translated src=- shape=3209d344 vocab=e32c335f
-/
theorem smoothProviderPairMajorant_le (x p X : ℕ) :
    smoothProviderPairMajorant x p X ≤
      (x : ℝ) * (finiteProviderReciprocalSum p X) ^ 2 +
        finiteDivisorWeightedSmoothCount p X := by
  rw [smoothProviderPairMajorant_eq]
  simpa [add_comm] using add_le_add_right
    (mul_le_mul_of_nonneg_left (smoothProviderPairReciprocalSum_le_sq p X)
      (Nat.cast_nonneg x)) (finiteDivisorWeightedSmoothCount p X)

namespace LargePrimeSkeleton

variable {h n p : ℕ} (s : LargePrimeSkeleton h n p)

/-- The provider product is the product of the two affine forms.
@isnad1 id=eq.0h4v.s6.967665d735de from=translated src=- shape=4f4345eb vocab=2df2d527
-/
theorem provider_product_eq :
    s.q1 * s.q2 = (s.k1 * p + 1) * (s.k2 * p + 1) := by
  rw [s.q1_eq, s.q2_eq]

/-- Cofactors and providers give an exact factorization of the shifted product.
@isnad1 id=eq.0h4v.s6.b2bd5f7a758b from=translated src=- shape=a123fad8 vocab=ad852536
-/
theorem cofactor_provider_factorization :
    n * (n + h) = (s.m1 * s.m2) * (s.q1 * s.q2) := by
  calc
    n * (n + h) = (s.m1 * s.q1) * (s.m2 * s.q2) :=
      congrArg₂ (· * ·) s.n_eq s.shifted_eq
    _ = (s.m1 * s.m2) * (s.q1 * s.q2) := by ring

/-- The paper's elementary `q₁q₂ ≤ 2xy` cutoff in the large-cofactor range.
@isnad1 id=le.5h6v.s6.5fe861aeb519 from=translated src=- shape=6a75ac2c vocab=96738ad4
-/
theorem provider_product_le_two_mul_xy {x y : ℕ} (hnx : n ≤ x) (hy : 0 < y)
    (hhy : h ≤ y) (hxy : y ≤ x) (hlarge : x / y < s.m1 * s.m2) :
    s.q1 * s.q2 ≤ 2 * x * y := by
  have hn : 0 < n := by
    rw [s.n_eq]
    exact Nat.mul_pos s.m1_pos s.q1_prime.pos
  have hx : 0 < x := hn.trans_le hnx
  have hxlt : x < y * (s.m1 * s.m2) := by
    simpa [mul_comm] using (Nat.div_lt_iff_lt_mul hy).mp hlarge
  have hnshift : n + h ≤ 2 * x := by
    have hhx : h ≤ x := hhy.trans hxy
    omega
  have hupper : n * (n + h) ≤ x * (2 * x) := Nat.mul_le_mul hnx hnshift
  by_contra hnot
  have hq : 2 * x * y < s.q1 * s.q2 := Nat.lt_of_not_ge hnot
  have hleft : x * (2 * x) < (s.m1 * s.m2) * (2 * x * y) := by
    calc
      x * (2 * x) = (2 * x) * x := by ring
      _ < (2 * x) * (y * (s.m1 * s.m2)) :=
        Nat.mul_lt_mul_of_pos_left hxlt (by omega)
      _ = (s.m1 * s.m2) * (2 * x * y) := by ring
  have hright : (s.m1 * s.m2) * (2 * x * y) <
      (s.m1 * s.m2) * (s.q1 * s.q2) :=
    Nat.mul_lt_mul_of_pos_left hq (Nat.mul_pos s.m1_pos s.m2_pos)
  have hcontra : n * (n + h) < (s.m1 * s.m2) * (s.q1 * s.q2) :=
    hupper.trans_lt (hleft.trans hright)
  rw [← s.cofactor_provider_factorization] at hcontra
  exact (Nat.lt_irrefl _ hcontra)

/-- Consequently the multiplier product has the precise divisor cutoff in (4.6).
@isnad1 id=le.6h6v.s7.0380801a51ab from=translated src=- shape=813503ce vocab=da706bf6
-/
theorem multiplier_product_le_large_cofactor_cutoff {x y : ℕ} (hnx : n ≤ x)
    (hp : 0 < p) (hy : 0 < y) (hhy : h ≤ y) (hxy : y ≤ x)
    (hlarge : x / y < s.m1 * s.m2) :
    s.k1 * s.k2 ≤ (2 * x * y) / p ^ 2 := by
  apply multiplier_product_le_div_sq hp
  rw [← s.provider_product_eq]
  exact s.provider_product_le_two_mul_xy hnx hy hhy hxy hlarge

/-- A large-cofactor skeleton contributes an admissible pair to the smooth census in (4.6).
@isnad1 id=mem.6h6v.s7.b8a6235bb1ea from=translated src=- shape=c4d26c34 vocab=a10ed19a
-/
theorem multiplier_pair_mem_large_cofactor_set {x y : ℕ} (hnx : n ≤ x)
    (hp : 0 < p) (hy : 0 < y) (hhy : h ≤ y) (hxy : y ≤ x)
    (hlarge : x / y < s.m1 * s.m2) :
    (s.k1, s.k2) ∈ smoothFactorPairSet p ((2 * x * y) / p ^ 2) := by
  exact mem_smoothFactorPairSet.mpr
    ⟨s.k1_pos, s.k2_pos,
      s.multiplier_product_le_large_cofactor_cutoff hnx hp hy hhy hxy hlarge,
      s.multipliers_smooth⟩

/-- Every skeleton number lies in the shifted divisibility class of its provider primes.
@isnad1 id=mem.1h5v.s5.59e39842b114 from=translated src=- shape=051ec2bc vocab=dc206f55
-/
theorem mem_shiftedDivisibilitySet {x : ℕ} (hnx : n ≤ x) :
    n ∈ RankAmplification.shiftedDivisibilitySet x h s.q1 s.q2 := by
  exact RankAmplification.mem_shiftedDivisibilitySet.mpr
    ⟨by rw [s.n_eq]; exact Nat.mul_pos s.m1_pos s.q1_prime.pos,
      hnx, s.q1_dvd, s.q2_dvd⟩

end LargePrimeSkeleton

end

end RankAmplification
