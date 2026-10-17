import Tengoku.OpenaiMath.OAI.Analysis.C0Absorption.Detection

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

abbrev BandGrid (j : ℕ) := Fin j → GridIndex (2^j)
abbrev PrefixCube (j : ℕ) := Fin j → Icc (-1 : ℝ) 1

def bandPoint (j : ℕ) (ξ : BandGrid j) : PrefixCube j :=
  fun k => gridPoint (2^j) (by positivity) (ξ k)

def prefixRestrict (j : ℕ) (s : C0Ball) : PrefixCube j := fun k =>
  ⟨s.val k, abs_le.mp ((c0_norm_apply_le s.val k).trans (by
    have hh := s.property
    simpa only [Metric.mem_closedBall,dist_zero_right] using hh))⟩

/--
@isnad1 id=lipschit.0h1v.s6.b46ac8bf94da from=translated src=- shape=9d071583 vocab=f0ef46e1
-/
theorem prefixRestrict_lipschitz (j : ℕ) : LipschitzWith 1 (prefixRestrict j) := by
  apply LipschitzWith.of_dist_le_mul
  intro x y
  rw [NNReal.coe_one,one_mul]
  apply (dist_pi_le_iff dist_nonneg).mpr
  intro k
  exact BoundedContinuousFunction.dist_coe_le_dist (f := x.val.toBCF) (g := y.val.toBCF) k

def bandBump (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) : ℝ :=
  max 0 (1-dist s (bandPoint j ξ)/dyadic j)

def bandVector (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) : ℝ :=
  min 1 (max 0 (2-dist s (bandPoint j ξ)/dyadic j))

def bandDenominator (j : ℕ) (s : PrefixCube j) : ℝ := ∑ ξ : BandGrid j, bandBump j ξ s

def bandRow (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) : ℝ :=
  bandBump j ξ s / bandDenominator j s

/--
@isnad1 id=le.0h3v.s4.2081895e1f17 from=translated src=- shape=d78b0cc0 vocab=91b84f9d
-/
theorem bandBump_nonneg (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    0 ≤ bandBump j ξ s := le_max_left _ _

/--
@isnad1 id=le.0h3v.s4.dc177ce3258a from=translated src=- shape=d78b0cc0 vocab=ec5d0dc8
-/
theorem bandVector_nonneg (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    0 ≤ bandVector j ξ s := le_min zero_le_one (le_max_left _ _)

/--
@isnad1 id=le.0h3v.s4.166406560b02 from=translated src=- shape=79967cc3 vocab=ec5d0dc8
-/
theorem bandVector_le_one (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    bandVector j ξ s ≤ 1 := min_le_left _ _

/--
@isnad1 id=eq.1h3v.s5.ca4adfef2b48 from=translated src=- shape=722e1ca5 vocab=c81f1023
-/
theorem bandVector_eq_one {j : ℕ} {ξ : BandGrid j} {s : PrefixCube j}
    (h : bandBump j ξ s ≠ 0) : bandVector j ξ s=1 := by
  have hh : 0 < 1-dist s (bandPoint j ξ)/dyadic j := by
    by_contra hn
    exact h (max_eq_left (by linarith))
  unfold bandVector
  rw [min_eq_left]
  exact le_max_of_le_right (by linarith)

/--
@isnad1 id=lt.1h3v.s6.d6aaccdb6489 from=translated src=- shape=5f6840b1 vocab=1d3a5107
-/
theorem bandVector_support {j : ℕ} {ξ : BandGrid j} {s : PrefixCube j}
    (h : bandVector j ξ s ≠ 0) : dist s (bandPoint j ξ) < 2*dyadic j := by
  have hmax : max 0 (2-dist s (bandPoint j ξ)/dyadic j) ≠ 0 := by
    intro hh
    exact h (by simp only [bandVector,hh,min_eq_right zero_le_one])
  have hh : 0 < 2-dist s (bandPoint j ξ)/dyadic j := by
    by_contra hn
    exact hmax (max_eq_left (by linarith))
  exact (div_lt_iff₀ (dyadic_pos j)).mp (by linarith)

/--
@isnad1 id=lipschit.0h4v.s6.c352d4bc8a41 from=translated src=- shape=8f939144 vocab=4c7eaa27
-/
theorem const_dist_div_lipschitz {X : Type*} [PseudoMetricSpace X] (q : X) (a : ℝ) (j : ℕ) :
    LipschitzWith (2^j) (fun s => a-dist s q/dyadic j) := by
  apply LipschitzWith.of_dist_le_mul
  intro s t
  rw [Real.dist_eq,sub_sub_sub_cancel_left,← sub_div,abs_div,abs_of_pos (dyadic_pos j)]
  calc
    _ ≤ dist t s/dyadic j := div_le_div_of_nonneg_right (abs_dist_sub_le t s q) (dyadic_pos j).le
    _ = (2^j : ℝ≥0)*dist s t := by simp only [dyadic,div_inv_eq_mul,NNReal.coe_pow,NNReal.coe_ofNat,dist_comm]; ring

/--
@isnad1 id=lipschit.0h2v.s6.2d8a41f2e12f from=translated src=- shape=b7202cee vocab=03aa5527
-/
theorem bandBump_lipschitz (j : ℕ) (ξ : BandGrid j) :
    LipschitzWith (2^j) (bandBump j ξ) :=
  (const_dist_div_lipschitz (bandPoint j ξ) 1 j).const_max 0

/--
@isnad1 id=lipschit.0h2v.s6.8c52a7a8b35c from=translated src=- shape=b7202cee vocab=ad764eb6
-/
theorem bandVector_lipschitz (j : ℕ) (ξ : BandGrid j) :
    LipschitzWith (2^j) (bandVector j ξ) :=
  ((const_dist_div_lipschitz (bandPoint j ξ) 2 j).const_max 0).const_min 1

/--
@isnad1 id=le.0h2v.s5.c318318c0d8b from=translated src=- shape=3b32af4f vocab=38b5d391
-/
theorem bandDenominator_ge (j : ℕ) (s : PrefixCube j) : 1/2 ≤ bandDenominator j s := by
  classical
  let ξ : BandGrid j := fun k => nearestGridIndex (2^j) (by positivity) (s k)
  have hd : dist s (bandPoint j ξ) ≤ dyadic j/2 := by
    apply (dist_pi_le_iff (div_nonneg (dyadic_pos j).le (by norm_num) : 0 ≤ dyadic j/2)).mpr
    intro k
    have hh := nearestGrid_dist (2^j) (by positivity) (s k)
    change dist (s k) (gridPoint _ _ (nearestGridIndex _ _ (s k))) ≤ _
    refine hh.trans_eq ?_
    push_cast
    unfold dyadic
    ring
  have hb : 1/2 ≤ bandBump j ξ s := by
    apply le_max_of_le_right
    have hh : dist s (bandPoint j ξ)/dyadic j ≤ 1/2 := (div_le_iff₀ (dyadic_pos j)).mpr (by linarith)
    linarith
  exact hb.trans (Finset.single_le_sum (fun a _ => bandBump_nonneg j a s) (Finset.mem_univ ξ))

/--
@isnad1 id=lt.0h2v.s4.45a9d4ff5b53 from=translated src=- shape=9363a417 vocab=f388688b
-/
theorem bandDenominator_pos (j : ℕ) (s : PrefixCube j) : 0 < bandDenominator j s :=
  lt_of_lt_of_le (by norm_num) (bandDenominator_ge j s)

/--
@isnad1 id=le.0h3v.s4.15f9ce7108e2 from=translated src=- shape=d78b0cc0 vocab=b7e326fd
-/
theorem bandRow_nonneg (j : ℕ) (ξ : BandGrid j) (s : PrefixCube j) :
    0 ≤ bandRow j ξ s := div_nonneg (bandBump_nonneg j ξ s) (bandDenominator_pos j s).le

/--
@isnad1 id=eq.0h2v.s6.2dd81c2c8495 from=translated src=- shape=eb2ee21d vocab=afa9ca37
-/
theorem bandRow_sum (j : ℕ) (s : PrefixCube j) : ∑ ξ : BandGrid j, bandRow j ξ s=1 := by
  simp only [bandRow,← Finset.sum_div]
  change bandDenominator j s/bandDenominator j s=1
  exact div_self (bandDenominator_pos j s).ne'

/--
@isnad1 id=eq.0h2v.s7.2bdd59909a80 from=translated src=- shape=788857ff vocab=d5cfa683
-/
theorem bandRow_vector (j : ℕ) (s : PrefixCube j) :
    ∑ ξ : BandGrid j, bandRow j ξ s*bandVector j ξ s=1 := by
  rw [← bandRow_sum j s]
  apply Finset.sum_congr rfl
  intro ξ _
  by_cases h : bandBump j ξ s=0
  · simp only [bandRow,h,zero_div,zero_mul]
  · rw [bandVector_eq_one h,mul_one]

/--
@isnad1 id=le.4h3v.s7.ef27dd8a1c41 from=translated src=- shape=9e8d57bc vocab=80cc892a
-/
theorem normalized_sum_distance {A : Type*} [Fintype A] (b c : A → ℝ)
    (_hb : ∀ i, 0 ≤ b i) (hc : ∀ i, 0 ≤ c i)
    (hB : 1/2 ≤ ∑ i,b i) (hC : 1/2 ≤ ∑ i,c i) :
    (∑ i, |b i/(∑ i,b i)-c i/(∑ i,c i)|) ≤ 4*∑ i,|b i-c i| := by
  let B := ∑ i,b i
  let C := ∑ i,c i
  have hB' : 0 < B := lt_of_lt_of_le (by norm_num) hB
  have hC' : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hdist : |C-B| ≤ ∑ i,|b i-c i| := by
    rw [abs_sub_comm]
    change |(∑ i,b i)-(∑ i,c i)| ≤ _
    rw [← Finset.sum_sub_distrib]
    exact Finset.abs_sum_le_sum_abs _ _
  have hrow : ∑ i,c i/C=1 := by rw [← Finset.sum_div]; exact div_self hC'.ne'
  have he (i : A) : b i/B-c i/C=(b i-c i)/B+(c i/C)*((C-B)/B) := by
    field_simp
    ; ring
  calc
    _ ≤ ∑ i, (|b i-c i|/B+(c i/C)*(|C-B|/B)) := by
      apply Finset.sum_le_sum
      intro i _
      rw [he]
      refine (abs_add_le _ _).trans_eq ?_
      simp only [abs_mul,abs_div,abs_of_pos hB',abs_of_nonneg (hc i),abs_of_pos hC']
    _ = (∑ i,|b i-c i|)/B+|C-B|/B := by
      rw [Finset.sum_add_distrib,← Finset.sum_div,← Finset.sum_mul,hrow,one_mul]
    _ ≤ (∑ i,|b i-c i|)/B+(∑ i,|b i-c i|)/B :=
      add_le_add_right ((div_le_div_iff_of_pos_right hB').mpr hdist) _
    _ ≤ 4*∑ i,|b i-c i| := by
      have hh : (∑ i,|b i-c i|)/B ≤ 2*∑ i,|b i-c i| := by
        apply (div_le_iff₀ hB').mpr
        have ha : 0 ≤ ∑ i,|b i-c i| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
        nlinarith
      linarith

def bandL (j : ℕ) : ℝ≥0 := 4*Fintype.card (BandGrid j)*2^j

/--
@isnad1 id=le.0h3v.s7.5c58ea870c79 from=translated src=- shape=e850fced vocab=c4dcc4fe
-/
theorem bandRow_distance (j : ℕ) (s t : PrefixCube j) :
    (∑ ξ : BandGrid j,|bandRow j ξ s-bandRow j ξ t|) ≤ bandL j*dist s t := by
  refine (normalized_sum_distance (fun ξ => bandBump j ξ s) (fun ξ => bandBump j ξ t)
    (fun ξ => bandBump_nonneg j ξ s) (fun ξ => bandBump_nonneg j ξ t)
    (bandDenominator_ge j s) (bandDenominator_ge j t)).trans ?_
  calc
    _ ≤ 4*∑ ξ : BandGrid j, (2 : ℝ)^j*dist s t := by
      gcongr with ξ
      simpa only [Real.dist_eq,NNReal.coe_pow,NNReal.coe_ofNat] using
        (bandBump_lipschitz j ξ).dist_le_mul s t
    _ = bandL j*dist s t := by simp [bandL]; ring

end
end C0Absorption

end OAI
