/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.KernelReduction
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.RationalSpace
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Frame

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

open scoped _root_.Matrix

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def centroidHeight (x : V)
    (c : IntegralGramLattice G x) :
    ratGramSpace G x →ₗ[ℚ] ℚ :=
  (1 / 15 : ℚ) • ratGramForm G x (toRatSpace G x c)

theorem centroidHeight_apply (x : V)
    (c : IntegralGramLattice G x) (z : ratGramSpace G x) :
    centroidHeight G x c z =
      (1 / 15 : ℚ) * ratGramForm G x (toRatSpace G x c) z := by
  rfl

@[simp]
theorem centroidHeight_generator
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    centroidHeight G x c
        (toRatSpace G x (integralGramGenerator G x B)) = 1 := by
  rw [centroidHeight_apply, toRatSpace_pairing,
    integral_centroid_pairing_generator G hG x c hc B]
  norm_num

@[simp]
theorem centroidHeight_centroid
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    centroidHeight G x c (toRatSpace G x c) = 20 := by
  rw [centroidHeight_apply, toRatSpace_pairing,
    integral_centroid_norm G hG x c hc]
  norm_num

noncomputable def centroidRankOneForm (x : V)
    (c : IntegralGramLattice G x) :
    LinearMap.BilinForm ℚ (ratGramSpace G x) :=
  LinearMap.mk₂ ℚ
    (fun u v => centroidHeight G x c u * centroidHeight G x c v)
    (by intros; simp [add_mul])
    (by intros; simp [mul_assoc])
    (by intros; simp [mul_add])
    (by intros; simp [mul_left_comm])

noncomputable def lorentzGramForm (x : V)
    (c : IntegralGramLattice G x) :
    LinearMap.BilinForm ℚ (ratGramSpace G x) :=
  ratGramForm G x - centroidRankOneForm G x c

@[simp]
theorem lorentzGramForm_apply (x : V)
    (c : IntegralGramLattice G x) (u v : ratGramSpace G x) :
    lorentzGramForm G x c u v =
      ratGramForm G x u v -
        centroidHeight G x c u * centroidHeight G x c v := by
  rfl

theorem lorentzGramForm_generator_generator
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B C : SecondSubconstituent G x) :
    lorentzGramForm G x c
        (toRatSpace G x (integralGramGenerator G x B))
        (toRatSpace G x (integralGramGenerator G x C)) =
      (localKMatrix G x B C : ℚ) := by
  rw [lorentzGramForm_apply, centroidHeight_generator G hG x c hc B,
    centroidHeight_generator G hG x c hc C, toRatSpace_pairing,
    integralGramPairing_generator_generator]
  simp [localKMatrix]

noncomputable def lorentzWeylVector (x : V)
    (c : IntegralGramLattice G x) : ratGramSpace G x :=
  (1 / 5 : ℚ) • toRatSpace G x c

@[simp]
theorem centroidHeight_weylVector
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    centroidHeight G x c (lorentzWeylVector G x c) = 4 := by
  rw [lorentzWeylVector, map_smul, centroidHeight_centroid G hG x c hc]
  norm_num

@[simp]
theorem lorentzWeylVector_pair_generator
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    lorentzGramForm G x c (lorentzWeylVector G x c)
        (toRatSpace G x (integralGramGenerator G x B)) = -1 := by
  rw [lorentzGramForm_apply]
  have hpair :
      ratGramForm G x (lorentzWeylVector G x c)
          (toRatSpace G x (integralGramGenerator G x B)) = 3 := by
    rw [lorentzWeylVector, map_smul, LinearMap.smul_apply,
      toRatSpace_pairing,
      integral_centroid_pairing_generator G hG x c hc B]
    norm_num
  rw [hpair, centroidHeight_weylVector G hG x c hc,
    centroidHeight_generator G hG x c hc B]
  norm_num

@[simp]
theorem lorentzWeylVector_norm
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    lorentzGramForm G x c (lorentzWeylVector G x c)
        (lorentzWeylVector G x c) = -4 := by
  rw [lorentzGramForm_apply]
  have hnorm :
      ratGramForm G x (lorentzWeylVector G x c)
          (lorentzWeylVector G x c) = 12 := by
    simp only [lorentzWeylVector, map_smul, LinearMap.smul_apply,
      smul_eq_mul]
    rw [toRatSpace_pairing, integral_centroid_norm G hG x c hc]
    norm_num
  rw [hnorm, centroidHeight_weylVector G hG x c hc]
  norm_num

@[simp]
theorem lorentzWeylVector_pair
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (z : ratGramSpace G x) :
    lorentzGramForm G x c (lorentzWeylVector G x c) z =
      -centroidHeight G x c z := by
  rw [lorentzGramForm_apply,
    centroidHeight_weylVector G hG x c hc, lorentzWeylVector,
    map_smul, LinearMap.smul_apply, centroidHeight_apply]
  ring

theorem lorentzGramForm_isSymm (x : V)
    (c : IntegralGramLattice G x) :
    (lorentzGramForm G x c).IsSymm := by
  constructor
  intro z w
  rw [lorentzGramForm_apply, lorentzGramForm_apply,
    (ratGramForm_isSymm G x).eq z w]
  ring

theorem lorentz_integral_frame_identity
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    ∑ C, localKMatrix G x B C • integralGramGenerator G x C =
      (45 : ℤ) • integralGramGenerator G x B - (5 : ℤ) • c := by
  calc
    (∑ C, localKMatrix G x B C • integralGramGenerator G x C) =
        ∑ C, (localGramMatrix G x B C - 1) •
          integralGramGenerator G x C := by rfl
    _ = (∑ C, localGramMatrix G x B C • integralGramGenerator G x C) -
          integralGramGeneratorSum G x := by
      rw [integralGramGeneratorSum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro C _
      rw [sub_smul, one_smul]
    _ = (45 : ℤ) • integralGramGenerator G x B + (6 : ℤ) • c -
          (11 : ℤ) • c := by
      rw [gram_frame_identity G hG x c hc B, hc]
    _ = (45 : ℤ) • integralGramGenerator G x B - (5 : ℤ) • c := by
      module

theorem lorentzGramForm_nondegenerate
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    (lorentzGramForm G x c).Nondegenerate := by
  have hleft : (lorentzGramForm G x c).SeparatingLeft := by
    intro z hz
    have hheight : centroidHeight G x c z = 0 := by
      have hrho := hz (lorentzWeylVector G x c)
      rw [(lorentzGramForm_isSymm G x c).eq z (lorentzWeylVector G x c),
        lorentzWeylVector_pair G hG x c hc z] at hrho
      linarith
    apply (ratGramForm_nondegenerate G hG x).1 z
    intro w
    have hw := hz w
    rw [lorentzGramForm_apply, hheight, zero_mul, sub_zero] at hw
    exact hw
  refine ⟨hleft, fun z hz => hleft z fun w => ?_⟩
  rw [(lorentzGramForm_isSymm G x c).eq z w]
  exact hz w

@[simp]
theorem lorentzGramForm_pair_centroid
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (z : ratGramSpace G x) :
    lorentzGramForm G x c z (toRatSpace G x c) =
      -5 * centroidHeight G x c z := by
  rw [lorentzGramForm_apply, centroidHeight_centroid G hG x c hc,
    (ratGramForm_isSymm G x).eq z (toRatSpace G x c),
    centroidHeight_apply]
  ring

theorem eq_zero_of_lorentzPairing_generators_eq_zero
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (z : ratGramSpace G x)
    (hz : ∀ B, lorentzGramForm G x c
      (toRatSpace G x (integralGramGenerator G x B)) z = 0) :
    z = 0 := by
  refine (lorentzGramForm_nondegenerate G hG x c hc).2 z fun w => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [ratGramSpace_mk_eq_sum_smul_generator, map_sum,
    LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun B _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, hz B, mul_zero]

theorem lorentz_rat_frame_identity
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (y : ratGramSpace G x) :
    ∑ C, lorentzGramForm G x c y
        (toRatSpace G x (integralGramGenerator G x C)) •
          toRatSpace G x (integralGramGenerator G x C) =
      (45 : ℚ) • y -
        (5 * centroidHeight G x c y) • toRatSpace G x c := by
  apply sub_eq_zero.mp
  apply eq_zero_of_lorentzPairing_generators_eq_zero G hG x c hc
  intro D
  have hframe := congrArg (toRatSpace G x)
    (lorentz_integral_frame_identity G hG x c hc D)
  have hpair := congrArg (fun z => lorentzGramForm G x c y z) hframe
  simp only [map_sum, map_zsmul, map_sub, zsmul_eq_mul] at hpair
  simp only [map_sum, map_smul, map_sub, smul_eq_mul]
  simp_rw [lorentzGramForm_generator_generator G hG x c hc D]
  rw [(lorentzGramForm_isSymm G x c).eq
      (toRatSpace G x (integralGramGenerator G x D)) y,
    lorentzGramForm_pair_centroid G hG x c hc,
    centroidHeight_generator G hG x c hc D]
  rw [lorentzGramForm_pair_centroid G hG x c hc] at hpair
  have hpair' :
      ∑ C, lorentzGramForm G x c y
          (toRatSpace G x (integralGramGenerator G x C)) *
            (localKMatrix G x D C : ℚ) =
        (45 : ℚ) * lorentzGramForm G x c y
            (toRatSpace G x (integralGramGenerator G x D)) -
          (5 : ℚ) * (-5 * centroidHeight G x c y) := by
    calc
      _ = ∑ C, (localKMatrix G x D C : ℚ) *
          lorentzGramForm G x c y
            (toRatSpace G x (integralGramGenerator G x C)) := by
        apply Finset.sum_congr rfl
        intro C _
        ring
      _ = _ := hpair
  linear_combination hpair'

theorem lorentz_dual_denominator
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    ∀ y ∈ (lorentzGramForm G x c).dualSubmodule (gramLattice G x),
      (45 : ℤ) • y ∈ gramLattice G x := by
  classical
  intro y hy
  have hint : ∀ a : IntegralGramLattice G x,
      ∃ n : ℤ, (n : ℚ) = lorentzGramForm G x c y (toRatSpace G x a) := by
    intro a
    exact Submodule.mem_one.mp
      (hy _ (toRatSpace_mem_gramLattice G x a))
  choose n hn using fun B => hint (integralGramGenerator G x B)
  obtain ⟨m, hm⟩ := hint c
  set z : IntegralGramLattice G x :=
    ∑ B, n B • integralGramGenerator G x B with hzdef
  refine ⟨z - m • c, ?_⟩
  have hframe := lorentz_rat_frame_identity G hG x c hc y
  calc
    toRatSpace G x (z - m • c) =
        (∑ B, (n B : ℚ) •
          toRatSpace G x (integralGramGenerator G x B)) -
            (m : ℚ) • toRatSpace G x c := by
      simp only [map_sub, hzdef, map_sum, map_zsmul,
        ← Int.cast_smul_eq_zsmul ℚ]
    _ = (∑ B, lorentzGramForm G x c y
          (toRatSpace G x (integralGramGenerator G x B)) •
            toRatSpace G x (integralGramGenerator G x B)) -
          lorentzGramForm G x c y (toRatSpace G x c) •
            toRatSpace G x c := by
      simp only [hn, hm]
    _ = ((45 : ℚ) • y -
          (5 * centroidHeight G x c y) • toRatSpace G x c) -
          (-5 * centroidHeight G x c y) • toRatSpace G x c := by
      rw [hframe, lorentzGramForm_pair_centroid G hG x c hc]
    _ = (45 : ℤ) • y := by
      module

noncomputable def lorentzHeightZeroPart
    (x : V) (c : IntegralGramLattice G x)
    (z : ratGramSpace G x) : ratGramSpace G x :=
  z - (centroidHeight G x c z / 4) • lorentzWeylVector G x c

@[simp]
theorem centroidHeight_heightZeroPart
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (z : ratGramSpace G x) :
    centroidHeight G x c (lorentzHeightZeroPart G x c z) = 0 := by
  rw [lorentzHeightZeroPart, map_sub, map_smul,
    centroidHeight_weylVector G hG x c hc]
  ring

theorem lorentzGramForm_heightZeroPart
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (z w : ratGramSpace G x) :
    lorentzGramForm G x c (lorentzHeightZeroPart G x c z)
        (lorentzHeightZeroPart G x c w) =
      lorentzGramForm G x c z w +
        centroidHeight G x c z * centroidHeight G x c w / 4 := by
  simp only [lorentzHeightZeroPart, map_sub, LinearMap.sub_apply, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  rw [lorentzWeylVector_pair G hG x c hc w,
    (lorentzGramForm_isSymm G x c).eq z (lorentzWeylVector G x c),
    lorentzWeylVector_pair G hG x c hc z,
    lorentzWeylVector_norm G hG x c hc]
  ring

theorem lorentzHeightZeroPart_generator_generator
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B C : SecondSubconstituent G x) :
    lorentzGramForm G x c
        (lorentzHeightZeroPart G x c
          (toRatSpace G x (integralGramGenerator G x B)))
        (lorentzHeightZeroPart G x c
          (toRatSpace G x (integralGramGenerator G x C))) =
      (localKMatrix G x B C : ℚ) + 1 / 4 := by
  rw [lorentzGramForm_heightZeroPart G hG x c hc,
    lorentzGramForm_generator_generator G hG x c hc B C,
    centroidHeight_generator G hG x c hc B,
    centroidHeight_generator G hG x c hc C]
  ring

@[simp]
theorem lorentzHeightZeroPart_generator_norm
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    lorentzGramForm G x c
        (lorentzHeightZeroPart G x c
          (toRatSpace G x (integralGramGenerator G x B)))
        (lorentzHeightZeroPart G x c
          (toRatSpace G x (integralGramGenerator G x B))) = 9 / 4 := by
  rw [lorentzHeightZeroPart_generator_generator G hG x c hc B B,
    localKMatrix_diagonal G hG x B]
  norm_num

theorem lorentzGramForm_eq_ratGramForm_of_height_zero
    (x : V) (c : IntegralGramLattice G x) (z : ratGramSpace G x)
    (hz : centroidHeight G x c z = 0) :
    lorentzGramForm G x c z z = ratGramForm G x z z := by
  rw [lorentzGramForm_apply, hz]
  ring

theorem lorentz_height_decomposition
    (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (z : ratGramSpace G x) :
    let a : ℚ := centroidHeight G x c z / 4
    let z₀ := z - a • lorentzWeylVector G x c
    centroidHeight G x c z₀ = 0 ∧
      z = z₀ + a • lorentzWeylVector G x c := by
  dsimp only
  constructor
  · rw [map_sub, map_smul, centroidHeight_weylVector G hG x c hc]
    ring
  · module

end SRG266
