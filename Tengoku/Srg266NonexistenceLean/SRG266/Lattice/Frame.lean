/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.KernelReduction
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.PositiveDefinite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem ratGramForm_zsmul_right (x : V) (v w : ratGramSpace G x) (k : ℤ) :
    ratGramForm G x v (k • w) = (k : ℚ) * ratGramForm G x v w := by
  rw [map_zsmul, zsmul_eq_mul]

theorem ratGramForm_zsmul_left (x : V) (v w : ratGramSpace G x) (k : ℤ) :
    ratGramForm G x (k • v) w = (k : ℚ) * ratGramForm G x v w := by
  calc ratGramForm G x (k • v) w
      = ratGramForm G x w (k • v) := (ratGramForm_isSymm G x).eq _ _
    _ = (k : ℚ) * ratGramForm G x w v := ratGramForm_zsmul_right G x w v k
    _ = (k : ℚ) * ratGramForm G x v w := by rw [(ratGramForm_isSymm G x).eq w v]

theorem ratGramSpace_mk_eq_sum_smul_generator (x : V)
    (a : SecondSubconstituent G x → ℚ) :
    (Submodule.Quotient.mk a : ratGramSpace G x) =
      ∑ B, a B • toRatSpace G x (integralGramGenerator G x B) := by
  have hsum : (∑ B, a B • Pi.single B (1 : ℚ)) = a := by
    funext C
    simp [Pi.single_apply, Finset.sum_ite_eq]
  calc (Submodule.Quotient.mk a : ratGramSpace G x)
      = (rationalGramKernel G x).mkQ (∑ B, a B • Pi.single B (1 : ℚ)) := by
        rw [hsum]; rfl
    _ = ∑ B, a B • toRatSpace G x (integralGramGenerator G x B) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun B _ => ?_
        rw [map_smul, toRatSpace_generator]
        rfl

theorem eq_zero_of_ratPairing_generators_eq_zero (hG : IsHypothetical G) (x : V)
    (v : ratGramSpace G x)
    (h : ∀ B, ratGramForm G x (toRatSpace G x (integralGramGenerator G x B)) v = 0) :
    v = 0 := by
  refine (ratGramForm_nondegenerate G hG x).2 v fun w => ?_
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  rw [ratGramSpace_mk_eq_sum_smul_generator, map_sum, LinearMap.sum_apply]
  refine Finset.sum_eq_zero fun B _ => ?_
  rw [map_smul, LinearMap.smul_apply, smul_eq_mul, h B, mul_zero]

theorem gram_frame_identity (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    ∑ C, localGramMatrix G x B C • integralGramGenerator G x C =
      (45 : ℤ) • integralGramGenerator G x B + (6 : ℤ) • c := by
  refine sub_eq_zero.mp (eq_zero_of_pairing_generators_eq_zero G hG x _ fun D => ?_)
  have hlhs :
      integralGramPairing G x
          (∑ C, localGramMatrix G x B C • integralGramGenerator G x C)
          (integralGramGenerator G x D) =
        ∑ C, localGramMatrix G x B C * localGramMatrix G x C D := by
    rw [map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun C _ => ?_
    rw [map_smul, LinearMap.smul_apply, smul_eq_mul,
      integralGramPairing_generator_generator]
  have hrhs :
      integralGramPairing G x
          ((45 : ℤ) • integralGramGenerator G x B + (6 : ℤ) • c)
          (integralGramGenerator G x D) =
        45 * localGramMatrix G x B D + 6 * 15 := by
    rw [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      map_smul, LinearMap.smul_apply, smul_eq_mul,
      integralGramPairing_generator_generator,
      integral_centroid_pairing_generator G hG x c hc D]
  have hmul :
      (∑ C, localGramMatrix G x B C * localGramMatrix G x C D) =
        45 * localGramMatrix G x B D + 90 := by
    rw [← Matrix.mul_apply, localGramMatrix_sq_apply G hG x B D]
  rw [map_sub, LinearMap.sub_apply, hlhs, hrhs, hmul]
  ring

theorem ratGram_frame_identity (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    ∑ C, (localGramMatrix G x B C) •
        toRatSpace G x (integralGramGenerator G x C) =
      (45 : ℤ) • toRatSpace G x (integralGramGenerator G x B) +
        (6 : ℤ) • toRatSpace G x c := by
  have h := congrArg (toRatSpace G x) (gram_frame_identity G hG x c hc B)
  rw [map_add, map_smul, map_smul, map_sum] at h
  rw [← h]
  exact Finset.sum_congr rfl fun C _ => (map_smul _ _ _).symm

theorem gramLattice_isIntegral (x : V) :
    Lattice.IsIntegral (ratGramForm G x) (gramLattice G x) := by
  rw [Lattice.isIntegral_iff_forall]
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [toRatSpace_pairing]
  exact Submodule.mem_one.mpr ⟨integralGramPairing G x a b, by simp⟩

theorem gramLattice_le_dual (x : V) :
    gramLattice G x ≤ (ratGramForm G x).dualSubmodule (gramLattice G x) :=
  gramLattice_isIntegral G x

theorem gramLattice_dual_isLattice (hG : IsHypothetical G) (x : V) :
    Lattice.IsLattice ℚ ((ratGramForm G x).dualSubmodule (gramLattice G x)) :=
  Lattice.dual_isLattice (ratGramForm G x) (gramLattice_isLattice G x)
    (ratGramForm_nondegenerate G hG x)

theorem gram_dual_denominator (hG : IsHypothetical G) (x : V) :
    ∀ y ∈ (ratGramForm G x).dualSubmodule (gramLattice G x),
      (225 : ℤ) • y ∈ gramLattice G x := by
  classical
  intro y hy
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x

  have hint : ∀ a : IntegralGramLattice G x,
      ∃ k : ℤ, (k : ℚ) = ratGramForm G x (toRatSpace G x a) y := by
    intro a
    obtain ⟨k, hk⟩ := Submodule.mem_one.mp (hy _ (toRatSpace_mem_gramLattice G x a))
    refine ⟨k, ?_⟩
    rw [(ratGramForm_isSymm G x).eq]
    simpa using hk
  choose n hn using fun B => hint (integralGramGenerator G x B)
  obtain ⟨m, hm⟩ := hint c
  set z : IntegralGramLattice G x := ∑ B, n B • integralGramGenerator G x B with hzdef

  have hrow : ∀ D, (∑ B, (localGramMatrix G x D B : ℚ) * (n B : ℚ)) =
      45 * (n D : ℚ) + 6 * (m : ℚ) := by
    intro D
    have hpair := congrArg (fun u => ratGramForm G x u y)
      (ratGram_frame_identity G hG x c hc D)
    simp only [map_sum, LinearMap.sum_apply, map_add, LinearMap.add_apply,
      ratGramForm_zsmul_left] at hpair
    simp only [← hn, ← hm] at hpair
    rw [hpair]
    norm_num

  have hz : ∀ D, ratGramForm G x (toRatSpace G x (integralGramGenerator G x D))
      (toRatSpace G x z) = 45 * (n D : ℚ) + 6 * (m : ℚ) := by
    intro D
    have hcast :
        integralGramPairing G x (integralGramGenerator G x D)
            (∑ B, n B • integralGramGenerator G x B) =
          ∑ B, localGramMatrix G x D B * n B := by
      rw [map_sum]
      refine Finset.sum_congr rfl fun B _ => ?_
      rw [map_smul, smul_eq_mul, integralGramPairing_generator_generator]
      ring
    rw [toRatSpace_pairing, hzdef, hcast]
    push_cast
    exact hrow D

  have hcent : ∀ D, ratGramForm G x (toRatSpace G x (integralGramGenerator G x D))
      (toRatSpace G x c) = 15 := by
    intro D
    rw [toRatSpace_pairing,
      (integralGramPairing_isSymm G x).eq (integralGramGenerator G x D) c,
      integral_centroid_pairing_generator G hG x c hc D]
    norm_num

  refine ⟨(5 : ℤ) • z - (2 * m : ℤ) • c, ?_⟩
  have hkey : (225 : ℤ) • y -
      toRatSpace G x ((5 : ℤ) • z - (2 * m : ℤ) • c) = 0 := by
    refine eq_zero_of_ratPairing_generators_eq_zero G hG x _ fun D => ?_
    have hsplit : toRatSpace G x ((5 : ℤ) • z - (2 * m : ℤ) • c) =
        (5 : ℤ) • toRatSpace G x z - (2 * m : ℤ) • toRatSpace G x c := by
      rw [map_sub, map_smul, map_smul]
    rw [hsplit, map_sub, map_sub]
    simp only [ratGramForm_zsmul_right]
    rw [hz D, hcent D, ← hn D]
    push_cast
    ring
  exact (sub_eq_zero.mp hkey).symm

abbrev gramDualQuotient (x : V) :=
  (ratGramForm G x).dualSubmodule (gramLattice G x) ⧸
    (gramLattice G x).comap
      ((ratGramForm G x).dualSubmodule (gramLattice G x)).subtype

theorem gramDualQuotient_nsmul_eq_zero (hG : IsHypothetical G) (x : V)
    (q : gramDualQuotient G x) : (225 : ℕ) • q = 0 :=
  Lattice.quotient_nsmul_eq_zero
    (fun w hw => by simpa using gram_dual_denominator G hG x w hw) q

theorem gramLattice_dual_quotient_finite (hG : IsHypothetical G) (x : V) :
    Finite (gramDualQuotient G x) :=
  Lattice.finite_quotient_of_nsmul_le
    (gramLattice_dual_isLattice G hG x).fg (n := 225)
    (fun w hw => by simpa using gram_dual_denominator G hG x w hw)

end SRG266
