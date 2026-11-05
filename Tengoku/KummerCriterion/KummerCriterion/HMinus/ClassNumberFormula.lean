module

public import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.ClassGroup
public import Tengoku.KummerCriterion.KummerCriterion.TotallyRealSubfield.ZetaPrime
public import Tengoku.Seed.NumberTheory.NumberField.DedekindZeta
import Tengoku.Seed.Algebra.Polynomial.Degree.IsMonicOfDegree
import Tengoku.Seed.RingTheory.RootsOfUnity.CyclotomicUnits
import Tengoku.Seed.Analysis.SpecialFunctions.Bernstein
import Tengoku.Seed.NumberTheory.ArithmeticFunction.VonMangoldt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Analytic class number formula for `K` and `K⁺`

Rearranged analytic class-number formulas and cyclotomic invariant evaluations for
`K = ℚ(ζ_p)` and its maximal real subfield.
-/

@[expose] public section

noncomputable section

open NumberField
open scoped BigOperators

namespace KummerCriterion

variable (p : ℕ) [hp : Fact p.Prime] (hp_odd : p ≠ 2)
  (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {p} ℚ K] [IsCMField K]

/-- The class number formula for `K`, rearranged to solve for `h`.
@isnad1 id=eq.0h1v.s7.2cf78b97910e from=translated src=- shape=681a96f6 vocab=fbd05ff6
-/
theorem h_formula :
    (h K : ℝ) =
      NumberField.dedekindZeta_residue K *
        (((Units.torsionOrder K : ℝ) * Real.sqrt |discr K|) /
          (2 ^ InfinitePlace.nrRealPlaces K *
            (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K)) := by
  let A : ℝ :=
    2 ^ InfinitePlace.nrRealPlaces K *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K
  let B : ℝ := (Units.torsionOrder K : ℝ) * Real.sqrt |discr K|
  have hA_pos : 0 < A := by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos K)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hA : A ≠ 0 := hA_pos.ne'
  have hB_pos : 0 < B := by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos K
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero K)))
  calc
    (h K : ℝ) = ((A * (h K : ℝ)) / B) * (B / A) := by
      field_simp [hA, hB_pos.ne']
    _ = NumberField.dedekindZeta_residue K * (B / A) := by
          dsimp [A, B]
          rw [NumberField.dedekindZeta_residue_def, KummerCriterion.h, NumberField.classNumber]
    _ = NumberField.dedekindZeta_residue K *
          (((Units.torsionOrder K : ℝ) * Real.sqrt |discr K|) /
            (2 ^ InfinitePlace.nrRealPlaces K *
              (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces K * Units.regulator K)) := by
          simp [A, B]

/-- The class number formula for the maximal real subfield `K⁺`, rearranged to
solve for `h⁺`.
@isnad1 id=eq.0h1v.s8.31393982fa80 from=translated src=- shape=7bddd1a6 vocab=3509593d
-/
theorem hPlus_formula :
    (hPlus K : ℝ) =
      NumberField.dedekindZeta_residue (NumberField.maximalRealSubfield K) *
        (((Units.torsionOrder (NumberField.maximalRealSubfield K) : ℝ) *
            Real.sqrt |discr (NumberField.maximalRealSubfield K)|) /
          (2 ^ InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
            (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) *
              Units.regulator (NumberField.maximalRealSubfield K))) := by
  let L := NumberField.maximalRealSubfield K
  let A : ℝ :=
    2 ^ InfinitePlace.nrRealPlaces L *
      (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L
  let B : ℝ := (Units.torsionOrder L : ℝ) * Real.sqrt |discr L|
  have hA_pos : 0 < A := by
    dsimp [A]
    refine mul_pos ?_ (Units.regulator_pos L)
    exact mul_pos (pow_pos (by positivity) _) (pow_pos (by positivity) _)
  have hA : A ≠ 0 := hA_pos.ne'
  have hB_pos : 0 < B := by
    dsimp [B]
    refine mul_pos ?_ ?_
    · exact_mod_cast Units.torsionOrder_pos L
    · exact Real.sqrt_pos_of_pos (abs_pos.mpr (Int.cast_ne_zero.mpr (discr_ne_zero L)))
  calc
    (hPlus K : ℝ) = ((A * (hPlus K : ℝ)) / B) * (B / A) := by
      field_simp [hA, hB_pos.ne']
    _ = NumberField.dedekindZeta_residue L * (B / A) := by
          dsimp [A, B, L]
          rw [NumberField.dedekindZeta_residue_def, KummerCriterion.hPlus, NumberField.classNumber]
    _ = NumberField.dedekindZeta_residue L *
          (((Units.torsionOrder L : ℝ) * Real.sqrt |discr L|) /
            (2 ^ InfinitePlace.nrRealPlaces L *
              (2 * Real.pi) ^ InfinitePlace.nrComplexPlaces L * Units.regulator L)) := by
          simp [A, B]

omit [IsCMField K] in
/--
@isnad1 id=eq.0h1v.s5.f5d623d78687 from=translated src=- shape=e63adbaf vocab=b1f3c51e
-/
lemma nrComplexPlaces_maximalRealSubfield_eq_zero :
    NumberField.InfinitePlace.nrComplexPlaces (NumberField.maximalRealSubfield K) = 0 :=
  NumberField.IsTotallyReal.nrComplexPlaces_eq_zero
      (K := NumberField.maximalRealSubfield K)

/--
@isnad1 id=eq.0h2v.s6.2e62515dbab7 from=translated src=- shape=c0044089 vocab=b3a6caa5
-/
lemma nrRealPlaces_maximalRealSubfield_eq_prime_sub_one_div_two :
    NumberField.InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) = (p - 1) / 2 := by
  let L := NumberField.maximalRealSubfield K
  calc
    NumberField.InfinitePlace.nrRealPlaces L = Module.finrank ℚ L := by
      rw [← NumberField.IsTotallyReal.finrank (K := L)]
    _ = (p - 1) / 2 := by
      rw [finrank_Kplus_over_rat (p := p) (K := K)]

/--
@isnad1 id=eq.0h2v.s7.fdaafe793da5 from=translated src=- shape=0eeb03f0 vocab=583ae332
-/
lemma maximalRealSubfield_archimedeanFactor_eq_pow :
    2 ^ NumberField.InfinitePlace.nrRealPlaces (NumberField.maximalRealSubfield K) *
        (2 * Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces
          (NumberField.maximalRealSubfield K) =
      2 ^ ((p - 1) / 2 : ℕ) := by
  rw [nrComplexPlaces_maximalRealSubfield_eq_zero (K := K), pow_zero, mul_one,
    nrRealPlaces_maximalRealSubfield_eq_prime_sub_one_div_two (p := p) (K := K)]

set_option linter.unusedSectionVars false in
/--
@isnad1 id=or.0h2v.s12.58f934c021fd from=translated src=- shape=f6bfc27d vocab=c1b9746d
-/
lemma maximalRealSubfield_torsion_eq_one_or_neg_one
    (x : NumberField.Units.torsion (NumberField.maximalRealSubfield K)) :
    (x : (𝓞 (NumberField.maximalRealSubfield K))ˣ) = 1 ∨
      (x : (𝓞 (NumberField.maximalRealSubfield K))ˣ) = -1 := by
  let L := NumberField.maximalRealSubfield K
  by_cases! hc : 2 < orderOf (x : (𝓞 L)ˣ)
  · rw [← orderOf_units,
      ← orderOf_injective _ (FaithfulSMul.algebraMap_injective (𝓞 L) L)] at hc
    linarith [InfinitePlace.IsPrimitiveRoot.nrRealPlaces_eq_zero_of_two_lt hc
        (IsPrimitiveRoot.orderOf _),
      IsTotallyReal.finrank (K := L), Module.finrank_pos (R := ℚ) (M := L)]
  · interval_cases hi : orderOf (x : (𝓞 L)ˣ)
    · linarith [orderOf_pos_iff.2 ((CommGroup.mem_torsion x.1).1 x.2)]
    · exact .inl (orderOf_eq_one_iff.1 hi)
    · rw [← orderOf_units, CharP.orderOf_eq_two_iff 0 (by decide)] at hi
      simp [← Units.val_inj, hi]

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h1v.s5.067b3a979ea3 from=translated src=- shape=750154d8 vocab=468a700e
-/
lemma maximalRealSubfield_torsionOrder_eq_two :
    Units.torsionOrder (NumberField.maximalRealSubfield K) = 2 := by
  let L := NumberField.maximalRealSubfield K
  classical
  let := Fintype.ofFinite (Units.torsion L)
  rw [Units.torsionOrder, Nat.card_eq_fintype_card]
  refine Finset.card_eq_two.2
    ⟨1, ⟨-1, neg_one_mem_torsion⟩, by simp [← Subtype.coe_ne_coe],
      Finset.ext fun x ↦ ⟨fun _ ↦ ?_, fun _ ↦ Finset.mem_univ _⟩⟩
  rw [Finset.mem_insert, Finset.mem_singleton, ← Subtype.val_inj, ← Subtype.val_inj]
  exact maximalRealSubfield_torsion_eq_one_or_neg_one (K := K) x

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.1h2v.s6.ab81bf26e096 from=translated src=- shape=5d155228 vocab=69de4b53
-/
lemma cyclotomic_torsionOrder_eq_two_mul_prime (hp_odd' : p ≠ 2) :
    Units.torsionOrder K = 2 * p := by
  have hneven : ¬ Even p := fun h =>
    hp_odd' ((hp.out.even_iff).mp h)
  simpa [hneven, two_mul] using
    (IsCyclotomicExtension.Rat.torsionOrder_eq (n := p) (K := K))

/--
@isnad1 id=eq.0h2v.s6.ad4b62eb72b3 from=translated src=- shape=e7b2038a vocab=5e51584f
-/
lemma units_rank_eq_prime_sub_three_div_two :
    Units.rank K = (p - 3) / 2 := by
  let L := NumberField.maximalRealSubfield K
  rw [← NumberField.IsCMField.units_rank_eq_units_rank (K := K), Units.rank]
  calc
    Fintype.card (NumberField.InfinitePlace L) - 1
        = NumberField.InfinitePlace.nrRealPlaces L - 1 := by
            rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
              NumberField.IsTotallyReal.nrComplexPlaces_eq_zero, add_zero]
    _ = Module.finrank ℚ L - 1 := by
          rw [← NumberField.IsTotallyReal.finrank (K := L)]
    _ = (p - 1) / 2 - 1 := by
          rw [finrank_Kplus_over_rat (p := p) (K := K)]
    _ = (p - 3) / 2 := by omega

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h2v.s6.e676701d9222 from=translated src=- shape=4a93b931 vocab=16fa52bb
-/
lemma abs_discr_cyclotomic_eq_pow :
    |((NumberField.discr K : ℤ) : ℝ)| = (p : ℝ) ^ (p - 2) := by
  rw [IsCyclotomicExtension.Rat.discr_prime (p := p) (K := K)]
  rw [Int.cast_mul, Int.cast_pow, Int.cast_neg, Int.cast_one, abs_mul, abs_pow, abs_neg,
    abs_one, one_pow]
  simp [abs_of_nonneg (show 0 ≤ ((p : ℝ) ^ (p - 2)) by positivity)]

set_option linter.unusedSectionVars false in
/--
@isnad1 id=not.1h2v.s6.8d4d3ca44f34 from=translated src=- shape=2ac75c02 vocab=d2fdbf1a
-/
lemma zeta_not_mem_maximalRealSubfield (hp_odd' : p ≠ 2) :
    IsCyclotomicExtension.zeta p ℚ K ∉ NumberField.maximalRealSubfield K := by
  classical
  let ζ : K := IsCyclotomicExtension.zeta p ℚ K
  have hζ : IsPrimitiveRoot ζ p := IsCyclotomicExtension.zeta_spec p ℚ K
  intro hmem
  have hfix := (NumberField.mem_maximalRealSubfield_iff (K := K) ζ).mp hmem
  let φ : K →+* ℂ := Classical.choice inferInstance
  have hstar : star (φ ζ) = φ ζ := hfix φ
  have hpow : (φ ζ) ^ p = 1 := by
    simpa [map_pow] using congrArg φ hζ.pow_eq_one
  have hnorm : ‖φ ζ‖ = 1 :=
    Complex.norm_eq_one_of_pow_eq_one hpow hp.out.ne_zero
  have him : (φ ζ).im = 0 := by
    simpa [RCLike.star_def] using (Complex.conj_eq_iff_im.mp hstar)
  let r : ℝ := (φ ζ).re
  have hreal : φ ζ = (r : ℂ) := by
    apply Complex.ext <;> simp [r, him]
  rw [hreal] at hnorm
  have hr_abs : |r| = 1 := by
    simpa [Complex.norm_real] using hnorm
  have hr_sq : r ^ 2 = 1 := by
    have hsquare := congrArg (fun t : ℝ => t ^ 2) hr_abs
    simpa [sq_abs] using hsquare
  rcases sq_eq_one_iff.mp hr_sq with hr | hr
  · have hφζ : φ ζ = 1 := by
      calc
        φ ζ = (r : ℂ) := hreal
        _ = (1 : ℂ) := by simp [hr]
    have hζeq : ζ = 1 := φ.injective <| by simpa using hφζ
    exact (hζ.ne_one hp.out.one_lt) hζeq
  · have hφζ : φ ζ = -1 := by
      calc
        φ ζ = (r : ℂ) := hreal
        _ = (-1 : ℂ) := by simp [hr]
    have hpo : Odd p := hp.out.odd_of_ne_two hp_odd'
    have : ((-1 : ℂ) ^ p) = 1 := by simpa [hφζ] using hpow
    have hneg : (-1 : ℂ) = 1 := by simpa [Odd.neg_one_pow hpo] using this
    have hneq : (-1 : ℂ) ≠ 1 := by norm_num
    exact hneq hneg

set_option linter.unusedSectionVars false in
/--
@isnad1 id=not.1h2v.s8.0d28edd3d37f from=translated src=- shape=da90964d vocab=9093eaa5
-/
lemma zetaInteger_not_mem_field_range (hp_odd' : p ≠ 2) :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ∉
      Set.range (algebraMap (NumberField.maximalRealSubfield K) K) := by
  rintro ⟨x, hx⟩
  have hxmem : (algebraMap (NumberField.maximalRealSubfield K) K x) ∈
      NumberField.maximalRealSubfield K := x.2
  have hzmem : (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ∈
      NumberField.maximalRealSubfield K := by
    simpa [hx] using hxmem
  exact zeta_not_mem_maximalRealSubfield (p := p) (K := K) hp_odd' hzmem

set_option linter.unusedSectionVars false in
/--
@isnad1 id=not.1h2v.s9.64a79b34ef78 from=translated src=- shape=0977075e vocab=29f77532
-/
lemma zetaInteger_not_mem_ring_range (hp_odd' : p ≠ 2) :
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ∉
      Set.range (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) := by
  rintro ⟨x, hx⟩
  apply zetaInteger_not_mem_field_range (p := p) (K := K) hp_odd'
  refine ⟨(x : NumberField.maximalRealSubfield K), ?_⟩
  exact congrArg (fun y : 𝓞 K => (y : K)) hx

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.1h2v.s10.c5eac72c4a78 from=translated src=- shape=365ba9fb vocab=62918be9
-/
lemma zetaInteger_adjoin_eq_top_maximalRealSubfield (hp_odd' : p ≠ 2) :
    Algebra.adjoin (NumberField.maximalRealSubfield K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K)} : Set K) = ⊤ := by
  let L : IntermediateField (NumberField.maximalRealSubfield K) K :=
    IntermediateField.adjoin (NumberField.maximalRealSubfield K)
      ({(((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K)} : Set K)
  have hL : L = ⊤ := by
    have hprime : Nat.Prime (Module.finrank (NumberField.maximalRealSubfield K) K) := by
      simpa [finrank_K_over_Kplus (K := K)] using Nat.prime_two
    have hsimple :=
      ((IntermediateField.isSimpleOrder_of_finrank_prime (NumberField.maximalRealSubfield K) K
          hprime).eq_bot_or_eq_top L)
    refine hsimple.resolve_left ?_
    intro hbot
    have hzeta_mem : (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K) ∈ L :=
      IntermediateField.subset_adjoin _ _ (by simp)
    rw [hbot, IntermediateField.mem_bot] at hzeta_mem
    exact zetaInteger_not_mem_field_range (p := p) (K := K) hp_odd' hzeta_mem
  have hzeta_alg : IsAlgebraic (NumberField.maximalRealSubfield K)
      ((((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) : K)) :=
    Algebra.IsAlgebraic.isAlgebraic _
  exact Algebra.adjoin_eq_top_of_primitive_element hzeta_alg hL

set_option linter.unusedSectionVars false in
/--
@isnad1 id=isunit.1h2v.s7.8da00b734aaf from=translated src=- shape=3baacc75 vocab=37129737
-/
lemma one_add_zetaInteger_isUnit (hp_odd' : p ≠ 2) :
    IsUnit (1 + ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K)) := by
  have h :=
    (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger_isPrimitiveRoot.geom_sum_isUnit
      hp.out.two_le (Nat.coprime_two_left.mpr (hp.out.odd_of_ne_two hp_odd'))
  simpa [Finset.sum_range_succ] using h

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h2v.s7.382255e068bd from=translated src=- shape=1fa4648e vocab=7acf3603
-/
lemma zetaInteger_pow_pred_mul_eq_one :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) = 1 :=
  zeta_toInteger_pow_pred_mul p K

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h2v.s7.75fdabdbee45 from=translated src=- shape=7a88d77f vocab=7acf3603
-/
lemma zetaInteger_mul_pow_pred_eq_one :
    (((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) *
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) : 𝓞 K) = 1 := by
  simpa [mul_comm] using zetaInteger_pow_pred_mul_eq_one (p := p) (K := K)

set_option linter.unusedSectionVars false in
/--
@isnad1 id=isunit.1h2v.s7.6c0c329aa563 from=translated src=- shape=0a31f5ed vocab=715ca335
-/
lemma one_add_zetaInteger_pow_pred_isUnit (hp_odd' : p ≠ 2) :
    IsUnit (1 + ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) ^ (p - 1)) := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hzeta_unit : IsUnit (ζi ^ (p - 1) : 𝓞 K) := by
    simpa using! (IsCyclotomicExtension.zeta_spec p ℚ K).unit'.isUnit.pow (p - 1)
  have hmul : (ζi ^ (p - 1) : 𝓞 K) * (1 + ζi) = 1 + ζi ^ (p - 1) := by
    rw [mul_add, mul_one, zetaInteger_pow_pred_mul_eq_one (p := p) (K := K)]
    ring
  rw [← hmul]
  exact hzeta_unit.mul (one_add_zetaInteger_isUnit (p := p) (K := K) hp_odd')

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h2v.s9.c75baeb21e55 from=translated src=- shape=a95c950f vocab=cff0f73c
-/
lemma algebraMap_piPlus_eq_two_sub_zeta_sub_zetaPowPred :
    (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) (piPlus p K) =
      (2 : 𝓞 K) - (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [algebraMap_piPlus]
  have hconj : NumberField.IsCMField.ringOfIntegersComplexConj K (ζi - 1) =
      ζi ^ (p - 1) - 1 := by
    rw [map_sub, map_one, complexConj_apply_zeta]
  calc
    (ζi - 1) * NumberField.IsCMField.ringOfIntegersComplexConj K (ζi - 1)
        = (ζi - 1) * (ζi ^ (p - 1) - 1) := by rw [hconj]
    _ = ζi * ζi ^ (p - 1) - ζi - ζi ^ (p - 1) + 1 := by
          ring
    _ = (2 : 𝓞 K) - ζi - ζi ^ (p - 1) := by
          rw [zetaInteger_mul_pow_pred_eq_one (p := p) (K := K)]
          ring_nf

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.0h2v.s12.2364eaaa6952 from=translated src=- shape=d8ab57e2 vocab=63583094
-/
lemma aeval_zetaInteger_quadratic_eq_zero :
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
        Polynomial (𝓞 (NumberField.maximalRealSubfield K))) = 0 := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hcalc :
      ζi ^ 2 + (((2 : 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) * ζi + 1 = 0 := by
    calc
      ζi ^ 2 + (((2 : 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) * ζi + 1
          = -(ζi ^ (p - 1) * ζi) + 1 := by ring
      _ = 0 := by
            rw [zetaInteger_pow_pred_mul_eq_one (p := p) (K := K)]
            norm_num
  simpa [Polynomial.aeval_def, algebraMap_piPlus_eq_two_sub_zeta_sub_zetaPowPred,
    pow_two, map_sub, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm]
    using! hcalc

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.1h2v.s12.052730d1ae82 from=translated src=- shape=4a340ce1 vocab=19f42093
-/
lemma minpoly_maximalRealSubfield_zetaInteger_eq_quadratic (hp_odd' : p ≠ 2) :
    minpoly (𝓞 (NumberField.maximalRealSubfield K))
        ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) =
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
        Polynomial (𝓞 (NumberField.maximalRealSubfield K))) := by
  let A := 𝓞 (NumberField.maximalRealSubfield K)
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have hint : IsIntegral A ζi := IsIntegralClosure.isIntegral A K ζi
  have hdeg :
      (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
          Polynomial A).degree ≤
        (minpoly A ζi).degree := by
    have hnatdeg : 2 ≤ (minpoly A ζi).natDegree :=
      (minpoly.two_le_natDegree_iff hint).2
        (zetaInteger_not_mem_ring_range (p := p) (K := K) hp_odd')
    have hpoly_deg :
        (Polynomial.X ^ 2 + Polynomial.C (piPlus p K - 2) * Polynomial.X + 1 :
          Polynomial A).degree = 2 := by
      simpa [one_mul, Polynomial.C_1] using
        (Polynomial.degree_quadratic
          (R := A)
          (a := (1 : A))
          (b := piPlus p K - 2)
          (c := (1 : A))
          one_ne_zero)
    rw [hpoly_deg, Polynomial.degree_eq_natDegree (minpoly.ne_zero hint)]
    exact_mod_cast hnatdeg
  symm
  refine IsIntegrallyClosed.minpoly.unique (R := A) (S := 𝓞 K) (s := ζi) ?_ ?_ ?_
  · simpa [Polynomial.C_1] using
      (Polynomial.isMonicOfDegree_add_add_two (a := piPlus p K - 2) (b := (1 : A))).monic
  · exact aeval_zetaInteger_quadratic_eq_zero (p := p) (K := K)
  · intro Q hQ hQroot
    exact hdeg.trans (minpoly.min (A := A) (x := ζi) hQ hQroot)

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.1h2v.s12.9ae70ace3ea5 from=translated src=- shape=f639e469 vocab=c740534e
-/
lemma aeval_derivative_minpoly_zetaInteger_eq_zeta_sub_complexConj_zeta (hp_odd' : p ≠ 2) :
    Polynomial.aeval (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
      (Polynomial.derivative
        (minpoly (𝓞 (NumberField.maximalRealSubfield K))
          ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K))) =
      ((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) -
        (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1) := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  have htwo :
      (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) 2 = (2 : 𝓞 K) := by
    simpa using map_natCast (algebraMap (𝓞 (NumberField.maximalRealSubfield K)) (𝓞 K)) 2
  rw [minpoly_maximalRealSubfield_zetaInteger_eq_quadratic (p := p) (K := K) hp_odd']
  simpa [Polynomial.aeval_def, algebraMap_piPlus_eq_two_sub_zeta_sub_zetaPowPred,
    map_sub, htwo, add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm,
    mul_comm] using
    (show ((1 + 1 : 𝓞 K) * ζi) + (((2 : 𝓞 K) - ζi - ζi ^ (p - 1)) - 2) =
        ζi - ζi ^ (p - 1) by ring)

set_option linter.unusedSectionVars false in
/--
@isnad1 id=eq.1h2v.s7.69ae343e1e6e from=translated src=- shape=a1c1f412 vocab=a358cb67
-/
lemma span_zetaInteger_sub_zetaPowPred_eq_zetaPrime (hp_odd' : p ≠ 2) :
    Ideal.span
        ({((IsCyclotomicExtension.zeta_spec p ℚ K).toInteger : 𝓞 K) -
            (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger ^ (p - 1)} :
          Set (𝓞 K)) =
      zetaPrime p K := by
  let ζi : 𝓞 K := (IsCyclotomicExtension.zeta_spec p ℚ K).toInteger
  rw [zetaPrime]
  have hcalc :
      (ζi - 1) * (1 + ζi ^ (p - 1)) = ζi - ζi ^ (p - 1) := by
    have hmul : ζi * ζi ^ (p - 1) = 1 := zetaInteger_mul_pow_pred_eq_one (p := p) (K := K)
    calc
      (ζi - 1) * (1 + ζi ^ (p - 1)) = ζi - 1 + (ζi * ζi ^ (p - 1) - ζi ^ (p - 1)) := by
        ring
      _ = ζi - ζi ^ (p - 1) := by
        rw [hmul]
        ring
  rw [← hcalc, Ideal.span_singleton_mul_right_unit]
  exact one_add_zetaInteger_pow_pred_isUnit (p := p) (K := K) hp_odd'

/-- The class number formula for the prime cyclotomic field, with the standard
cyclotomic invariants made explicit.
@isnad1 id=eq.1h2v.s7.3b722a0de561 from=translated src=- shape=d7ab59a4 vocab=e87607cb
-/
theorem h_formula_cyclotomic (hp_odd' : p ≠ 2) :
    (h K : ℝ) =
      NumberField.dedekindZeta_residue K *
        ((((2 * p : ℕ) : ℝ) * Real.sqrt ((p : ℝ) ^ (p - 2))) /
          ((2 * Real.pi) ^ ((p - 1) / 2) * Units.regulator K)) := by
  have hp_gt2 : 2 < p := lt_of_le_of_ne hp.out.two_le (by simpa using hp_odd'.symm)
  have hreal : NumberField.InfinitePlace.nrRealPlaces K = 0 :=
    IsCyclotomicExtension.Rat.nrRealPlaces_eq_zero (n := p) (K := K) hp_gt2
  have hcomplex : NumberField.InfinitePlace.nrComplexPlaces K = (p - 1) / 2 := by
    simpa [Nat.totient_prime hp.out] using
      (IsCyclotomicExtension.Rat.nrComplexPlaces_eq_totient_div_two (n := p) (K := K))
  rw [h_formula (K := K), hreal, hcomplex,
    cyclotomic_torsionOrder_eq_two_mul_prime (p := p) (K := K) hp_odd',
    abs_discr_cyclotomic_eq_pow (p := p) (K := K)]
  simp [mul_assoc, mul_comm]
end KummerCriterion
