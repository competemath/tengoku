/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.D7Glue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

open SRG266.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def lorentzD7OddLift (x : V) (c : IntegralGramLattice G x)
    (B : SecondSubconstituent G x) :
    ratGramSpace G x →ₗ[ℚ] (lorentzPerpSpace G x c × (Fin 7 → ℚ)) :=
  (lorentzIntegralProjection G x c B).prod 0

/--
@isnad1 id=mem.5h7v.s14.b256390ad94e from=translated src=- shape=4789d8ab vocab=f533d27c
-/
theorem lorentzD7OddLift_mem_dual (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {v : ratGramSpace G x}
    (hv : v ∈ (lorentzGramForm G x c).dualSubmodule P) :
    lorentzD7OddLift G x c B v ∈
      (lorentzD7Form G x c).dualSubmodule (lorentzD7Glue G hG x c hc P B) := by
  change lorentzD7Glue G hG x c hc P B ≤
    rightIntegral (lorentzD7Form G x c) (lorentzD7OddLift G x c B v)
  refine sup_le (fun z hz => ?_) (Submodule.span_le.mpr ?_)
  · change lorentzPerpForm G x c (lorentzIntegralProjection G x c B v) z.1 +
      standardRatForm 7 0 z.2 ∈ (1 : Submodule ℤ ℚ)
    simpa only [map_zero, LinearMap.zero_apply, add_zero] using
      lorentzIntegralProjection_mem_dual G hG x c hc hle hint B hv z.1 hz.1
  · rintro _ (rfl : _ = (lorentzPerpGenerator G hG x c hc B, coordinateSpinor 7))
    change lorentzPerpForm G x c (lorentzIntegralProjection G x c B v)
      (lorentzPerpGenerator G hG x c hc B) + standardRatForm 7 0 (coordinateSpinor 7) ∈
        (1 : Submodule ℤ ℚ)
    simpa only [map_zero, LinearMap.zero_apply, add_zero] using
      lorentzIntegralProjection_pair_marked_integral G hG x c hc hle B hv

/--
@isnad1 id=eq.4h6v.s14.2d07ee18f992 from=translated src=- shape=c7ee00f6 vocab=68f3fcaf
-/
theorem lorentzD7_dual_eq_sup_map (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : IsIntegral (lorentzGramForm G x c) P) (B : SecondSubconstituent G x) :
    (lorentzD7Form G x c).dualSubmodule (lorentzD7Glue G hG x c hc P B) =
      lorentzD7Glue G hG x c hc P B ⊔
        ((lorentzGramForm G x c).dualSubmodule P).map
          ((lorentzD7OddLift G x c B).restrictScalars ℤ) := by
  apply le_antisymm
  · intro z hz
    have hp : z ∈ (prodForm (lorentzPerpForm G x c) (standardRatForm 7)).dualSubmodule
        ((lorentzPerpLattice G x c P).prod (evenCoordinateLattice 7)) :=
      fun w hw => hz w (Submodule.mem_sup_left hw)
    rw [dualSubmodule_prodForm] at hp
    obtain ⟨hx, hy⟩ := hp
    rw [lorentzPerp_dual_eq_map_sup_marked G hG x c hc hle hint B] at hx
    obtain ⟨jv, hjv, au, hau, hxeq⟩ := Submodule.mem_sup.mp hx
    obtain ⟨v, hv, rfl⟩ := hjv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hau
    change lorentzIntegralProjection G x c B v +
      a • lorentzPerpGenerator G hG x c hc B = z.1 at hxeq
    rw [d7_dual] at hy
    obtain ⟨d, hd, bs, hbs, hyeq⟩ := Submodule.mem_sup.mp hy
    obtain ⟨b, rfl⟩ := Submodule.mem_span_singleton.mp hbs
    have hj := lorentzIntegralProjection_pair_marked_integral G hG x c hc hle B hv
    have hs : standardRatForm 7 d (coordinateSpinor 7) ∈ (1 : Submodule ℤ ℚ) := by
      rw [(standardRatForm_isSymm 7).eq]
      exact coordinateSpinor_mem_dual 7 d hd
    have hg := hz (lorentzD7FrameVector G hG x c hc B)
      (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _))
    have he : lorentzD7Form G x c z (lorentzD7FrameVector G hG x c hc B) =
        lorentzPerpForm G x c (lorentzIntegralProjection G x c B v)
          (lorentzPerpGenerator G hG x c hc B) +
        standardRatForm 7 d (coordinateSpinor 7) +
        (a : ℚ) * (9 / 4) + (b : ℚ) * (7 / 4) := by
      change lorentzPerpForm G x c z.1 (lorentzPerpGenerator G hG x c hc B) +
        standardRatForm 7 z.2 (coordinateSpinor 7) = _
      rw [← hxeq, ← hyeq]
      have ha : a • lorentzPerpGenerator G hG x c hc B =
          (a : ℚ) • lorentzPerpGenerator G hG x c hc B := by module
      have hb : b • coordinateSpinor 7 = (b : ℚ) • coordinateSpinor 7 := by module
      rw [ha, hb]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
        smul_eq_mul, lorentzPerpGenerator_norm, coordinateSpinor_norm]
      norm_num
      ring
    obtain ⟨r, hr⟩ := mem_one_iff.mp hj
    obtain ⟨s, hs'⟩ := mem_one_iff.mp hs
    obtain ⟨t, ht⟩ := mem_one_iff.mp hg
    have hlinQ : (9 : ℚ) * a + 7 * b = 4 * ((t : ℚ) - r - s) := by
      rw [he, ← hr, ← hs'] at ht
      linarith
    have hlin : 9 * a + 7 * b = 4 * (t - r - s) := by exact_mod_cast hlinQ
    have hdvd : (4 : ℤ) ∣ a - b := ⟨t - r - s - 2 * a - 2 * b, by linarith⟩
    obtain ⟨k, hk⟩ := hdvd
    have hres : d - k • ((4 : ℤ) • coordinateSpinor 7) ∈ evenCoordinateLattice 7 :=
      Submodule.sub_mem _ hd (Submodule.smul_mem _ k (four_smul_coordinateSpinor_mem 7))
    have hdecomp : z = lorentzD7OddLift G x c B v +
        ((0 : lorentzPerpSpace G x c), d - k • ((4 : ℤ) • coordinateSpinor 7)) +
        a • lorentzD7FrameVector G hG x c hc B := by
      apply Prod.ext
      · change z.1 = lorentzIntegralProjection G x c B v + 0 +
          a • lorentzPerpGenerator G hG x c hc B
        simpa only [add_zero] using hxeq.symm
      · change z.2 = 0 + (d - k • ((4 : ℤ) • coordinateSpinor 7)) +
          a • coordinateSpinor 7
        rw [← hyeq]
        have hb : b = a - 4 * k := by omega
        rw [hb]
        module
    rw [hdecomp]
    apply Submodule.add_mem
    · apply Submodule.add_mem
      · exact Submodule.mem_sup_right ⟨v, hv, rfl⟩
      · exact Submodule.mem_sup_left (Submodule.mem_sup_left
          ⟨(lorentzPerpLattice G x c P).zero_mem, hres⟩)
    · exact Submodule.mem_sup_left (Submodule.smul_mem _ a
        (Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)))
  · refine sup_le (lorentzD7Glue_isIntegral G hG x c hc hle hint B) ?_
    rintro _ ⟨v, hv, rfl⟩
    exact lorentzD7OddLift_mem_dual G hG x c hc hle hint B hv

/--
@isnad1 id=iff.5h7v.s13.4f1d343ed43a from=translated src=- shape=56da83b4 vocab=39be0aba
-/
theorem lorentzD7OddLift_mem_iff (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {v : ratGramSpace G x}
    (hv : v ∈ (lorentzGramForm G x c).dualSubmodule P) :
    lorentzD7OddLift G x c B v ∈ lorentzD7Glue G hG x c hc P B ↔ v ∈ P := by
  exact (lorentzD7Glue_mem_left_iff G hG x c hc hle B _).trans
    (lorentzIntegralProjection_mem_iff G hG x c hc hle hint B hv)

/--
@isnad1 id=iff.5h8v.s14.3e8d8d389196 from=translated src=- shape=4ac71f42 vocab=39be0aba
-/
theorem lorentzD7OddLift_zsmul_mem_iff (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {v : ratGramSpace G x}
    (hv : v ∈ (lorentzGramForm G x c).dualSubmodule P) (m : ℤ) :
    m • lorentzD7OddLift G x c B v ∈ lorentzD7Glue G hG x c hc P B ↔ m • v ∈ P := by
  rw [← map_zsmul]
  exact lorentzD7OddLift_mem_iff G hG x c hc hle hint B (Submodule.smul_mem _ m hv)

/--
@isnad1 id=ex.4h7v.s14.f73a247af505 from=translated src=- shape=c17b586a vocab=51275e22
-/
theorem lorentzD7OddLift_norm_mod_even (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (B : SecondSubconstituent G x) {v : ratGramSpace G x}
    (hv : v ∈ (lorentzGramForm G x c).dualSubmodule P) :
    ∃ n : ℤ, lorentzD7Form G x c (lorentzD7OddLift G x c B v)
      (lorentzD7OddLift G x c B v) = lorentzGramForm G x c v v + 2 * (n : ℚ) := by
  change ∃ n : ℤ, lorentzPerpForm G x c (lorentzIntegralProjection G x c B v)
      (lorentzIntegralProjection G x c B v) + standardRatForm 7 0 0 =
      lorentzGramForm G x c v v + 2 * (n : ℚ)
  simpa only [map_zero, LinearMap.zero_apply, add_zero] using
    lorentzIntegralProjection_norm_mod_even G hG x c hc hle B hv

/--
@isnad1 id=mem.6h7v.s14.f3c265a72dd9 from=translated src=- shape=7662656e vocab=d7cc616d
-/
theorem lorentzD7_dual_denominator (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : IsIntegral (lorentzGramForm G x c) P)
    (hden : ∀ v ∈ (lorentzGramForm G x c).dualSubmodule P, (15 : ℤ) • v ∈ P)
    (B : SecondSubconstituent G x) {z}
    (hz : z ∈ (lorentzD7Form G x c).dualSubmodule (lorentzD7Glue G hG x c hc P B)) :
    (15 : ℤ) • z ∈ lorentzD7Glue G hG x c hc P B := by
  rw [lorentzD7_dual_eq_sup_map G hG x c hc hle hint B] at hz
  obtain ⟨a, ha, jv, hjv, rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨v, hv, rfl⟩ := hjv
  rw [smul_add]
  apply Submodule.add_mem _ (Submodule.smul_mem _ _ ha)
  exact (lorentzD7OddLift_zsmul_mem_iff G hG x c hc hle hint B hv 15).mpr (hden v hv)

/--
@isnad1 id=ex.1h4v.s15.c4aca67e9d23 from=translated src=- shape=78f9b44e vocab=a7aaf078
-/
theorem exists_lorentzD7_discriminant_from_graph (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∃ (c : IntegralGramLattice G x)
      (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
      (P : Submodule ℤ (ratGramSpace G x)),
      lorentzMarkedLattice G x c ≤ P ∧ IsMaximalIntegral (lorentzGramForm G x c) P ∧
      IsLattice ℚ (lorentzD7Glue G hG x c hc P B) ∧
      IsEven (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) ∧
      (lorentzD7Form G x c).dualSubmodule (lorentzD7Glue G hG x c hc P B) =
        lorentzD7Glue G hG x c hc P B ⊔
          ((lorentzGramForm G x c).dualSubmodule P).map
            ((lorentzD7OddLift G x c B).restrictScalars ℤ) ∧
      ∀ z ∈ (lorentzD7Form G x c).dualSubmodule (lorentzD7Glue G hG x c hc P B),
        (15 : ℤ) • z ∈ lorentzD7Glue G hG x c hc P B := by
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨P, hle, hlat, hmax, heven, hden⟩ :=
    exists_lorentzMarked_maximal_even_extension G hG x c hc
  refine ⟨c, hc, P, hle, hmax,
    cyclicGlueLattice_isLattice (lorentzPerpLattice_isLattice G hG x c hc hle hlat hmax.integral)
      (evenCoordinateLattice_isLattice 7),
    lorentzD7Glue_isEven G hG x c hc hle hmax.integral
      (lorentzPerpLattice_isEven G x c heven) B,
    lorentzD7_dual_eq_sup_map G hG x c hc hle hmax.integral B, ?_⟩
  exact fun _ hz => lorentzD7_dual_denominator G hG x c hc hle hmax.integral hden B hz

end SRG266
