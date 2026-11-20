/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.PerpDiscriminant
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.EvenCoordinates
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.CyclicGlue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

open SRG266.Lattice

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def lorentzD7Form (x : V) (c : IntegralGramLattice G x) :
    LinearMap.BilinForm ℚ (lorentzPerpSpace G x c × (Fin 7 → ℚ)) :=
  prodForm (lorentzPerpForm G x c) (standardRatForm 7)

noncomputable def lorentzD7Glue (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (P : Submodule ℤ (ratGramSpace G x)) (B : SecondSubconstituent G x) :
    Submodule ℤ (lorentzPerpSpace G x c × (Fin 7 → ℚ)) :=
  cyclicGlueLattice (lorentzPerpLattice G x c P) (evenCoordinateLattice 7)
    (lorentzPerpGenerator G hG x c hc B) (coordinateSpinor 7)

noncomputable def lorentzD7FrameVector (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) :
    lorentzPerpSpace G x c × (Fin 7 → ℚ) :=
  (lorentzPerpGenerator G hG x c hc B, coordinateSpinor 7)

/--
@isnad1 id=eq.2h5v.s13.b0d569b2c847 from=translated src=- shape=2888275a vocab=6df790c8
-/
theorem lorentzD7FrameVector_norm (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) (B : SecondSubconstituent G x) :
    lorentzD7Form G x c (lorentzD7FrameVector G hG x c hc B)
      (lorentzD7FrameVector G hG x c hc B) = 4 := by
  change lorentzPerpForm G x c (lorentzPerpGenerator G hG x c hc B)
    (lorentzPerpGenerator G hG x c hc B) +
    standardRatForm 7 (coordinateSpinor 7) (coordinateSpinor 7) = 4
  rw [lorentzPerpGenerator_norm, coordinateSpinor_norm]
  norm_num

/--
@isnad1 id=isintegr.4h6v.s11.2c5b734e349b from=translated src=- shape=01071384 vocab=826abcf1
-/
theorem lorentzD7Glue_isIntegral (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : IsIntegral (lorentzGramForm G x c) P) (B : SecondSubconstituent G x) :
    IsIntegral (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) := by
  apply cyclicGlueLattice_isIntegral (lorentzPerpForm_isSymm G x c)
    (standardRatForm_isSymm 7) (lorentzPerpLattice_isIntegral G x c hint)
    (evenCoordinateLattice_isIntegral 7)
    (lorentzPerpGenerator_mem_dual G hG x c hc hle hint B)
    (coordinateSpinor_mem_dual 7)
  apply mem_one_iff.mpr
  exact ⟨4, (lorentzD7FrameVector_norm G hG x c hc B).symm⟩

/--
@isnad1 id=iseven.5h6v.s11.e973474a404e from=translated src=- shape=38f25dfe vocab=0bb43c9e
-/
theorem lorentzD7Glue_isEven (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : IsIntegral (lorentzGramForm G x c) P)
    (heven : IsEven (lorentzPerpForm G x c) (lorentzPerpLattice G x c P))
    (B : SecondSubconstituent G x) :
    IsEven (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) := by
  apply cyclicGlueLattice_isEven (lorentzPerpForm_isSymm G x c)
    (standardRatForm_isSymm 7) (lorentzD7Glue_isIntegral G hG x c hc hle hint B)
    heven (evenCoordinateLattice_isEven 7)
  exact ⟨2, (lorentzD7FrameVector_norm G hG x c hc B).trans (by norm_num)⟩

/--
@isnad1 id=iff.3h7v.s13.ad27b0cd7e63 from=translated src=- shape=18a0ab6e vocab=5972088c
-/
theorem lorentzD7Glue_mem_left_iff (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (B : SecondSubconstituent G x) (y : lorentzPerpSpace G x c) :
    (y, (0 : Fin 7 → ℚ)) ∈ lorentzD7Glue G hG x c hc P B ↔
      y ∈ lorentzPerpLattice G x c P :=
  cyclicGlueLattice_mem_left_iff
    (four_zsmul_lorentzPerpGenerator_mem G hG x c hc hle B) d7_spinor_order y

/--
@isnad1 id=iff.4h7v.s13.3a9da9082b68 from=translated src=- shape=e99eaca6 vocab=557f4df7
-/
theorem lorentzD7Glue_mem_right_iff (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (heven : IsEven (lorentzPerpForm G x c) (lorentzPerpLattice G x c P))
    (B : SecondSubconstituent G x) (z : Fin 7 → ℚ) :
    ((0 : lorentzPerpSpace G x c), z) ∈ lorentzD7Glue G hG x c hc P B ↔
      z ∈ evenCoordinateLattice 7 := by
  apply cyclicGlueLattice_mem_right_iff (p := 4) ?_ (four_smul_coordinateSpinor_mem 7)
  intro m
  exact zsmul_mem_iff_four_dvd_of_odd_quarter_norm heven (a := 9) (by decide)
    (lorentzPerpGenerator_norm G hG x c hc B)
    (four_zsmul_lorentzPerpGenerator_mem G hG x c hc hle B) m

/--
@isnad1 id=mem.3h7v.s12.1795fdfd75a2 from=translated src=- shape=26bb325e vocab=538bc841
-/
theorem lorentzD7FrameVector_mem (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (B C : SecondSubconstituent G x) :
    lorentzD7FrameVector G hG x c hc C ∈ lorentzD7Glue G hG x c hc P B := by
  have hbase : lorentzD7FrameVector G hG x c hc B ∈ lorentzD7Glue G hG x c hc P B :=
    Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)
  have hdiff : (lorentzPerpGenerator G hG x c hc C -
      lorentzPerpGenerator G hG x c hc B, (0 : Fin 7 → ℚ)) ∈
      lorentzD7Glue G hG x c hc P B :=
    Submodule.mem_sup_left ⟨lorentzPerpGenerator_sub_mem G hG x c hc hle C B,
      (evenCoordinateLattice 7).zero_mem⟩
  have heq : lorentzD7FrameVector G hG x c hc C =
      (lorentzPerpGenerator G hG x c hc C - lorentzPerpGenerator G hG x c hc B,
        (0 : Fin 7 → ℚ)) + lorentzD7FrameVector G hG x c hc B := by
    ext <;> simp [lorentzD7FrameVector]
  rw [heq]
  exact Submodule.add_mem _ hdiff hbase

/--
@isnad1 id=eq.2h4v.s10.1c9a00eaa983 from=translated src=- shape=9b559a00 vocab=174d8e3f
-/
theorem finrank_lorentzD7Space (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    Module.finrank ℚ (lorentzPerpSpace G x c × (Fin 7 → ℚ)) = 18 := by
  rw [Module.finrank_prod, finrank_lorentzPerpSpace G hG x c hc]
  simp

/--
@isnad1 id=ex.1h4v.s16.add101183ac7 from=translated src=- shape=46faa1a9 vocab=5bb0cc79
-/
theorem exists_lorentzD7Glue_from_graph (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∃ (c : IntegralGramLattice G x)
      (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
      (P : Submodule ℤ (ratGramSpace G x)),
      IsLattice ℚ (lorentzD7Glue G hG x c hc P B) ∧
      IsIntegral (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) ∧
      IsEven (lorentzD7Form G x c) (lorentzD7Glue G hG x c hc P B) ∧
      Module.finrank ℚ (lorentzPerpSpace G x c × (Fin 7 → ℚ)) = 18 ∧
      (∀ z, z ≠ 0 → 0 < lorentzD7Form G x c z z) ∧
      (∀ C, lorentzD7FrameVector G hG x c hc C ∈ lorentzD7Glue G hG x c hc P B ∧
        lorentzD7Form G x c (lorentzD7FrameVector G hG x c hc C)
          (lorentzD7FrameVector G hG x c hc C) = 4) ∧
      (∀ y, (y, (0 : Fin 7 → ℚ)) ∈ lorentzD7Glue G hG x c hc P B ↔
        y ∈ lorentzPerpLattice G x c P) ∧
      (∀ z, ((0 : lorentzPerpSpace G x c), z) ∈ lorentzD7Glue G hG x c hc P B ↔
        z ∈ evenCoordinateLattice 7) := by
  obtain ⟨c, hc, P, hle, hmax, hlat, heven, _, hpd, _⟩ :=
    exists_lorentzPerp_discriminant_from_graph G hG x B
  exact ⟨c, hc, P, cyclicGlueLattice_isLattice hlat (evenCoordinateLattice_isLattice 7),
    lorentzD7Glue_isIntegral G hG x c hc hle hmax.integral B,
    lorentzD7Glue_isEven G hG x c hc hle hmax.integral heven B,
    finrank_lorentzD7Space G hG x c hc, prodForm_posDef hpd (standardRatForm_posDef 7),
    fun C => ⟨lorentzD7FrameVector_mem G hG x c hc hle B C,
      lorentzD7FrameVector_norm G hG x c hc C⟩,
    lorentzD7Glue_mem_left_iff G hG x c hc hle B,
    lorentzD7Glue_mem_right_iff G hG x c hc hle heven B⟩

end SRG266
