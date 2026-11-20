/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.MarkedExtension
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.ProjectedFrame
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.IntegralKernel
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.QuarterCoset
import Tengoku.Seed.LinearAlgebra.Dual.Lemmas

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable abbrev lorentzPerpSpace (x : V) (c : IntegralGramLattice G x) :=
  (centroidHeight G x c).ker

noncomputable def lorentzPerpForm (x : V) (c : IntegralGramLattice G x) :
    LinearMap.BilinForm ℚ (lorentzPerpSpace G x c) :=
  (lorentzGramForm G x c).restrict (centroidHeight G x c).ker

noncomputable def lorentzPerpLattice (x : V) (c : IntegralGramLattice G x)
    (P : Submodule ℤ (ratGramSpace G x)) : Submodule ℤ (lorentzPerpSpace G x c) :=
  P.comap ((centroidHeight G x c).ker.subtype.restrictScalars ℤ)

@[simp]
theorem mem_lorentzPerpLattice (x : V) (c : IntegralGramLattice G x)
    (P : Submodule ℤ (ratGramSpace G x)) (y : lorentzPerpSpace G x c) :
    y ∈ lorentzPerpLattice G x c P ↔ (y : ratGramSpace G x) ∈ P := Iff.rfl

theorem centroidHeight_ne_zero (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) : centroidHeight G x c ≠ 0 := by
  intro h
  have he := centroidHeight_weylVector G hG x c hc
  rw [h, LinearMap.zero_apply] at he
  norm_num at he

theorem finrank_lorentzPerpSpace (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    Module.finrank ℚ (lorentzPerpSpace G x c) = 11 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (centroidHeight_ne_zero G hG x c hc)
  rw [finrank_ratGramSpace G hG x] at h
  change Module.finrank ℚ (centroidHeight G x c).ker = 11
  omega

theorem lorentzPerpForm_isSymm (x : V) (c : IntegralGramLattice G x) :
    (lorentzPerpForm G x c).IsSymm := (lorentzGramForm_isSymm G x c).restrict _

theorem lorentzPerpForm_posDef (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (y : lorentzPerpSpace G x c) (hy : y ≠ 0) :
    0 < lorentzPerpForm G x c y y := by
  change 0 < lorentzGramForm G x c (y : ratGramSpace G x) y
  rw [lorentzGramForm_eq_ratGramForm_of_height_zero G x c y y.2]
  exact ratGramForm_posDef G hG x y (fun h => hy (Subtype.ext h))

theorem centroidHeight_integral_of_marked_le (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    {z : ratGramSpace G x} (hz : z ∈ P) :
    centroidHeight G x c z ∈ (1 : Submodule ℤ ℚ) := by
  have h := hint (hle (lorentzWeylVector_mem_markedLattice G x c)) z hz
  rw [lorentzWeylVector_pair G hG x c hc] at h
  simpa only [neg_neg] using (1 : Submodule ℤ ℚ).neg_mem h

theorem lorentzPerpLattice_isLattice (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hlat : Lattice.IsLattice ℚ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P) :
    Lattice.IsLattice ℚ (lorentzPerpLattice G x c P) := by
  apply Lattice.isLattice_comap_kernel (centroidHeight G x c) hlat
    (fun _ hz => centroidHeight_integral_of_marked_le G hG x c hc hle hint hz)
    (hle (lorentzWeylVector_mem_markedLattice G x c))
  rw [centroidHeight_weylVector G hG x c hc]
  norm_num

theorem lorentzPerpLattice_isIntegral (x : V) (c : IntegralGramLattice G x)
    {P : Submodule ℤ (ratGramSpace G x)}
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P) :
    Lattice.IsIntegral (lorentzPerpForm G x c) (lorentzPerpLattice G x c P) := by
  intro y hy z hz
  exact hint hy z hz

theorem lorentzPerpLattice_isEven (x : V) (c : IntegralGramLattice G x)
    {P : Submodule ℤ (ratGramSpace G x)}
    (heven : Lattice.IsEven (lorentzGramForm G x c) P) :
    Lattice.IsEven (lorentzPerpForm G x c) (lorentzPerpLattice G x c P) := by
  intro y hy
  exact heven y hy

noncomputable def lorentzPerpGenerator (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) : lorentzPerpSpace G x c :=
  ⟨lorentzProjectedGenerator G x c B, centroidHeight_heightZeroPart G hG x c hc _⟩

@[simp]
theorem lorentzPerpGenerator_norm (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) (B : SecondSubconstituent G x) :
    lorentzPerpForm G x c (lorentzPerpGenerator G hG x c hc B)
      (lorentzPerpGenerator G hG x c hc B) = 9 / 4 :=
  lorentzHeightZeroPart_generator_norm G hG x c hc B

theorem lorentzPerpGenerator_mem_dual (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) :
    lorentzPerpGenerator G hG x c hc B ∈
      (lorentzPerpForm G x c).dualSubmodule (lorentzPerpLattice G x c P) := by
  intro y hy
  change lorentzGramForm G x c (lorentzProjectedGenerator G x c B) y ∈ _
  rw [(lorentzGramForm_isSymm G x c).eq,
    lorentzProjectedGenerator_pair G hG x c hc y y.2,
    (lorentzGramForm_isSymm G x c).eq]
  exact hint (hle (gramLattice_le_lorentzMarkedLattice G x c
    (toRatSpace_mem_gramLattice G x _))) y hy

theorem four_zsmul_lorentzPerpGenerator_mem (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (B : SecondSubconstituent G x) :
    (4 : ℤ) • lorentzPerpGenerator G hG x c hc B ∈ lorentzPerpLattice G x c P := by
  change (4 : ℤ) • lorentzProjectedGenerator G x c B ∈ P
  have heq : (4 : ℤ) • lorentzProjectedGenerator G x c B =
      (4 : ℤ) • toRatSpace G x (integralGramGenerator G x B) - lorentzWeylVector G x c := by
    simp only [lorentzProjectedGenerator, lorentzHeightZeroPart,
      centroidHeight_generator G hG x c hc]
    module
  rw [heq]
  exact P.sub_mem (P.smul_mem _ (hle (gramLattice_le_lorentzMarkedLattice G x c
    (toRatSpace_mem_gramLattice G x _)))) (hle (lorentzWeylVector_mem_markedLattice G x c))

theorem lorentzPerpGenerator_sub_mem (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (B C : SecondSubconstituent G x) :
    lorentzPerpGenerator G hG x c hc B - lorentzPerpGenerator G hG x c hc C ∈
      lorentzPerpLattice G x c P := by
  change lorentzProjectedGenerator G x c B - lorentzProjectedGenerator G x c C ∈ P
  have heq : lorentzProjectedGenerator G x c B - lorentzProjectedGenerator G x c C =
      toRatSpace G x (integralGramGenerator G x B) -
        toRatSpace G x (integralGramGenerator G x C) := by
    simp only [lorentzProjectedGenerator, lorentzHeightZeroPart,
      centroidHeight_generator G hG x c hc]
    module
  rw [heq]
  exact P.sub_mem (hle (gramLattice_le_lorentzMarkedLattice G x c
    (toRatSpace_mem_gramLattice G x _))) (hle (gramLattice_le_lorentzMarkedLattice G x c
    (toRatSpace_mem_gramLattice G x _)))

theorem lorentzPerpGenerator_zsmul_mem_iff (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (heven : Lattice.IsEven (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) (m : ℤ) :
    m • lorentzPerpGenerator G hG x c hc B ∈ lorentzPerpLattice G x c P ↔ 4 ∣ m := by
  exact Lattice.zsmul_mem_iff_four_dvd_of_odd_quarter_norm
    (lorentzPerpLattice_isEven G x c heven) (a := 9) ⟨4, by norm_num⟩
    (lorentzPerpGenerator_norm G hG x c hc B)
    (four_zsmul_lorentzPerpGenerator_mem G hG x c hc hle B) m

theorem lorentzPerpGenerator_sum (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    ∑ B, lorentzPerpGenerator G hG x c hc B = 0 := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, ZeroMemClass.coe_zero, lorentzPerpGenerator] using
    lorentzProjectedGenerator_sum G hG x c hc

theorem lorentzPerpGenerator_secondMoment (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) (y : lorentzPerpSpace G x c) :
    ∑ B, (lorentzPerpForm G x c y (lorentzPerpGenerator G hG x c hc B)) ^ 2 =
      45 * lorentzPerpForm G x c y y :=
  lorentzProjectedGenerator_secondMoment G hG x c hc y y.2

end SRG266
