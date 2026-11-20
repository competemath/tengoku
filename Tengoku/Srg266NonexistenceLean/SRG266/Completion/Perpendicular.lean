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

/--
@isnad1 id=iff.0h6v.s12.91aee2b6069c from=translated src=- shape=994d27e7 vocab=2407f53a
-/
@[simp]
theorem mem_lorentzPerpLattice (x : V) (c : IntegralGramLattice G x)
    (P : Submodule ℤ (ratGramSpace G x)) (y : lorentzPerpSpace G x c) :
    y ∈ lorentzPerpLattice G x c P ↔ (y : ratGramSpace G x) ∈ P := Iff.rfl

/--
@isnad1 id=ne.2h4v.s9.b993e35e4f99 from=translated src=- shape=fc6d8190 vocab=8ee18a42
-/
theorem centroidHeight_ne_zero (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) : centroidHeight G x c ≠ 0 := by
  intro h
  have he := centroidHeight_weylVector G hG x c hc
  rw [h, LinearMap.zero_apply] at he
  norm_num at he

/--
@isnad1 id=eq.2h4v.s9.ed7c3a01ece5 from=translated src=- shape=f2609756 vocab=b4ef0be1
-/
theorem finrank_lorentzPerpSpace (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    Module.finrank ℚ (lorentzPerpSpace G x c) = 11 := by
  have h := Module.Dual.finrank_ker_add_one_of_ne_zero
    (centroidHeight_ne_zero G hG x c hc)
  rw [finrank_ratGramSpace G hG x] at h
  change Module.finrank ℚ (centroidHeight G x c).ker = 11
  omega

/--
@isnad1 id=issymm.0h4v.s9.ad5c1ec29c38 from=translated src=- shape=a0e9a255 vocab=1e3ca23d
-/
theorem lorentzPerpForm_isSymm (x : V) (c : IntegralGramLattice G x) :
    (lorentzPerpForm G x c).IsSymm := (lorentzGramForm_isSymm G x c).restrict _

/--
@isnad1 id=lt.2h5v.s13.effb1782563a from=translated src=- shape=e65adc21 vocab=998f7bca
-/
theorem lorentzPerpForm_posDef (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (y : lorentzPerpSpace G x c) (hy : y ≠ 0) :
    0 < lorentzPerpForm G x c y y := by
  change 0 < lorentzGramForm G x c (y : ratGramSpace G x) y
  rw [lorentzGramForm_eq_ratGramForm_of_height_zero G x c y y.2]
  exact ratGramForm_posDef G hG x y (fun h => hy (Subtype.ext h))

/--
@isnad1 id=mem.5h6v.s10.aee1aba37c55 from=translated src=- shape=7662f914 vocab=86d8b9c5
-/
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

/--
@isnad1 id=islattic.5h5v.s11.eefc97ef3ea6 from=translated src=- shape=2a9f5152 vocab=40779e2d
-/
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

/--
@isnad1 id=isintegr.1h5v.s10.9316b6be4be8 from=translated src=- shape=3ce307d4 vocab=2f215c67
-/
theorem lorentzPerpLattice_isIntegral (x : V) (c : IntegralGramLattice G x)
    {P : Submodule ℤ (ratGramSpace G x)}
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P) :
    Lattice.IsIntegral (lorentzPerpForm G x c) (lorentzPerpLattice G x c P) := by
  intro y hy z hz
  exact hint hy z hz

/--
@isnad1 id=iseven.1h5v.s9.3ccf2c7a6391 from=translated src=- shape=2edab585 vocab=ba339eb0
-/
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

/--
@isnad1 id=eq.2h5v.s12.fe1814c1d405 from=translated src=- shape=8281e85d vocab=e6bc086e
-/
@[simp]
theorem lorentzPerpGenerator_norm (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) (B : SecondSubconstituent G x) :
    lorentzPerpForm G x c (lorentzPerpGenerator G hG x c hc B)
      (lorentzPerpGenerator G hG x c hc B) = 9 / 4 :=
  lorentzHeightZeroPart_generator_norm G hG x c hc B

/--
@isnad1 id=mem.4h6v.s12.2bc35c453e38 from=translated src=- shape=9a4f0483 vocab=51249a25
-/
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

/--
@isnad1 id=mem.3h6v.s12.567dbf1a5ae5 from=translated src=- shape=48b0468a vocab=a4e3c73d
-/
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

/--
@isnad1 id=mem.3h7v.s12.c4dd699a37f3 from=translated src=- shape=c08d5155 vocab=be8dd108
-/
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

/--
@isnad1 id=iff.4h7v.s12.1e5ff9a683c0 from=translated src=- shape=97a0dcb6 vocab=e1ce6652
-/
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

/--
@isnad1 id=eq.2h4v.s11.30c9dfa6cf32 from=translated src=- shape=716ea0b8 vocab=f1ca10a0
-/
theorem lorentzPerpGenerator_sum (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    ∑ B, lorentzPerpGenerator G hG x c hc B = 0 := by
  apply Subtype.ext
  simpa only [Submodule.coe_sum, ZeroMemClass.coe_zero, lorentzPerpGenerator] using
    lorentzProjectedGenerator_sum G hG x c hc

/--
@isnad1 id=eq.2h5v.s13.5b4d5cc91815 from=translated src=- shape=2cad6662 vocab=27ec7108
-/
theorem lorentzPerpGenerator_secondMoment (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) (y : lorentzPerpSpace G x c) :
    ∑ B, (lorentzPerpForm G x c y (lorentzPerpGenerator G hG x c hc B)) ^ 2 =
      45 * lorentzPerpForm G x c y y :=
  lorentzProjectedGenerator_secondMoment G hG x c hc y y.2

end SRG266
