/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.Perpendicular
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.MarkedDiscriminant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

noncomputable def lorentzIntegralProjection (x : V) (c : IntegralGramLattice G x)
    (B : SecondSubconstituent G x) : ratGramSpace G x →ₗ[ℚ] lorentzPerpSpace G x c :=
  Lattice.kernelNumerator (centroidHeight G x c)
    (toRatSpace G x (integralGramGenerator G x B))

theorem lorentzIntegralProjection_apply (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) (z : ratGramSpace G x) :
    (lorentzIntegralProjection G x c B z : ratGramSpace G x) =
      z - centroidHeight G x c z • toRatSpace G x (integralGramGenerator G x B) := by
  change centroidHeight G x c (toRatSpace G x (integralGramGenerator G x B)) • z -
    centroidHeight G x c z • toRatSpace G x (integralGramGenerator G x B) = _
  rw [centroidHeight_generator G hG x c hc, one_smul]

theorem lorentzIntegralProjection_apply_perp (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) (y : lorentzPerpSpace G x c) :
    lorentzIntegralProjection G x c B (y : ratGramSpace G x) = y := by
  apply Subtype.ext
  rw [lorentzIntegralProjection_apply G hG x c hc]
  have hy : centroidHeight G x c (y : ratGramSpace G x) = 0 := y.2
  rw [hy, zero_smul, sub_zero]

theorem centroidHeight_integral_on_dual (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    {z : ratGramSpace G x} (hz : z ∈ (lorentzGramForm G x c).dualSubmodule P) :
    centroidHeight G x c z ∈ (1 : Submodule ℤ ℚ) := by
  have h := hz _ (hle (lorentzWeylVector_mem_markedLattice G x c))
  rw [(lorentzGramForm_isSymm G x c).eq, lorentzWeylVector_pair G hG x c hc] at h
  simpa only [neg_neg] using (1 : Submodule ℤ ℚ).neg_mem h

theorem lorentzIntegralProjection_mem (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {z : ratGramSpace G x} (hz : z ∈ P) :
    lorentzIntegralProjection G x c B z ∈ lorentzPerpLattice G x c P := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp
    (centroidHeight_integral_of_marked_le G hG x c hc hle hint hz)
  have ha' : (a : ℚ) = centroidHeight G x c z := by simpa using ha
  rw [mem_lorentzPerpLattice, lorentzIntegralProjection_apply G hG x c hc,
    ← ha', Int.cast_smul_eq_zsmul]
  exact P.sub_mem hz (P.smul_mem _ (hle (gramLattice_le_lorentzMarkedLattice G x c
    (toRatSpace_mem_gramLattice G x _))))

theorem lorentzIntegralProjection_map_lattice (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) :
    P.map ((lorentzIntegralProjection G x c B).restrictScalars ℤ) =
      lorentzPerpLattice G x c P := by
  apply le_antisymm
  · rintro _ ⟨z, hz, rfl⟩
    exact lorentzIntegralProjection_mem G hG x c hc hle hint B hz
  · intro y hy
    exact ⟨y, hy, lorentzIntegralProjection_apply_perp G hG x c hc B y⟩

theorem lorentzIntegralProjection_mem_dual (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {z : ratGramSpace G x}
    (hz : z ∈ (lorentzGramForm G x c).dualSubmodule P) :
    lorentzIntegralProjection G x c B z ∈
      (lorentzPerpForm G x c).dualSubmodule (lorentzPerpLattice G x c P) := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (centroidHeight_integral_on_dual G hG x c hc hle hz)
  have ha' : (a : ℚ) = centroidHeight G x c z := by simpa using ha
  intro y hy
  change lorentzGramForm G x c (lorentzIntegralProjection G x c B z) y ∈ _
  rw [lorentzIntegralProjection_apply G hG x c hc, ← ha', Int.cast_smul_eq_zsmul,
    map_sub, LinearMap.sub_apply, map_zsmul, LinearMap.smul_apply]
  exact (1 : Submodule ℤ ℚ).sub_mem (hz y hy) ((1 : Submodule ℤ ℚ).smul_mem a
    (hint (hle (gramLattice_le_lorentzMarkedLattice G x c
      (toRatSpace_mem_gramLattice G x _))) y hy))

theorem lorentzIntegralProjection_mem_iff (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {z : ratGramSpace G x}
    (hz : z ∈ (lorentzGramForm G x c).dualSubmodule P) :
    lorentzIntegralProjection G x c B z ∈ lorentzPerpLattice G x c P ↔ z ∈ P := by
  constructor
  · intro hj
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (centroidHeight_integral_on_dual G hG x c hc hle hz)
    have ha' : (a : ℚ) = centroidHeight G x c z := by simpa using ha
    rw [mem_lorentzPerpLattice, lorentzIntegralProjection_apply G hG x c hc,
      ← ha', Int.cast_smul_eq_zsmul] at hj
    have hg := P.smul_mem a (hle (gramLattice_le_lorentzMarkedLattice G x c
      (toRatSpace_mem_gramLattice G x (integralGramGenerator G x B))))
    simpa only [sub_add_cancel] using P.add_mem hj hg
  · exact lorentzIntegralProjection_mem G hG x c hc hle hint B

noncomputable def lorentzPerpDualLift (x : V) (c : IntegralGramLattice G x)
    (B : SecondSubconstituent G x) (y : lorentzPerpSpace G x c) : ratGramSpace G x :=
  (y : ratGramSpace G x) +
    lorentzGramForm G x c y (toRatSpace G x (integralGramGenerator G x B)) •
      lorentzWeylVector G x c

theorem lorentzPerpDualLift_pair (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) (y : lorentzPerpSpace G x c) (z : ratGramSpace G x) :
    lorentzGramForm G x c (lorentzPerpDualLift G x c B y) z =
      lorentzPerpForm G x c y (lorentzIntegralProjection G x c B z) := by
  change lorentzGramForm G x c (lorentzPerpDualLift G x c B y) z =
    lorentzGramForm G x c y (lorentzIntegralProjection G x c B z)
  rw [lorentzIntegralProjection_apply G hG x c hc, lorentzPerpDualLift]
  simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply,
    smul_eq_mul, map_sub]
  rw [lorentzWeylVector_pair G hG x c hc]
  ring

theorem lorentzPerpDualLift_mem_dual (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {y : lorentzPerpSpace G x c}
    (hy : y ∈ (lorentzPerpForm G x c).dualSubmodule (lorentzPerpLattice G x c P)) :
    lorentzPerpDualLift G x c B y ∈ (lorentzGramForm G x c).dualSubmodule P := by
  intro z hz
  rw [lorentzPerpDualLift_pair G hG x c hc]
  exact hy _ (lorentzIntegralProjection_mem G hG x c hc hle hint B hz)

theorem lorentzPerpDualLift_decomposition (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) (y : lorentzPerpSpace G x c) :
    y = lorentzIntegralProjection G x c B (lorentzPerpDualLift G x c B y) +
      centroidHeight G x c (lorentzPerpDualLift G x c B y) •
        lorentzPerpGenerator G hG x c hc B := by
  apply Subtype.ext
  have hy : centroidHeight G x c (y : ratGramSpace G x) = 0 := y.2
  change (y : ratGramSpace G x) =
    (lorentzIntegralProjection G x c B (lorentzPerpDualLift G x c B y) : ratGramSpace G x) +
      centroidHeight G x c (lorentzPerpDualLift G x c B y) • lorentzProjectedGenerator G x c B
  rw [lorentzIntegralProjection_apply G hG x c hc]
  simp only [lorentzPerpDualLift, lorentzProjectedGenerator, lorentzHeightZeroPart,
    map_add, map_smul, hy, centroidHeight_weylVector G hG x c hc,
    centroidHeight_generator G hG x c hc, smul_eq_mul, zero_add]
  module

theorem lorentzPerp_dual_eq_map_sup_marked (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) :
    (lorentzPerpForm G x c).dualSubmodule (lorentzPerpLattice G x c P) =
      ((lorentzGramForm G x c).dualSubmodule P).map
        ((lorentzIntegralProjection G x c B).restrictScalars ℤ) ⊔
      Submodule.span ℤ {lorentzPerpGenerator G hG x c hc B} := by
  apply le_antisymm
  · intro y hy
    have hz := lorentzPerpDualLift_mem_dual G hG x c hc hle hint B hy
    obtain ⟨a, ha⟩ := Submodule.mem_one.mp (centroidHeight_integral_on_dual G hG x c hc hle hz)
    have ha' : (a : ℚ) = centroidHeight G x c (lorentzPerpDualLift G x c B y) := by
      simpa using ha
    have hsmul : (a : ℚ) • lorentzPerpGenerator G hG x c hc B =
        (a : ℤ) • lorentzPerpGenerator G hG x c hc B := by module
    rw [lorentzPerpDualLift_decomposition G hG x c hc B y, ← ha', hsmul]
    exact Submodule.add_mem _ (Submodule.mem_sup_left ⟨_, hz, rfl⟩)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · apply sup_le
    · rintro _ ⟨z, hz, rfl⟩
      exact lorentzIntegralProjection_mem_dual G hG x c hc hle hint B hz
    · apply Submodule.span_le.mpr
      rintro z (rfl : z = _)
      exact lorentzPerpGenerator_mem_dual G hG x c hc hle hint B

theorem lorentzIntegralProjection_pair (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) (z w : ratGramSpace G x) :
    lorentzPerpForm G x c (lorentzIntegralProjection G x c B z)
        (lorentzIntegralProjection G x c B w) =
      lorentzGramForm G x c z w - centroidHeight G x c z *
        lorentzGramForm G x c (toRatSpace G x (integralGramGenerator G x B)) w -
      centroidHeight G x c w * lorentzGramForm G x c z
        (toRatSpace G x (integralGramGenerator G x B)) +
      2 * centroidHeight G x c z * centroidHeight G x c w := by
  change lorentzGramForm G x c (lorentzIntegralProjection G x c B z)
    (lorentzIntegralProjection G x c B w) = _
  rw [lorentzIntegralProjection_apply G hG x c hc, lorentzIntegralProjection_apply G hG x c hc]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [lorentzGramForm_generator_generator G hG x c hc, localKMatrix_diagonal G hG x B]
  norm_num
  ring

theorem lorentzIntegralProjection_norm_mod_even (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (B : SecondSubconstituent G x) {z : ratGramSpace G x}
    (hz : z ∈ (lorentzGramForm G x c).dualSubmodule P) :
    ∃ n : ℤ, lorentzPerpForm G x c (lorentzIntegralProjection G x c B z)
        (lorentzIntegralProjection G x c B z) = lorentzGramForm G x c z z + 2 * (n : ℚ) := by
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (centroidHeight_integral_on_dual G hG x c hc hle hz)
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp (hz _ (hle (gramLattice_le_lorentzMarkedLattice G x c
    (toRatSpace_mem_gramLattice G x (integralGramGenerator G x B)))))
  have ha' : (a : ℚ) = centroidHeight G x c z := by simpa using ha
  have hb' : (b : ℚ) = lorentzGramForm G x c z
      (toRatSpace G x (integralGramGenerator G x B)) := by simpa using hb
  refine ⟨a ^ 2 - a * b, ?_⟩
  rw [lorentzIntegralProjection_pair G hG x c hc,
    (lorentzGramForm_isSymm G x c).eq (toRatSpace G x (integralGramGenerator G x B)) z,
    ← ha', ← hb']
  push_cast
  ring

theorem lorentzIntegralProjection_pair_marked (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    (B : SecondSubconstituent G x) (z : ratGramSpace G x) :
    lorentzPerpForm G x c (lorentzIntegralProjection G x c B z)
        (lorentzPerpGenerator G hG x c hc B) =
      lorentzGramForm G x c z (toRatSpace G x (integralGramGenerator G x B)) -
        2 * centroidHeight G x c z := by
  change lorentzGramForm G x c (lorentzIntegralProjection G x c B z)
    (lorentzProjectedGenerator G x c B) = _
  rw [lorentzProjectedGenerator_pair G hG x c hc _ (lorentzIntegralProjection G x c B z).2,
    lorentzIntegralProjection_apply G hG x c hc]
  simp only [map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul]
  rw [lorentzGramForm_generator_generator G hG x c hc, localKMatrix_diagonal G hG x B]
  norm_num
  ring

theorem lorentzIntegralProjection_pair_integral (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (B : SecondSubconstituent G x) {z w : ratGramSpace G x}
    (hz : z ∈ (lorentzGramForm G x c).dualSubmodule P)
    (hw : w ∈ (lorentzGramForm G x c).dualSubmodule P)
    (hzw : lorentzGramForm G x c z w ∈ (1 : Submodule ℤ ℚ)) :
    lorentzPerpForm G x c (lorentzIntegralProjection G x c B z)
      (lorentzIntegralProjection G x c B w) ∈ (1 : Submodule ℤ ℚ) := by
  have hg := hle (gramLattice_le_lorentzMarkedLattice G x c
    (toRatSpace_mem_gramLattice G x (integralGramGenerator G x B)))
  obtain ⟨a, ha⟩ := Lattice.mem_one_iff.mp (centroidHeight_integral_on_dual G hG x c hc hle hz)
  obtain ⟨b, hb⟩ := Lattice.mem_one_iff.mp (centroidHeight_integral_on_dual G hG x c hc hle hw)
  obtain ⟨d, hd⟩ := Lattice.mem_one_iff.mp (hz _ hg)
  obtain ⟨e, he⟩ := Lattice.mem_one_iff.mp (hw _ hg)
  obtain ⟨k, hk⟩ := Lattice.mem_one_iff.mp hzw
  refine Lattice.mem_one_iff.mpr ⟨k - a * e - b * d + 2 * a * b, ?_⟩
  rw [lorentzIntegralProjection_pair G hG x c hc,
    (lorentzGramForm_isSymm G x c).eq (toRatSpace G x (integralGramGenerator G x B)) w,
    ← ha, ← hb, ← hd, ← he, ← hk]
  push_cast
  ring

theorem lorentzIntegralProjection_pair_marked_integral (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (B : SecondSubconstituent G x) {z : ratGramSpace G x}
    (hz : z ∈ (lorentzGramForm G x c).dualSubmodule P) :
    lorentzPerpForm G x c (lorentzIntegralProjection G x c B z)
      (lorentzPerpGenerator G hG x c hc B) ∈ (1 : Submodule ℤ ℚ) := by
  rw [lorentzIntegralProjection_pair_marked G hG x c hc]
  apply (1 : Submodule ℤ ℚ).sub_mem
  · exact hz _ (hle (gramLattice_le_lorentzMarkedLattice G x c
      (toRatSpace_mem_gramLattice G x _)))
  · simpa only [zsmul_eq_mul, Int.cast_ofNat] using
      (1 : Submodule ℤ ℚ).smul_mem (2 : ℤ)
        (centroidHeight_integral_on_dual G hG x c hc hle hz)

theorem lorentzPerp_dual_eq_sup_span (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) (s : Set (ratGramSpace G x))
    (hdual : (lorentzGramForm G x c).dualSubmodule P = P ⊔ Submodule.span ℤ s) :
    (lorentzPerpForm G x c).dualSubmodule (lorentzPerpLattice G x c P) =
      lorentzPerpLattice G x c P ⊔ Submodule.span ℤ
        ({lorentzPerpGenerator G hG x c hc B} ∪ (lorentzIntegralProjection G x c B) '' s) := by
  rw [lorentzPerp_dual_eq_map_sup_marked G hG x c hc hle hint B, hdual,
    Submodule.map_sup, lorentzIntegralProjection_map_lattice G hG x c hc hle hint B,
    Submodule.map_span, Submodule.span_union]
  ac_rfl

theorem lorentzIntegralProjection_zsmul_mem (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {z : ratGramSpace G x} {m : ℤ} (hz : m • z ∈ P) :
    m • lorentzIntegralProjection G x c B z ∈ lorentzPerpLattice G x c P := by
  have h := lorentzIntegralProjection_mem G hG x c hc hle hint B hz
  rwa [map_zsmul] at h

theorem lorentzIntegralProjection_mem_torsionPart (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {z : ratGramSpace G x} {p : ℕ}
    (hz : z ∈ Lattice.torsionPart (lorentzGramForm G x c) P p) :
    lorentzIntegralProjection G x c B z ∈
      Lattice.torsionPart (lorentzPerpForm G x c) (lorentzPerpLattice G x c P) p := by
  obtain ⟨hd, hm⟩ := Lattice.mem_torsionPart.mp hz
  exact Lattice.mem_torsionPart.mpr
    ⟨lorentzIntegralProjection_mem_dual G hG x c hc hle hint B hd,
      lorentzIntegralProjection_zsmul_mem G hG x c hc hle hint B hm⟩

theorem lorentzIntegralProjection_zsmul_mem_iff (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (B : SecondSubconstituent G x) {z : ratGramSpace G x}
    (hz : z ∈ (lorentzGramForm G x c).dualSubmodule P) (m : ℤ) :
    m • lorentzIntegralProjection G x c B z ∈ lorentzPerpLattice G x c P ↔ m • z ∈ P := by
  have h := lorentzIntegralProjection_mem_iff G hG x c hc hle hint B
    (((lorentzGramForm G x c).dualSubmodule P).smul_mem m hz)
  rwa [map_zsmul] at h

theorem lorentzPerp_dual_denominator (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (hden : ∀ z ∈ (lorentzGramForm G x c).dualSubmodule P, (15 : ℤ) • z ∈ P)
    (B : SecondSubconstituent G x) :
    ∀ y ∈ (lorentzPerpForm G x c).dualSubmodule (lorentzPerpLattice G x c P),
      (60 : ℤ) • y ∈ lorentzPerpLattice G x c P := by
  intro y hy
  rw [lorentzPerp_dual_eq_map_sup_marked G hG x c hc hle hint B] at hy
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
  obtain ⟨z, hz, rfl⟩ := ha
  obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hb
  have h15 := lorentzIntegralProjection_zsmul_mem G hG x c hc hle hint B (hden z hz)
  have h4 := four_zsmul_lorentzPerpGenerator_mem G hG x c hc hle B
  have heq : (60 : ℤ) • (lorentzIntegralProjection G x c B z +
      m • lorentzPerpGenerator G hG x c hc B) =
      (4 : ℤ) • ((15 : ℤ) • lorentzIntegralProjection G x c B z) +
      (15 * m) • ((4 : ℤ) • lorentzPerpGenerator G hG x c hc B) := by module
  change (60 : ℤ) • (lorentzIntegralProjection G x c B z +
    m • lorentzPerpGenerator G hG x c hc B) ∈ lorentzPerpLattice G x c P
  rw [heq]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ h15) (Submodule.smul_mem _ _ h4)

theorem lorentzPerp_four_torsion_eq_span_marked (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x) (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {P : Submodule ℤ (ratGramSpace G x)} (hle : lorentzMarkedLattice G x c ≤ P)
    (hint : Lattice.IsIntegral (lorentzGramForm G x c) P)
    (hden : ∀ z ∈ (lorentzGramForm G x c).dualSubmodule P, (15 : ℤ) • z ∈ P)
    (B : SecondSubconstituent G x) :
    Lattice.torsionPart (lorentzPerpForm G x c) (lorentzPerpLattice G x c P) 4 =
      lorentzPerpLattice G x c P ⊔ Submodule.span ℤ {lorentzPerpGenerator G hG x c hc B} := by
  apply le_antisymm
  · intro y hy
    obtain ⟨hyd, hy4⟩ := Lattice.mem_torsionPart.mp hy
    rw [lorentzPerp_dual_eq_map_sup_marked G hG x c hc hle hint B] at hyd
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hyd
    obtain ⟨z, hz, rfl⟩ := ha
    obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hb
    have h15 := lorentzIntegralProjection_zsmul_mem G hG x c hc hle hint B (hden z hz)
    have h4 := four_zsmul_lorentzPerpGenerator_mem G hG x c hc hle B
    have heq : (4 : ℤ) • (lorentzIntegralProjection G x c B z +
        m • lorentzPerpGenerator G hG x c hc B) -
        m • ((4 : ℤ) • lorentzPerpGenerator G hG x c hc B) =
        (4 : ℤ) • lorentzIntegralProjection G x c B z := by module
    have hj4 : (4 : ℤ) • lorentzIntegralProjection G x c B z ∈ lorentzPerpLattice G x c P := by
      rw [← heq]
      exact Submodule.sub_mem _ hy4 (Submodule.smul_mem _ m h4)
    have heq' : (4 : ℤ) • ((4 : ℤ) • lorentzIntegralProjection G x c B z) -
        (15 : ℤ) • lorentzIntegralProjection G x c B z = lorentzIntegralProjection G x c B z := by module
    have hj : lorentzIntegralProjection G x c B z ∈ lorentzPerpLattice G x c P := by
      rw [← heq']
      exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hj4) h15
    exact Submodule.add_mem _ (Submodule.mem_sup_left hj)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self _)))
  · apply sup_le (Lattice.le_torsionPart (lorentzPerpLattice_isIntegral G x c hint) 4)
    apply Submodule.span_le.mpr
    rintro y (rfl : y = _)
    exact Lattice.mem_torsionPart.mpr
      ⟨lorentzPerpGenerator_mem_dual G hG x c hc hle hint B,
        four_zsmul_lorentzPerpGenerator_mem G hG x c hc hle B⟩

theorem exists_lorentzPerp_discriminant_from_graph (hG : IsHypothetical G) (x : V)
    (B : SecondSubconstituent G x) :
    ∃ (c : IntegralGramLattice G x)
      (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
      (P : Submodule ℤ (ratGramSpace G x)),
      lorentzMarkedLattice G x c ≤ P ∧
      Lattice.IsMaximalIntegral (lorentzGramForm G x c) P ∧
      Lattice.IsLattice ℚ (lorentzPerpLattice G x c P) ∧
      Lattice.IsEven (lorentzPerpForm G x c) (lorentzPerpLattice G x c P) ∧
      Module.finrank ℚ (lorentzPerpSpace G x c) = 11 ∧
      (∀ y : lorentzPerpSpace G x c, y ≠ 0 → 0 < lorentzPerpForm G x c y y) ∧
      ∃ (S : Lattice.GlueBasis (lorentzGramForm G x c) P 3)
        (T : Lattice.GlueBasis (lorentzGramForm G x c) P 5),
      (lorentzPerpForm G x c).dualSubmodule (lorentzPerpLattice G x c P) =
        lorentzPerpLattice G x c P ⊔ Submodule.span ℤ
          ({lorentzPerpGenerator G hG x c hc B} ∪
            (lorentzIntegralProjection G x c B) '' (Set.range S.vec ∪ Set.range T.vec)) := by
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨P, hle, hlat, hmax, heven, S, T, hdual⟩ :=
    exists_lorentzMarked_orthogonal_glue G hG x c hc
  exact ⟨c, hc, P, hle, hmax, lorentzPerpLattice_isLattice G hG x c hc hle hlat hmax.integral,
    lorentzPerpLattice_isEven G x c heven, finrank_lorentzPerpSpace G hG x c hc,
    lorentzPerpForm_posDef G hG x c, S, T,
    lorentzPerp_dual_eq_sup_span G hG x c hc hle hmax.integral B _ hdual⟩

end SRG266
