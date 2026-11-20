/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.Lift
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.Even

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem gramLattice_eq_span_generators (x : V) :
    gramLattice G x = Submodule.span ℤ
      (Set.range fun B => toRatSpace G x (integralGramGenerator G x B)) := by
  apply le_antisymm
  · rintro _ ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
    rw [mk_eq_sum_smul_generator, map_sum]
    exact Submodule.sum_mem _ fun B _ => by
      rw [map_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨B, rfl⟩)
  · exact Submodule.span_le.mpr (by
      rintro _ ⟨B, rfl⟩
      exact toRatSpace_mem_gramLattice G x _)

theorem centroidHeight_integral (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x)
    {z : ratGramSpace G x} (hz : z ∈ gramLattice G x) :
    centroidHeight G x c z ∈ (1 : Submodule ℤ ℚ) := by
  obtain ⟨a, rfl⟩ := hz
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  rw [mk_eq_sum_smul_generator, map_sum, map_sum]
  simp only [map_zsmul, centroidHeight_generator G hG x c hc,
    zsmul_eq_mul, mul_one]
  exact Submodule.sum_mem _ fun B _ => Submodule.mem_one.mpr ⟨a B, by simp⟩

theorem lorentzGramLattice_isIntegral (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    Lattice.IsIntegral (lorentzGramForm G x c) (gramLattice G x) := by
  rw [Lattice.isIntegral_iff_forall]
  intro u hu v hv
  obtain ⟨a, ha⟩ := Submodule.mem_one.mp (centroidHeight_integral G hG x c hc hu)
  obtain ⟨b, hb⟩ := Submodule.mem_one.mp (centroidHeight_integral G hG x c hc hv)
  obtain ⟨k, hk⟩ := Submodule.mem_one.mp (gramLattice_isIntegral G x hu v hv)
  have ha' : (a : ℚ) = centroidHeight G x c u := by simpa using ha
  have hb' : (b : ℚ) = centroidHeight G x c v := by simpa using hb
  have hk' : (k : ℚ) = ratGramForm G x u v := by simpa using hk
  rw [lorentzGramForm_apply, ← ha', ← hb', ← hk']
  exact Submodule.mem_one.mpr ⟨k - a * b, by simp⟩

theorem lorentzGramLattice_isEven (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    Lattice.IsEven (lorentzGramForm G x c) (gramLattice G x) := by
  have hint := lorentzGramLattice_isIntegral G hG x c hc
  rw [gramLattice_eq_span_generators] at hint ⊢
  apply Lattice.isEven_of_span _ (lorentzGramForm_isSymm G x c) hint
  rintro _ ⟨B, rfl⟩
  refine ⟨1, ?_⟩
  rw [lorentzGramForm_generator_generator G hG x c hc,
    localKMatrix_diagonal G hG x B]
  norm_num

def lorentzMarkedLattice (x : V) (c : IntegralGramLattice G x) :
    Submodule ℤ (ratGramSpace G x) :=
  gramLattice G x ⊔ Submodule.span ℤ {lorentzWeylVector G x c}

theorem gramLattice_le_lorentzMarkedLattice (x : V) (c : IntegralGramLattice G x) :
    gramLattice G x ≤ lorentzMarkedLattice G x c := le_sup_left

theorem lorentzWeylVector_mem_markedLattice (x : V) (c : IntegralGramLattice G x) :
    lorentzWeylVector G x c ∈ lorentzMarkedLattice G x c :=
  Submodule.mem_sup_right (Submodule.mem_span_singleton_self _)

theorem lorentzMarkedLattice_isLattice (x : V) (c : IntegralGramLattice G x) :
    Lattice.IsLattice ℚ (lorentzMarkedLattice G x c) := by
  refine ⟨(gramLattice_fg G x).sup (Submodule.fg_span_singleton _), ?_⟩
  apply top_unique
  rw [← gramLattice_span_top G x]
  exact Submodule.span_mono (gramLattice_le_lorentzMarkedLattice G x c)

theorem lorentzMarkedLattice_isIntegral (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    Lattice.IsIntegral (lorentzGramForm G x c) (lorentzMarkedLattice G x c) := by
  apply Lattice.isIntegral_sup_span_singleton _ (lorentzGramForm_isSymm G x c)
    (lorentzGramLattice_isIntegral G hG x c hc)
  · intro z hz
    rw [lorentzWeylVector_pair G hG x c hc]
    exact Submodule.neg_mem _ (centroidHeight_integral G hG x c hc hz)
  · rw [lorentzWeylVector_norm G hG x c hc]
    exact Submodule.mem_one.mpr ⟨-4, by simp⟩

theorem five_zsmul_lorentzWeylVector (x : V) (c : IntegralGramLattice G x) :
    (5 : ℤ) • lorentzWeylVector G x c = toRatSpace G x c := by
  rw [lorentzWeylVector, ← Int.cast_smul_eq_zsmul ℚ, smul_smul]
  norm_num

theorem lorentzMarkedLattice_five_smul (x : V) (c : IntegralGramLattice G x) :
    ∀ z ∈ lorentzMarkedLattice G x c, (5 : ℤ) • z ∈ gramLattice G x := by
  intro z hz
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨m, rfl⟩ := Submodule.mem_span_singleton.mp hb
  have heq : (5 : ℤ) • (a + m • lorentzWeylVector G x c) =
      (5 : ℤ) • a + m • ((5 : ℤ) • lorentzWeylVector G x c) := by module
  rw [heq, five_zsmul_lorentzWeylVector]
  exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha)
    (Submodule.smul_mem _ _ (toRatSpace_mem_gramLattice G x c))

theorem lorentzMarkedLattice_isEven (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    Lattice.IsEven (lorentzGramForm G x c) (lorentzMarkedLattice G x c) := by
  apply (lorentzGramLattice_isEven G hG x c hc).of_odd_smul _
    (lorentzMarkedLattice_isIntegral G hG x c hc) (m := 5)
  · exact ⟨2, by norm_num⟩
  · exact lorentzMarkedLattice_five_smul G x c

theorem lorentzMarkedLattice_dual_denominator (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    ∀ y ∈ (lorentzGramForm G x c).dualSubmodule (lorentzMarkedLattice G x c),
      (45 : ℤ) • y ∈ lorentzMarkedLattice G x c := by
  intro y hy
  exact gramLattice_le_lorentzMarkedLattice G x c
    (lorentz_dual_denominator G hG x c hc y
      (Lattice.dualSubmodule_antitone _ (gramLattice_le_lorentzMarkedLattice G x c) hy))

theorem exists_lorentzMarked_maximal_even_extension (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    ∃ P : Submodule ℤ (ratGramSpace G x),
      lorentzMarkedLattice G x c ≤ P ∧ Lattice.IsLattice ℚ P ∧
      Lattice.IsMaximalIntegral (lorentzGramForm G x c) P ∧
      Lattice.IsEven (lorentzGramForm G x c) P ∧
      ∀ y ∈ (lorentzGramForm G x c).dualSubmodule P, (15 : ℤ) • y ∈ P := by
  apply Lattice.exists_even_maximal_integral_overlattice_denominator _
    (lorentzGramForm_nondegenerate G hG x c hc) (lorentzGramForm_isSymm G x c)
    (lorentzMarkedLattice_isLattice G x c) (lorentzMarkedLattice_isIntegral G hG x c hc)
    (lorentzMarkedLattice_isEven G hG x c hc) (k := 45) (j := 2)
  · exact ⟨22, by norm_num⟩
  · exact lorentzMarkedLattice_dual_denominator G hG x c hc
  · norm_num

end SRG266
