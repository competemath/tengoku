import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open MeasureTheory UpperHalfPlane Set
open scoped MatrixGroups ENNReal RealInnerProductSpace

noncomputable section

namespace FLT.L2Carrier

abbrev AutomorphicL2 (D : Set ℍ) : Type :=
  Lp ℂ 2 ((volume : Measure ℍ).restrict D)

/--
@isnad1 id=isfinite.1h1v.s5.018f25b88a55 from=translated src=- shape=4bd24726 vocab=8db22d40
-/
theorem isFiniteMeasure_restrict_of_lt_top {D : Set ℍ} (hD : volume D < ∞) :
    IsFiniteMeasure ((volume : Measure ℍ).restrict D) :=
  ⟨by simpa [Measure.restrict_apply_univ] using hD⟩

/--
@isnad1 id=memlp.3h3v.s7.a5dc863b1371 from=translated src=- shape=6de47188 vocab=544d3d57
-/
theorem memLp_two_restrict_of_bound {D : Set ℍ} (hD : volume D < ∞) {f : ℍ → ℂ}
    (hf : AEStronglyMeasurable f ((volume : Measure ℍ).restrict D)) (C : ℝ)
    (hC : ∀ z : ℍ, ‖f z‖ ≤ C) :
    MemLp f 2 ((volume : Measure ℍ).restrict D) :=
  haveI : IsFiniteMeasure ((volume : Measure ℍ).restrict D) :=
    isFiniteMeasure_restrict_of_lt_top hD
  MemLp.of_bound hf C (Filter.Eventually.of_forall hC)

/--
@isnad1 id=memlp.4h3v.s7.fc57f7034655 from=translated src=- shape=bea1120c vocab=8f20505d
-/
theorem memLp_two_restrict_of_bound_on {D : Set ℍ} (hD : volume D < ∞)
    (hDm : MeasurableSet D) {f : ℍ → ℂ} (hf : Continuous f) (C : ℝ)
    (hC : ∀ z ∈ D, ‖f z‖ ≤ C) :
    MemLp f 2 ((volume : Measure ℍ).restrict D) := by
  haveI : IsFiniteMeasure ((volume : Measure ℍ).restrict D) :=
    isFiniteMeasure_restrict_of_lt_top hD
  refine MemLp.of_bound hf.aestronglyMeasurable C ?_
  rw [ae_restrict_iff' hDm]
  exact Filter.Eventually.of_forall hC

def boundedToL2 {D : Set ℍ} (hD : volume D < ∞) (hDm : MeasurableSet D) (f : ℍ → ℂ)
    (hf : Continuous f) (C : ℝ) (hC : ∀ z ∈ D, ‖f z‖ ≤ C) : AutomorphicL2 D :=
  (memLp_two_restrict_of_bound_on hD hDm hf C hC).toLp f

/--
@isnad1 id=eventual.4h3v.s8.9f216078109b from=translated src=- shape=66889d07 vocab=f05f24b4
-/
theorem boundedToL2_coeFn {D : Set ℍ} (hD : volume D < ∞) (hDm : MeasurableSet D)
    (f : ℍ → ℂ) (hf : Continuous f) (C : ℝ) (hC : ∀ z ∈ D, ‖f z‖ ≤ C) :
    (boundedToL2 hD hDm f hf C hC : ℍ → ℂ) =ᵐ[(volume : Measure ℍ).restrict D] f :=
  MemLp.coeFn_toLp _

/--
@isnad1 id=eq.6h5v.s8.7bbdd6dc7199 from=translated src=- shape=8b186772 vocab=c4368627
-/
theorem boundedToL2_add {D : Set ℍ} (hD : volume D < ∞) (hDm : MeasurableSet D)
    (f g : ℍ → ℂ) (hf : Continuous f) (hg : Continuous g) (C C' : ℝ)
    (hC : ∀ z ∈ D, ‖f z‖ ≤ C) (hC' : ∀ z ∈ D, ‖g z‖ ≤ C') :
    boundedToL2 hD hDm (f + g) (hf.add hg) (C + C')
        (fun z hz => (norm_add_le _ _).trans (add_le_add (hC z hz) (hC' z hz))) =
      boundedToL2 hD hDm f hf C hC + boundedToL2 hD hDm g hg C' hC' := by
  simp only [boundedToL2]
  exact MemLp.toLp_add _ _

/--
@isnad1 id=ex.2h1v.s6.32f791108210 from=translated src=- shape=3f69fed6 vocab=665337d2
-/
theorem exists_bound_on_fd_of_isZeroAtImInfty {f : ℍ → ℂ} (hf : Continuous f)
    (hinf : IsZeroAtImInfty f) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ ModularGroup.fd, ‖f z‖ ≤ C := by

  obtain ⟨A, hA⟩ := (isZeroAtImInfty_iff.mp hinf) 1 one_pos

  have hcpt : IsCompact (ModularGroup.truncatedFundamentalDomain A) :=
    ModularGroup.isCompact_truncatedFundamentalDomain A
  have hbdd : BddAbove ((fun z => ‖f z‖) '' ModularGroup.truncatedFundamentalDomain A) :=
    (hcpt.image (by fun_prop)).bddAbove
  obtain ⟨B, hB⟩ := hbdd
  refine ⟨max B 1, le_trans zero_le_one (le_max_right _ _), fun z hz => ?_⟩
  rcases le_total z.im A with him | him
  ·
    exact le_trans (hB ⟨z, ⟨hz, him⟩, rfl⟩) (le_max_left _ _)
  ·
    exact le_trans (hA z him) (le_max_right _ _)

/--
@isnad1 id=memlp.4h1v.s7.4788a19d2455 from=translated src=- shape=1d8224d2 vocab=ee90e9ce
-/
theorem memLp_two_fd_of_isZeroAtImInfty (hvol : volume ModularGroup.fd < ∞)
    (hmeas : MeasurableSet ModularGroup.fd) {f : ℍ → ℂ} (hf : Continuous f)
    (hinf : IsZeroAtImInfty f) :
    MemLp f 2 ((volume : Measure ℍ).restrict ModularGroup.fd) := by
  obtain ⟨C, _, hC⟩ := exists_bound_on_fd_of_isZeroAtImInfty hf hinf
  exact memLp_two_restrict_of_bound_on hvol hmeas hf C hC

/--
@isnad1 id=measurep.0h1v.s8.bcc40a6c4c0d from=translated src=- shape=a8325292 vocab=5c49909c
-/
theorem measurePreserving_smul_upperHalfPlane (g : GL (Fin 2) ℝ) :
    MeasurePreserving (fun z : ℍ => g • z) volume volume :=
  MeasureTheory.measurePreserving_smul g (volume : Measure ℍ)

def rightRegular (g : GL (Fin 2) ℝ) :
    Lp ℂ 2 (volume : Measure ℍ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℍ) :=
  Lp.compMeasurePreservingₗᵢ ℂ (fun z : ℍ => g • z)
    (measurePreserving_smul_upperHalfPlane g)

/--
@isnad1 id=eq.0h2v.s11.b7d2bed05bee from=translated src=- shape=b2134841 vocab=3a028760
-/
theorem norm_rightRegular_apply (g : GL (Fin 2) ℝ) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    ‖rightRegular g f‖ = ‖f‖ :=
  (rightRegular g).norm_map f

/--
@isnad1 id=eq.0h3v.s13.db0f0702808e from=translated src=- shape=2e0fcf44 vocab=549dd398
-/
theorem rightRegular_mul (g h : GL (Fin 2) ℝ) (f : Lp ℂ 2 (volume : Measure ℍ)) :
    rightRegular (g * h) f = rightRegular h (rightRegular g f) := by

  show Lp.compMeasurePreserving (fun z : ℍ => (g * h) • z)
      (measurePreserving_smul_upperHalfPlane (g * h)) f =
    Lp.compMeasurePreserving (fun z : ℍ => h • z) (measurePreserving_smul_upperHalfPlane h)
      (Lp.compMeasurePreserving (fun z : ℍ => g • z)
        (measurePreserving_smul_upperHalfPlane g) f)
  rw [← Lp.compMeasurePreserving_comp_apply f]

  congr 1
  congr 1
  exact funext fun z => mul_smul g h z

def FundamentalDomainFiniteVolume : Prop :=
  volume ModularGroup.fd < ∞ ∧ MeasurableSet ModularGroup.fd

/--
@isnad1 id=memlp.3h1v.s6.ca27a60018ed from=translated src=- shape=e19bd9ef vocab=a7407c90
-/
theorem cuspFormMemL2_of_finiteVolume (h : FundamentalDomainFiniteVolume)
    {f : ℍ → ℂ} (hf : Continuous f) (hinf : IsZeroAtImInfty f) :
    MemLp f 2 ((volume : Measure ℍ).restrict ModularGroup.fd) :=
  memLp_two_fd_of_isZeroAtImInfty h.1 h.2 hf hinf

/--
@isnad1 id=memlp.1h1v.s6.d3dfc645b9af from=translated src=- shape=9e844a1c vocab=dd2868de
-/
theorem gate_const_memLp_of_finite {D : Set ℍ} (hD : volume D < ∞) :
    MemLp (fun _ : ℍ => (1 : ℂ)) 2 ((volume : Measure ℍ).restrict D) :=
  haveI : IsFiniteMeasure ((volume : Measure ℍ).restrict D) :=
    isFiniteMeasure_restrict_of_lt_top hD
  memLp_const 1

/--
@isnad1 id=not.1h1v.s6.8a3554455aa1 from=translated src=- shape=c22bf4b1 vocab=9b0b7ad8
-/
theorem gate_const_not_memLp_of_infinite {μ : Measure ℍ} (hμ : μ univ = ∞) :
    ¬ MemLp (fun _ : ℍ => (1 : ℂ)) 2 μ := by
  intro h
  rcases (memLp_const_iff (by norm_num) (by norm_num)).mp h with h1 | h2
  · exact one_ne_zero h1
  · exact absurd (hμ ▸ h2) (lt_irrefl _)

/--
@isnad1 id=eq.0h1v.s6.211805fd49d7 from=translated src=- shape=9382e532 vocab=b7124957
-/
theorem gate_empty_carrier_subsingleton (f : AutomorphicL2 (∅ : Set ℍ)) : f = 0 := by

  apply Lp.ext_iff.mpr
  have hbot : ae ((volume : Measure ℍ).restrict (∅ : Set ℍ)) = ⊥ :=
    ae_eq_bot.mpr Measure.restrict_empty
  rw [Filter.EventuallyEq, hbot]
  exact Filter.eventually_bot

/--
@isnad1 id=eq.2h1v.s7.f28ea2816f37 from=translated src=- shape=dd338aa1 vocab=828d74b1
-/
theorem gate_boundedToL2_zero {D : Set ℍ} (hD : volume D < ∞) (hDm : MeasurableSet D) :
    boundedToL2 hD hDm (fun _ => (0 : ℂ)) continuous_const 0
      (fun _ _ => by simp) = 0 := by
  simp only [boundedToL2]
  exact MemLp.toLp_zero _

end FLT.L2Carrier
end
