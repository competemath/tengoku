import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_Gamma0FundamentalSet
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_L2AutomorphicCarrier
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_TruncatedDomainPartition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open MeasureTheory
open scoped Modular MatrixGroups Pointwise ENNReal

noncomputable section

namespace FLT.L2ProductionInstance

open FLT.Gamma0FundamentalSet FLT.L2Carrier

/--
@isnad1 id=isclosed.0h1v.s7.e9c845c33b7d from=translated src=- shape=eb1a4cad vocab=451b2c3f
-/
theorem isClosed_smul_fd (γ : SL(2, ℤ)) : IsClosed (γ • 𝒟) :=
  ModularGroup.isClosed_fd.smul γ

/--
@isnad1 id=measurab.0h1v.s7.815cb8178bab from=translated src=- shape=eb1a4cad vocab=c25f5608
-/
theorem measurableSet_smul_fd (γ : SL(2, ℤ)) : MeasurableSet (γ • 𝒟) :=
  (isClosed_smul_fd γ).measurableSet

/--
@isnad1 id=countabl.0h0v.s4.cfea584b0f54 from=translated src=- shape=b781e9e2 vocab=cea6f078
-/
instance countable_SL2Z : Countable SL(2, ℤ) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) :=
    inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  inferInstanceAs (Countable { A : Matrix (Fin 2) (Fin 2) ℤ // A.det = 1 })

/--
@isnad1 id=countabl.0h1v.s7.7f6136c0794a from=translated src=- shape=23105b54 vocab=e26447e7
-/
instance countable_quotient (Γ : Subgroup SL(2, ℤ)) : Countable (SL(2, ℤ) ⧸ Γ) :=
  Quotient.countable

/--
@isnad1 id=measurab.0h1v.s5.42609c2780e4 from=translated src=- shape=edb20c5f vocab=72f828f5
-/
theorem measurableSet_gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) :
    MeasurableSet (gammaFundamentalSet Γ) :=
  MeasurableSet.iUnion fun q => measurableSet_smul_fd (Quotient.out q)⁻¹

/--
@isnad1 id=measurab.0h1v.s3.6afce92892e2 from=translated src=- shape=757122a2 vocab=1ace661a
-/
theorem measurableSet_gamma0 (N : ℕ) : MeasurableSet (gammaFundamentalSet (Gamma0 N)) :=
  measurableSet_gammaFundamentalSet (Gamma0 N)

abbrev Gamma0L2 (N : ℕ) : Type :=
  AutomorphicL2 (gammaFundamentalSet (Gamma0 N))

/--
@isnad1 id=isfinite.0h1v.s4.c807d29e5fc7 from=translated src=- shape=95807a9d vocab=86f94936
-/
instance isFiniteMeasure_gamma0 (N : ℕ) [NeZero N] :
    IsFiniteMeasure ((volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))) :=
  isFiniteMeasure_restrict_of_lt_top (volume_gamma0_lt_top N)

noncomputable def boundedToGamma0L2 (N : ℕ) [NeZero N] (f : ℍ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ z ∈ gammaFundamentalSet (Gamma0 N), ‖f z‖ ≤ C) : Gamma0L2 N :=
  boundedToL2 (volume_gamma0_lt_top N) (measurableSet_gamma0 N) f hf C hC

/--
@isnad1 id=eventual.2h3v.s8.79f24472b54c from=translated src=- shape=a4ff3e46 vocab=e8ebe06b
-/
theorem boundedToGamma0L2_coeFn (N : ℕ) [NeZero N] (f : ℍ → ℂ) (hf : Continuous f)
    (C : ℝ) (hC : ∀ z ∈ gammaFundamentalSet (Gamma0 N), ‖f z‖ ≤ C) :
    (boundedToGamma0L2 N f hf C hC : ℍ → ℂ)
      =ᵐ[(volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))] f :=
  boundedToL2_coeFn _ _ f hf C hC

noncomputable def gamma0L2Const (N : ℕ) [NeZero N] : Gamma0L2 N :=
  boundedToGamma0L2 N (fun _ => (1 : ℂ)) continuous_const 1 (fun _ _ => by simp)

/--
@isnad1 id=ne.0h1v.s6.8cb401c4527c from=translated src=- shape=2ca71cb7 vocab=633be884
-/
theorem gamma0L2Const_ne_zero (N : ℕ) [NeZero N] : gamma0L2Const N ≠ 0 := by
  intro h

  have h1 : (gamma0L2Const N : ℍ → ℂ)
      =ᵐ[(volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))] 0 :=
    Lp.eq_zero_iff_ae_eq_zero.mp h
  have h2 : (fun _ : ℍ => (1 : ℂ))
      =ᵐ[(volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))] 0 :=
    (boundedToGamma0L2_coeFn N (fun _ => (1 : ℂ)) continuous_const 1
      (fun _ _ => by simp)).symm.trans h1

  have hnull : (volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))
      Set.univ = 0 := by
    have h3 : ∀ᵐ z ∂((volume : Measure ℍ).restrict (gammaFundamentalSet (Gamma0 N))),
        (1 : ℂ) = 0 := h2
    simpa [ae_iff] using h3
  rw [Measure.restrict_apply_univ] at hnull
  exact absurd hnull (volume_gammaFundamentalSet_pos (Gamma0 N)).ne'

/--
@isnad1 id=nontrivi.0h1v.s3.7cfedc534631 from=translated src=- shape=a4efea94 vocab=f800b39e
-/
instance nontrivial_gamma0L2 (N : ℕ) [NeZero N] : Nontrivial (Gamma0L2 N) :=
  ⟨gamma0L2Const N, 0, gamma0L2Const_ne_zero N⟩

/--
@isnad1 id=not.0h0v.s6.9094a1918998 from=translated src=- shape=dd0d3c3d vocab=d3e1908f
-/
theorem gate_const_not_memLp_unrestricted :
    ¬ MemLp (fun _ : ℍ => (1 : ℂ)) 2 (volume : Measure ℍ) :=
  gate_const_not_memLp_of_infinite FLT.HyperbolicMeasure.volume_univ_eq_top

/--
@isnad1 id=le.0h0v.s5.2683a306d177 from=translated src=- shape=2df370ab vocab=d080dd22
-/
theorem gate_level_one_volume :
    volume (gammaFundamentalSet (Gamma0 1)) ≤ volume 𝒟 := by

  have hsub : ∀ q : SL(2, ℤ) ⧸ Gamma0 1,
      q = QuotientGroup.mk (1 : SL(2, ℤ)) := fun q => by
    induction q using QuotientGroup.induction_on with
    | _ a => exact (QuotientGroup.eq).mpr (Gamma0_mem.mpr (Subsingleton.elim _ _))
  have hcover : gammaFundamentalSet (Gamma0 1) ⊆
      (Quotient.out (QuotientGroup.mk (1 : SL(2, ℤ)) : SL(2, ℤ) ⧸ Gamma0 1))⁻¹ • 𝒟 := by
    refine Set.iUnion_subset fun q => ?_
    rw [hsub q]
  calc volume (gammaFundamentalSet (Gamma0 1))
      ≤ volume ((Quotient.out (QuotientGroup.mk (1 : SL(2, ℤ)) :
          SL(2, ℤ) ⧸ Gamma0 1))⁻¹ • 𝒟) := measure_mono hcover
    _ = volume 𝒟 := FLT.HyperbolicMeasure.volume_smul_sl2z _ _

end FLT.L2ProductionInstance

end
