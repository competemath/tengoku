import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_FundamentalDomainVolume
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_SiegelSetCover

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open Matrix Matrix.SpecialLinearGroup UpperHalfPlane ModularGroup CongruenceSubgroup
open MeasureTheory
open scoped Modular MatrixGroups Pointwise

namespace FLT.Gamma0FundamentalSet

def gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • 𝒟

/--
@isnad1 id=iff.0h2v.s9.9bde81507904 from=translated src=- shape=49abe58d vocab=b208bb20
-/
theorem mem_gammaFundamentalSet_iff {Γ : Subgroup SL(2, ℤ)} {z : ℍ} :
    z ∈ gammaFundamentalSet Γ ↔ ∃ q : SL(2, ℤ) ⧸ Γ, Quotient.out q • z ∈ 𝒟 := by
  simp only [gammaFundamentalSet, Set.mem_iUnion, Set.mem_inv_smul_set_iff]

/--
@isnad1 id=ex.0h2v.s8.08c98a93e3dd from=translated src=- shape=0658a61e vocab=d2c5f0a4
-/
theorem exists_smul_mem_gammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) (z : ℍ) :
    ∃ γ ∈ Γ, γ • z ∈ gammaFundamentalSet Γ :=
  FLT.SiegelSetCover.exists_smul_mem_iUnion_smul_fd Γ z

/--
@isnad1 id=eq.0h1v.s10.0b68b6511826 from=translated src=- shape=fbda888b vocab=5be84602
-/
theorem gammaFundamentalSet_eq_biUnion (Γ : Subgroup SL(2, ℤ)) [Finite (SL(2, ℤ) ⧸ Γ)] :
    haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
    gammaFundamentalSet Γ =
      ⋃ γ ∈ (Finset.univ.image fun q : SL(2, ℤ) ⧸ Γ => (Quotient.out q)⁻¹), γ • 𝒟 := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  ext z
  simp only [gammaFundamentalSet, Set.mem_iUnion, Finset.mem_image, Finset.mem_univ,
    true_and]
  exact ⟨fun ⟨q, hq⟩ => ⟨_, ⟨q, rfl⟩, hq⟩, fun ⟨γ, ⟨q, hq⟩, hz⟩ => ⟨q, hq ▸ hz⟩⟩

/--
@isnad1 id=lt.0h1v.s7.bb89fc6e4e33 from=translated src=- shape=8b6430c8 vocab=ae07a2a7
-/
theorem volume_gammaFundamentalSet_lt_top (Γ : Subgroup SL(2, ℤ))
    [Finite (SL(2, ℤ) ⧸ Γ)] : volume (gammaFundamentalSet Γ) < ⊤ := by
  haveI : Fintype (SL(2, ℤ) ⧸ Γ) := Fintype.ofFinite _
  rw [gammaFundamentalSet_eq_biUnion Γ]
  exact FLT.FundamentalDomainVolume.volume_biUnion_smul_fd_lt_top _

/--
@isnad1 id=lt.0h1v.s6.0623356b0f22 from=translated src=- shape=2c9226df vocab=43875448
-/
theorem volume_gammaFundamentalSet_pos (Γ : Subgroup SL(2, ℤ)) :
    0 < volume (gammaFundamentalSet Γ) := by
  refine lt_of_lt_of_le ?_
    (measure_mono (Set.subset_iUnion _ (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ)))
  rw [FLT.HyperbolicMeasure.volume_smul_sl2z]
  exact FLT.FundamentalDomainVolume.volume_fd_pos

/--
@isnad1 id=and.0h1v.s7.b8d052cc746f from=translated src=- shape=694f0c63 vocab=99cb60e7
-/
theorem volume_gammaFundamentalSet_ne_zero_ne_top (Γ : Subgroup SL(2, ℤ))
    [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) ≠ 0 ∧ volume (gammaFundamentalSet Γ) ≠ ⊤ :=
  ⟨(volume_gammaFundamentalSet_pos Γ).ne', (volume_gammaFundamentalSet_lt_top Γ).ne⟩

/--
@isnad1 id=lt.0h1v.s5.58bc1256f7bb from=translated src=- shape=1584ff9e vocab=432b6d29
-/
theorem volume_gamma0_lt_top (N : ℕ) [NeZero N] :
    volume (gammaFundamentalSet (Gamma0 N)) < ⊤ :=
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  volume_gammaFundamentalSet_lt_top (Gamma0 N)

/--
@isnad1 id=ex.0h2v.s8.429e74986492 from=translated src=- shape=c00583be vocab=1aa194bb
-/
theorem exists_gamma0_smul_mem (N : ℕ) (z : ℍ) :
    ∃ γ ∈ Gamma0 N, γ • z ∈ gammaFundamentalSet (Gamma0 N) :=
  exists_smul_mem_gammaFundamentalSet (Gamma0 N) z

def truncatedGammaFundamentalSet (Γ : Subgroup SL(2, ℤ)) (y : ℝ) : Set ℍ :=
  ⋃ q : SL(2, ℤ) ⧸ Γ, (Quotient.out q)⁻¹ • truncatedFundamentalDomain y

instance : ContinuousConstSMul SL(2, ℤ) ℍ where
  continuous_const_smul γ := by
    have h : (fun z : ℍ => γ • z) =
        fun z : ℍ => (Matrix.SpecialLinearGroup.mapGL ℝ γ) • z := by
      funext z
      exact MulAction.compHom_smul_def (Matrix.SpecialLinearGroup.mapGL ℝ) γ z
    rw [h]
    exact continuous_const_smul _

/--
@isnad1 id=iscompac.0h2v.s7.d01606359233 from=translated src=- shape=4e111fc2 vocab=43617d30
-/
theorem isCompact_smul_truncated (γ : SL(2, ℤ)) (y : ℝ) :
    IsCompact (γ • truncatedFundamentalDomain y) :=
  IsCompact.smul γ (isCompact_truncatedFundamentalDomain y)

/--
@isnad1 id=iscompac.0h2v.s7.8cd4f182a8a1 from=translated src=- shape=cb4b9dcb vocab=5cc9ac39
-/
theorem isCompact_truncatedGammaFundamentalSet (Γ : Subgroup SL(2, ℤ))
    [Finite (SL(2, ℤ) ⧸ Γ)] (y : ℝ) :
    IsCompact (truncatedGammaFundamentalSet Γ y) :=
  isCompact_iUnion fun q => isCompact_smul_truncated (Quotient.out q)⁻¹ y

/--
@isnad1 id=iscompac.0h2v.s4.4aab5231d1de from=translated src=- shape=275b4485 vocab=8034caa1
-/
theorem isCompact_truncatedGamma0 (N : ℕ) [NeZero N] (y : ℝ) :
    IsCompact (truncatedGammaFundamentalSet (Gamma0 N) y) :=
  haveI : Finite (SL(2, ℤ) ⧸ Gamma0 N) := FLT.SiegelSetCover.finite_quotient_gamma0 N
  isCompact_truncatedGammaFundamentalSet (Gamma0 N) y

/--
@isnad1 id=le.0h2v.s5.747078d1fc4d from=translated src=- shape=5e97977c vocab=0450abbd
-/
theorem truncatedGammaFundamentalSet_subset (Γ : Subgroup SL(2, ℤ)) (y : ℝ) :
    truncatedGammaFundamentalSet Γ y ⊆ gammaFundamentalSet Γ := by
  refine Set.iUnion_mono fun q => Set.smul_set_mono ?_
  exact fun z hz => hz.1

/--
@isnad1 id=lt.0h1v.s7.3e31d32c0000 from=translated src=- shape=c12829e5 vocab=07e14ea9
-/
theorem gate_volume_lt_volume_univ (Γ : Subgroup SL(2, ℤ)) [Finite (SL(2, ℤ) ⧸ Γ)] :
    volume (gammaFundamentalSet Γ) < volume (Set.univ : Set ℍ) := by
  rw [FLT.HyperbolicMeasure.volume_univ_eq_top]
  exact volume_gammaFundamentalSet_lt_top Γ

/--
@isnad1 id=eq.0h0v.s7.cf89950f9591 from=translated src=- shape=b21b7112 vocab=f3aa40dc
-/
theorem gate_volume_top_eq : volume (gammaFundamentalSet (⊤ : Subgroup SL(2, ℤ))) =
    volume 𝒟 := by
  haveI : Subsingleton (SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))) :=
    QuotientGroup.subsingleton_quotient_top
  have huniq : ∀ q : SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ)),
      q = (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))) := fun q =>
    Subsingleton.elim _ _
  have : gammaFundamentalSet (⊤ : Subgroup SL(2, ℤ)) =
      (Quotient.out (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ))))⁻¹ • 𝒟 := by
    refine Set.Subset.antisymm (Set.iUnion_subset fun q => ?_)
      (Set.subset_iUnion (fun q : SL(2, ℤ) ⧸ (⊤ : Subgroup SL(2, ℤ)) =>
        (Quotient.out q)⁻¹ • 𝒟) (QuotientGroup.mk 1))
    rw [huniq q]
  rw [this, FLT.HyperbolicMeasure.volume_smul_sl2z]

/--
@isnad1 id=nonempty.0h1v.s5.1c813fc02f2c from=translated src=- shape=9a7c7d47 vocab=e8374662
-/
theorem gate_truncated_nonempty (Γ : Subgroup SL(2, ℤ)) :
    (truncatedGammaFundamentalSet Γ 2).Nonempty := by
  refine ⟨(Quotient.out (QuotientGroup.mk 1 : SL(2, ℤ) ⧸ Γ))⁻¹ • UpperHalfPlane.ρ,
    Set.mem_iUnion.mpr ⟨QuotientGroup.mk 1, Set.smul_mem_smul_set ?_⟩⟩
  refine ⟨FLT.SiegelSetCover.gate_rho_mem_fd, ?_⟩
  rw [FLT.SiegelSetCover.gate_im_rho]
  nlinarith [Real.sq_sqrt (by norm_num : (3 : ℝ) ≥ 0),
    Real.sqrt_nonneg (3 : ℝ)]

end FLT.Gamma0FundamentalSet
