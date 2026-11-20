/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.SchwartzLocalNormal
import Tengoku.Seed.Algebra.Module.ZLattice.Basic
import Tengoku.Seed.MeasureTheory.Constructions.Pi
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

namespace SRG266.Lattice

open MeasureTheory
open scoped FourierTransform RealInnerProductSpace

def standardCubeIoc (n : ℕ) : Set (Fin n → ℝ) :=
  {x | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}

/--
@isnad1 id=eventual.0h1v.s7.4d5380373c99 from=translated src=- shape=a1658440 vocab=c225fca9
-/
theorem standardCubeIoc_ae_eq_fundamentalDomain (n : ℕ) :
    standardCubeIoc n =ᵐ[volume]
      ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)) := by
  rw [ZSpan.fundamentalDomain_pi_basisFun]
  have hcube : standardCubeIoc n =
      Set.pi Set.univ (fun _ : Fin n => Set.Ioc (0 : ℝ) 1) := by
    ext x
    simp [standardCubeIoc]
  rw [hcube]
  exact Measure.pi_Ioc_ae_eq_pi_Icc.trans Measure.pi_Ico_ae_eq_pi_Icc.symm

/--
@isnad1 id=eq.0h1v.s6.930097b40606 from=translated src=- shape=529c28aa vocab=abd504d4
-/
@[simp]
theorem volume_standardCubeIoc (n : ℕ) :
    volume (standardCubeIoc n) = 1 := by
  have hcube : standardCubeIoc n =
      Set.pi Set.univ (fun _ : Fin n ↦ Set.Ioc (0 : ℝ) 1) := by
    ext x
    simp [standardCubeIoc]
  rw [hcube, Real.volume_pi_Ioc]
  simp

def closedUnitCubeEuclidean (n : ℕ) :
    Set (EuclideanSpace ℝ (Fin n)) :=
  {x | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1}

/--
@isnad1 id=iscompac.0h1v.s5.10cc9b43cc40 from=translated src=- shape=5a85d845 vocab=6f9b7074
-/
theorem isCompact_closedUnitCubeEuclidean (n : ℕ) :
    IsCompact (closedUnitCubeEuclidean n) := by
  have hcoord : IsCompact
      {x : Fin n → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} :=
    isCompact_pi_infinite fun _ ↦ isCompact_Icc
  have hpre :=
    (PiLp.homeomorph 2 (fun _ : Fin n ↦ ℝ)).isCompact_preimage.mpr hcoord
  convert hpre using 1
  ext x
  rfl

/--
@isnad1 id=eq.0h4v.s8.89aa4dc25c6c from=translated src=- shape=ff2bce54 vocab=fd481645
-/
theorem mFourier_add_int {n : ℕ} (a m : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier m
        (fun i ↦ (((a i : ℝ) + x i : ℝ) : UnitAddCircle)) =
      UnitAddTorus.mFourier m (fun i ↦ (x i : UnitAddCircle)) := by
  congr 1
  funext i
  simp

def intVectorEquivStandardIntegerAddSubgroup (n : ℕ) :
    (Fin n → ℤ) ≃ (standardIntegerLattice n).toAddSubgroup :=
  (intVectorEquivStandardIntegerLattice n).toEquiv.trans
    { toFun := fun v ↦ ⟨v, v.property⟩
      invFun := fun v ↦ ⟨v, v.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }

/--
@isnad1 id=eq.0h2v.s9.b7065b0238f3 from=translated src=- shape=b79cc4db vocab=50d44652
-/
@[simp]
theorem coe_intVectorEquivStandardIntegerAddSubgroup {n : ℕ} (z : Fin n → ℤ) :
    ((intVectorEquivStandardIntegerAddSubgroup n z :
      (standardIntegerLattice n).toAddSubgroup) : Fin n → ℝ) =
        fun i ↦ (z i : ℝ) := by
  exact coe_intVectorEquivStandardIntegerLattice z

/--
@isnad1 id=eq.0h3v.s8.342fbc1a501b from=translated src=- shape=76b188ee vocab=049d716f
-/
theorem mFourier_neg_eq_fourierChar_inner {n : ℕ}
    (m : Fin n → ℤ) (x : Fin n → ℝ) :
    UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) =
      (𝐞 (-inner ℝ (WithLp.toLp 2 x) (intVectorToReal m)) : Circle) := by
  rw [UnitAddTorus.mFourier]
  simp only [ContinuousMap.coe_mk, Pi.neg_apply, fourier_coe_apply,
    PiLp.inner_apply, intVectorToReal]
  rw [← Complex.exp_sum]
  congr 1
  push_cast
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← Finset.sum_neg_distrib]
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  push_cast
  ring

def coordinatePoissonKernel {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (m : Fin n → ℤ) :
    (Fin n → ℝ) → ℂ := fun x =>
  UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) •
    f (WithLp.toLp 2 x)

/--
@isnad1 id=continuo.0h3v.s6.471ea7211bce from=translated src=- shape=9607a290 vocab=570777d6
-/
theorem coordinatePoissonKernel_continuous {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (m : Fin n → ℤ) :
    Continuous (coordinatePoissonKernel f m) := by
  unfold coordinatePoissonKernel
  fun_prop

/--
@isnad1 id=integrab.1h3v.s8.5f2e4f825558 from=translated src=- shape=b1451339 vocab=da6fe3ff
-/
theorem coordinatePoissonKernel_integrable {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (hf : Integrable f)
    (m : Fin n → ℤ) :
    Integrable (coordinatePoissonKernel f m) := by
  have hfun : coordinatePoissonKernel f m =
      (fun y : EuclideanSpace ℝ (Fin n) =>
        𝐞 (-inner ℝ y (intVectorToReal m)) • f y) ∘ WithLp.toLp 2 := by
    funext x
    rw [coordinatePoissonKernel, Function.comp_apply,
      mFourier_neg_eq_fourierChar_inner]
    rfl
  rw [hfun]
  apply (PiLp.volume_preserving_toLp (Fin n)).integrable_comp_of_integrable
  exact (Real.fourierIntegral_convergent_iff (intVectorToReal m)).2 hf

/--
@isnad1 id=summable.1h3v.s10.240000a3d664 from=translated src=- shape=6801f463 vocab=3f2a4127
-/
theorem summable_cube_integral_norm_coordinatePoissonKernel {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (m : Fin n → ℤ) :
    Summable fun z : Fin n → ℤ ↦
      ∫ x : Fin n → ℝ in standardCubeIoc n,
        ‖coordinatePoissonKernel f m
          (((intVectorEquivStandardIntegerLattice n z :
            standardIntegerLattice n) : Fin n → ℝ) + x)‖ := by
  let K : TopologicalSpace.Compacts (EuclideanSpace ℝ (Fin n)) :=
    ⟨closedUnitCubeEuclidean n, isCompact_closedUnitCubeEuclidean n⟩
  have hsup : Summable fun z : Fin n → ℤ ↦
      ‖(integerTranslate f z).restrict K‖ := hf K
  refine Summable.of_nonneg_of_le (fun z ↦ integral_nonneg fun _ ↦ norm_nonneg _) (fun z ↦ ?_)
    hsup
  have hnonneg : 0 ≤
      ∫ x : Fin n → ℝ in standardCubeIoc n,
        ‖coordinatePoissonKernel f m
          (((intVectorEquivStandardIntegerLattice n z :
            standardIntegerLattice n) : Fin n → ℝ) + x)‖ :=
    integral_nonneg fun _ ↦ norm_nonneg _
  calc
    (∫ x : Fin n → ℝ in standardCubeIoc n,
        ‖coordinatePoissonKernel f m
          (((intVectorEquivStandardIntegerLattice n z :
            standardIntegerLattice n) : Fin n → ℝ) + x)‖) =
        ‖∫ x : Fin n → ℝ in standardCubeIoc n,
          ‖coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x)‖‖ :=
      (Real.norm_of_nonneg hnonneg).symm
    _ ≤ ‖(integerTranslate f z).restrict K‖ *
        volume.real (standardCubeIoc n) := by
      apply norm_setIntegral_le_of_norm_le_const
      · simp
      · intro x hx
        have hvec :
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x) =
              fun i ↦ (z i : ℝ) + x i := by
          funext i
          rw [coe_intVectorEquivStandardIntegerLattice]
          rfl
        rw [Real.norm_of_nonneg (norm_nonneg _), hvec,
          coordinatePoissonKernel, norm_smul, mFourier_add_int]
        have hphase :
            ‖UnitAddTorus.mFourier (-m) (fun i ↦ (x i : UnitAddCircle))‖ = 1 := by
          rw [mFourier_neg_eq_fourierChar_inner]
          exact Circle.norm_coe _
        rw [hphase, one_mul]
        have hxK : WithLp.toLp 2 x ∈ closedUnitCubeEuclidean n := by
          intro i
          exact ⟨le_of_lt (hx i).1, (hx i).2⟩
        have hbound := ContinuousMap.norm_coe_le_norm
          ((integerTranslate f z).restrict K) ⟨WithLp.toLp 2 x, hxK⟩
        change ‖f (WithLp.toLp 2 x + intVectorToReal z)‖ ≤
          ‖(integerTranslate f z).restrict K‖ at hbound
        calc
          ‖f (WithLp.toLp 2 fun i ↦ (z i : ℝ) + x i)‖ =
              ‖f (WithLp.toLp 2 x + intVectorToReal z)‖ := by
            congr 2
            ext i
            simp [intVectorToReal, add_comm]
          _ ≤ ‖(integerTranslate f z).restrict K‖ := hbound
    _ = ‖(integerTranslate f z).restrict K‖ := by
      simp [measureReal_def, volume_standardCubeIoc]

/--
@isnad1 id=eq.1h3v.s11.877b502a97fc from=translated src=- shape=de2bf5c6 vocab=a6007745
-/
theorem integral_coordinatePoissonKernel_eq_tsum_cube {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (hf : Integrable f)
    (m : Fin n → ℤ) :
    (∫ x : Fin n → ℝ, coordinatePoissonKernel f m x) =
      ∑' z : Fin n → ℤ,
        ∫ x : Fin n → ℝ in standardCubeIoc n,
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x) := by
  let : Countable (standardIntegerLattice n).toAddSubgroup := by
    change Countable (standardIntegerLattice n)
    infer_instance
  have hfd :=
    (ZSpan.isAddFundamentalDomain' (Pi.basisFun ℝ (Fin n)) volume).integral_eq_tsum''
      (coordinatePoissonKernel f m) (coordinatePoissonKernel_integrable f hf m)
  calc
    (∫ x : Fin n → ℝ, coordinatePoissonKernel f m x) =
        ∑' v : (standardIntegerLattice n).toAddSubgroup,
          ∫ x : Fin n → ℝ in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)),
          coordinatePoissonKernel f m (v + x) := by
      simpa only [AddSubgroup.vadd_def, vadd_eq_add] using hfd
    _ = ∑' z : Fin n → ℤ,
        ∫ x : Fin n → ℝ in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)),
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerAddSubgroup n z :
              (standardIntegerLattice n).toAddSubgroup) : Fin n → ℝ) + x) := by
      exact ((intVectorEquivStandardIntegerAddSubgroup n).tsum_eq
          (fun v : (standardIntegerLattice n).toAddSubgroup ↦
            ∫ x : Fin n → ℝ in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin n)),
              coordinatePoissonKernel f m (v + x))).symm
    _ = ∑' z : Fin n → ℤ,
        ∫ x : Fin n → ℝ in standardCubeIoc n,
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerAddSubgroup n z :
              (standardIntegerLattice n).toAddSubgroup) : Fin n → ℝ) + x) := by
      apply tsum_congr
      intro z
      apply setIntegral_congr_set
      exact (standardCubeIoc_ae_eq_fundamentalDomain n).symm
    _ = _ := by
      simp only [coe_intVectorEquivStandardIntegerAddSubgroup,
        coe_intVectorEquivStandardIntegerLattice]

/--
@isnad1 id=eq.1h3v.s11.721dae0085b8 from=translated src=- shape=f0178006 vocab=27058760
-/
theorem tsum_cube_integral_coordinatePoissonKernel {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (hf : LocallyNormallySummableIntegerTranslates f)
    (m : Fin n → ℤ) :
    (∑' z : Fin n → ℤ,
        ∫ x : Fin n → ℝ in standardCubeIoc n,
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x)) =
      ∫ x : Fin n → ℝ in standardCubeIoc n,
        ∑' z : Fin n → ℤ,
          coordinatePoissonKernel f m
            (((intVectorEquivStandardIntegerLattice n z :
              standardIntegerLattice n) : Fin n → ℝ) + x) := by
  apply MeasureTheory.integral_tsum_of_summable_integral_norm
  · intro z
    have hcont : Continuous fun x : Fin n → ℝ ↦
        coordinatePoissonKernel f m
          (((intVectorEquivStandardIntegerLattice n z :
            standardIntegerLattice n) : Fin n → ℝ) + x) := by
      exact (coordinatePoissonKernel_continuous f m).comp (by fun_prop)
    have hcompact : IsCompact
        {x : Fin n → ℝ | ∀ i, x i ∈ Set.Icc (0 : ℝ) 1} :=
      isCompact_pi_infinite fun _ ↦ isCompact_Icc
    apply (hcont.continuousOn.integrableOn_compact hcompact).mono_set
    intro x hx i
    exact ⟨le_of_lt (hx i).1, (hx i).2⟩
  · exact summable_cube_integral_norm_coordinatePoissonKernel f hf m

/--
@isnad1 id=eq.0h5v.s11.765f11c708fe from=translated src=- shape=76e6c299 vocab=9ab93920
-/
theorem coordinatePoissonKernel_add_int {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (m z : Fin n → ℤ) (x : Fin n → ℝ) :
    coordinatePoissonKernel f m
        (((intVectorEquivStandardIntegerLattice n z :
          standardIntegerLattice n) : Fin n → ℝ) + x) =
      UnitAddTorus.mFourier (-m) (fun i ↦ (x i : UnitAddCircle)) •
        f (WithLp.toLp 2 x + intVectorToReal z) := by
  have hvec :
      (((intVectorEquivStandardIntegerLattice n z :
        standardIntegerLattice n) : Fin n → ℝ) + x) =
        fun i ↦ (z i : ℝ) + x i := by
    funext i
    rw [coe_intVectorEquivStandardIntegerLattice]
    rfl
  rw [hvec, coordinatePoissonKernel, mFourier_add_int]
  congr 2
  ext i
  simp [intVectorToReal, add_comm]

/--
@isnad1 id=eq.0h4v.s11.87ac8e925484 from=translated src=- shape=a333c103 vocab=ffcb6bb3
-/
theorem tsum_coordinatePoissonKernel_add_int {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ))
    (m : Fin n → ℤ) (x : Fin n → ℝ) :
    (∑' z : Fin n → ℤ,
      coordinatePoissonKernel f m
        (((intVectorEquivStandardIntegerLattice n z :
          standardIntegerLattice n) : Fin n → ℝ) + x)) =
      UnitAddTorus.mFourier (-m) (fun i ↦ (x i : UnitAddCircle)) •
        ∑' z : Fin n → ℤ, f (WithLp.toLp 2 x + intVectorToReal z) := by
  rw [tsum_congr fun z ↦ coordinatePoissonKernel_add_int f m z x]
  exact tsum_const_smul'' _

/--
@isnad1 id=eq.0h3v.s9.f1b66350c83d from=translated src=- shape=947349dd vocab=21819c81
-/
theorem integral_mFourier_kernel_eq_fourier {n : ℕ}
    (f : C(EuclideanSpace ℝ (Fin n), ℂ)) (m : Fin n → ℤ) :
    (∫ x : Fin n → ℝ,
      UnitAddTorus.mFourier (-m) (fun i => (x i : UnitAddCircle)) •
        f (WithLp.toLp 2 x)) =
      𝓕 (f : EuclideanSpace ℝ (Fin n) → ℂ) (intVectorToReal m) := by
  rw [Real.fourier_eq]
  rw [← (PiLp.volume_preserving_toLp (Fin n)).integral_comp
    (MeasurableEquiv.toLp 2 _).measurableEmbedding]
  apply integral_congr_ae
  filter_upwards with x
  rw [mFourier_neg_eq_fourierChar_inner]
  rfl

end SRG266.Lattice
