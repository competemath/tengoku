import Tengoku.OpenaiMath.OAI.Analysis.C0Absorption.Tags

namespace OAI

open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty
open NormedSpace

namespace C0Absorption
noncomputable section
open Set Filter Topology
open scoped NNReal BigOperators ZeroAtInfty

section GeneralC0
variable {A B : Type*} [TopologicalSpace A] [TopologicalSpace B]
  [DiscreteTopology A] [DiscreteTopology B]

def cfunOfTendsto (f : A → ℝ) (hf : Tendsto f cofinite (nhds 0)) : C₀(A,ℝ) where
  toFun := f
  continuous_toFun := continuous_of_discreteTopology
  zero_at_infty' := by simpa only [cocompact_eq_cofinite] using hf

/--
@isnad1 id=tendsto.0h2v.s6.a09f519a2e3a from=translated src=- shape=8f5a3719 vocab=ea6b3c06
-/
theorem cfun_tendsto (f : C₀(A,ℝ)) : Tendsto f cofinite (nhds 0) := by
  simpa only [cocompact_eq_cofinite] using zero_at_infty f

/--
@isnad1 id=le.0h3v.s6.1ea972ac29f9 from=translated src=- shape=6bce0e98 vocab=51c1b09a
-/
theorem cfun_norm_apply_le {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (f : C₀(A,ℝ)) (a : A) : |f a|≤‖f‖ := f.toBCF.norm_coe_le_norm a

/--
@isnad1 id=le.2h3v.s6.d46fe29b262e from=translated src=- shape=12a914c9 vocab=51c1b09a
-/
theorem cfun_norm_le {A : Type*} [TopologicalSpace A] [DiscreteTopology A]
    (f : C₀(A,ℝ)) {r : ℝ} (hr : 0≤r) (h : ∀ a,|f a|≤r) : ‖f‖≤r :=
  (f.toBCF.norm_le hr).mpr h

def cfunPull (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) : C₀(A,ℝ) :=
  cfunOfTendsto (fun a => f (j a)) ((cfun_tendsto f).comp hj)

/--
@isnad1 id=eq.1h5v.s6.8918d10d99d5 from=translated src=- shape=46643904 vocab=16a363af
-/
@[simp] theorem cfunPull_apply (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) (a : A) :
    cfunPull j hj f a=f (j a) := rfl

def cfunPullL (j : A → B) (hj : Tendsto j cofinite cofinite) : C₀(B,ℝ) →L[ℝ] C₀(A,ℝ) :=
  LinearMap.mkContinuous
    { toFun := cfunPull j hj
      map_add' := by intro f g; ext a; rfl
      map_smul' := by intro c f; ext a; rfl } 1 (fun f => by
        change ‖cfunPull j hj f‖≤1*‖f‖
        rw [one_mul]
        exact cfun_norm_le _ (norm_nonneg _) (fun a => cfun_norm_apply_le f (j a)))

/--
@isnad1 id=eq.1h5v.s8.ebb26285400a from=translated src=- shape=ab743770 vocab=327151a6
-/
@[simp] theorem cfunPullL_apply (j : A → B) (hj : Tendsto j cofinite cofinite) (f : C₀(B,ℝ)) (a : A) :
    cfunPullL j hj f a=f (j a) := rfl

end GeneralC0

/--
@isnad1 id=tendsto.2h6v.s5.db331e3d18d0 from=translated src=- shape=2fa65d6d vocab=28b39447
-/
theorem tendsto_sumElim_cofinite {A B : Type*} {X : Type*} (f : A → X) (g : B → X)
    (l : Filter X) (hf : Tendsto f cofinite l) (hg : Tendsto g cofinite l) :
    Tendsto (Sum.elim f g) cofinite l := by
  intro s hs
  have h1 : {a | f a∉s}.Finite := hf hs
  have h2 : {b | g b∉s}.Finite := hg hs
  apply ((h1.image Sum.inl).union (h2.image Sum.inr)).subset
  intro x hx
  cases x with
  | inl a => exact Or.inl ⟨a,hx,rfl⟩
  | inr b => exact Or.inr ⟨b,hx,rfl⟩

abbrev BlockC0 := C₀(Label,ℝ)

def inputRows : C0 →L[ℝ] C0 := cfunPullL rowIndex rowIndex_injective.tendsto_cofinite

def inputBlocks : C0 →L[ℝ] BlockC0 := cfunPullL labelIndex labelIndex_injective.tendsto_cofinite

/--
@isnad1 id=eq.0h2v.s7.c97f843a307e from=translated src=- shape=4c5ef393 vocab=131c3155
-/
@[simp] theorem inputRows_apply (x : C0) (i : ℕ) : inputRows x i=x (rowIndex i) := rfl
/--
@isnad1 id=eq.0h2v.s7.f570210d9390 from=translated src=- shape=2b80fc23 vocab=749b231d
-/
@[simp] theorem inputBlocks_apply (x : C0) (γ : Label) : inputBlocks x γ=x (labelIndex γ) := rfl

def joinInputs (x : C0 × BlockC0) : C0 :=
  cfunOfTendsto (fun k => Sum.elim x.1 x.2 (coordinateEnumeration.symm k))
    ((tendsto_sumElim_cofinite x.1 x.2 (nhds 0) (cfun_tendsto x.1) (cfun_tendsto x.2)).comp
      coordinateEnumeration.symm.injective.tendsto_cofinite)

/--
@isnad1 id=eq.0h2v.s5.6987efe4a9cb from=translated src=- shape=1d7b3fef vocab=f2bcbbe0
-/
@[simp] theorem joinInputs_row (x : C0 × BlockC0) (i : ℕ) : joinInputs x (rowIndex i)=x.1 i := by
  change Sum.elim x.1 x.2 (coordinateEnumeration.symm (coordinateEnumeration (Sum.inl i)))=x.1 i
  rw [Equiv.symm_apply_apply]
  rfl

/--
@isnad1 id=eq.0h2v.s5.dfce07641faf from=translated src=- shape=da67f8c6 vocab=2dde374c
-/
@[simp] theorem joinInputs_block (x : C0 × BlockC0) (γ : Label) : joinInputs x (labelIndex γ)=x.2 γ := by
  change Sum.elim x.1 x.2 (coordinateEnumeration.symm (coordinateEnumeration (Sum.inr γ)))=x.2 γ
  rw [Equiv.symm_apply_apply]
  rfl

/--
@isnad1 id=eq.0h1v.s8.c78b0d130746 from=translated src=- shape=cb5888c2 vocab=38759509
-/
theorem joinInputs_split (x : C0) : joinInputs (inputRows x,inputBlocks x)=x := by
  ext k
  obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
  cases a with
  | inl i => exact joinInputs_row _ i
  | inr γ => exact joinInputs_block _ γ

/--
@isnad1 id=eq.0h1v.s5.74f1ebf5d219 from=translated src=- shape=ba142651 vocab=20896d0f
-/
theorem joinInputs_norm (x : C0 × BlockC0) : ‖joinInputs x‖=‖x‖ := by
  apply le_antisymm
  · apply cfun_norm_le _ (norm_nonneg x)
    intro k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => exact (show |joinInputs x (rowIndex i)|≤‖x.1‖ by rw [joinInputs_row]; exact cfun_norm_apply_le _ _).trans (le_max_left _ _)
    | inr γ => exact (show |joinInputs x (labelIndex γ)|≤‖x.2‖ by rw [joinInputs_block]; exact cfun_norm_apply_le _ _).trans (le_max_right _ _)
  · rw [Prod.norm_def]
    apply max_le
    · apply cfun_norm_le _ (norm_nonneg _)
      intro i
      rw [← joinInputs_row x i]
      exact cfun_norm_apply_le _ _
    · apply cfun_norm_le _ (norm_nonneg _)
      intro γ
      rw [← joinInputs_block x γ]
      exact cfun_norm_apply_le _ _

def inputCoordinates : (C0 × BlockC0) ≃ₗᵢ[ℝ] C0 where
  toFun := joinInputs
  invFun := fun x => (inputRows x,inputBlocks x)
  left_inv := by
    intro x
    apply Prod.ext <;> ext k
    · exact joinInputs_row x k
    · exact joinInputs_block x k
  right_inv := joinInputs_split
  map_add' := by
    intro x y
    ext k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => simp only [show coordinateEnumeration (Sum.inl i)=rowIndex i from rfl,joinInputs_row,Prod.fst_add,ZeroAtInftyContinuousMap.add_apply]
    | inr γ => simp only [show coordinateEnumeration (Sum.inr γ)=labelIndex γ from rfl,joinInputs_block,Prod.snd_add,ZeroAtInftyContinuousMap.add_apply]
  map_smul' := by
    intro c x
    ext k
    obtain ⟨a,rfl⟩ := coordinateEnumeration.surjective k
    cases a with
    | inl i => simp only [show coordinateEnumeration (Sum.inl i)=rowIndex i from rfl,joinInputs_row,ZeroAtInftyContinuousMap.smul_apply]; rfl
    | inr γ => simp only [show coordinateEnumeration (Sum.inr γ)=labelIndex γ from rfl,joinInputs_block,ZeroAtInftyContinuousMap.smul_apply]; rfl
  norm_map' := joinInputs_norm

/--
@isnad1 id=tendsto.0h0v.s3.b7d1c5a8f87c from=translated src=- shape=57d238ad vocab=b94c9c91
-/
theorem labelLevel_tendsto : Tendsto Label.level cofinite cofinite :=
  Filter.Tendsto.cofinite_of_finite_preimage_singleton (fun lev => labels_at_level_finite lev)

/--
@isnad1 id=tendsto.0h1v.s4.32ceca2ddad6 from=translated src=- shape=1af2c31d vocab=f6ed2951
-/
theorem labelRadius_tendsto (x : C0) : Tendsto (fun γ : Label => localRadius γ.level x) cofinite (nhds 0) :=
  (localRadius_tendsto x).comp labelLevel_tendsto

/--
@isnad1 id=tendsto.0h2v.s7.0a248fdc77c1 from=translated src=- shape=bdc9e20f vocab=1b21cd80
-/
theorem frozenCorrection_tendsto (W : FrozenWeights) (x : C0) :
    Tendsto (fun γ => frozenCorrection W γ x) cofinite (nhds 0) := by
  apply squeeze_zero_norm (fun γ => frozenCorrection_local W γ x) _
  simpa only [mul_zero] using (labelRadius_tendsto x).const_mul 4

def frozenCorrectionC0 (W : FrozenWeights) (x : C0) : BlockC0 :=
  cfunOfTendsto (fun γ => frozenCorrection W γ x) (frozenCorrection_tendsto W x)

def frozenCorrectionL (W : FrozenWeights) : C0 →L[ℝ] BlockC0 :=
  LinearMap.mkContinuous
    { toFun := frozenCorrectionC0 W
      map_add' := by intro x y; ext γ; exact map_add (frozenCorrection W γ) x y
      map_smul' := by intro c x; ext γ; exact map_smul (frozenCorrection W γ) c x }
    4 (fun x => by
      change ‖frozenCorrectionC0 W x‖≤4*‖x‖
      exact cfun_norm_le _ (mul_nonneg (by norm_num) (norm_nonneg _)) (fun γ => frozenCorrection_bound W γ x))

/--
@isnad1 id=eq.0h3v.s8.5ac169320c9a from=translated src=- shape=92a03cd9 vocab=ce35588f
-/
@[simp] theorem frozenCorrectionL_apply (W : FrozenWeights) (x : C0) (γ : Label) :
    frozenCorrectionL W x γ=frozenCorrection W γ x := rfl

def correctionC0 (s : C0Ball) : BlockC0 := frozenCorrectionL (stateWeights s) s.val

/--
@isnad1 id=eq.0h2v.s4.cd71d571e27b from=translated src=- shape=e19f1adf vocab=ccd46322
-/
@[simp] theorem correctionC0_apply (s : C0Ball) (γ : Label) : correctionC0 s γ=correction γ s := rfl

end
end C0Absorption

end OAI
