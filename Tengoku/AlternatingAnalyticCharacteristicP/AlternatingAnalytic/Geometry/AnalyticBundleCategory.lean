import Tengoku.Seed.Geometry.Manifold.VectorBundle.ContMDiffSection
import Tengoku.Seed.Geometry.Manifold.VectorBundle.Hom
import Tengoku.Seed.CategoryTheory.Iso
import Tengoku.Seed.Geometry.Manifold.ContMDiff.NormedSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The category of analytic vector bundles

Over a fixed base manifold, `AnalyticBundleCat I M` has as objects analytic vector
bundles with a normed model fiber (the fibers themselves are topological vector
spaces), and as morphisms analytic sections of the Hom bundle. This is the category
on which Corollary 4.6 builds the alternating bifunctor. Morphisms are characterized
by analyticity of their operator coordinates (`exists_hom_iff_operatorAnalytic`).
-/

noncomputable section

open Bundle Set CategoryTheory
open scoped Bundle Manifold ContDiff Topology

universe u

namespace AlternatingAnalytic

section OperatorCoordinates

variable {K P M G : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]
  [NormedAddCommGroup G] [NormedSpace K G]
  [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]

/-- A map into a normed space is analytic on an open set iff it is analytic in every
chart.-/
theorem contMDiffOn_iff_analyticOnNhd_extChartAt {U : Set M} (hU : IsOpen U)
    {γ : M → G} :
    ContMDiffOn 𝓘(K, P) 𝓘(K, G) ω γ U ↔
      ∀ x : M, AnalyticOnNhd K (γ ∘ (extChartAt 𝓘(K, P) x).symm)
        ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) := by
  have hV (x : M) : IsOpen ((extChartAt 𝓘(K, P) x).target ∩
      (extChartAt 𝓘(K, P) x).symm ⁻¹' U) :=
    (continuousOn_extChartAt_symm x).isOpen_inter_preimage
      (isOpen_extChartAt_target x) hU
  constructor
  · intro hγ x
    have hγc : ContDiffOn K ω (γ ∘ (extChartAt 𝓘(K, P) x).symm)
        ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) := by
      simpa [chartAt_self_eq, mfld_simps] using (contMDiffOn_iff.mp hγ).2 x 0
    exact (hV x).analyticOn_iff_analyticOnNhd.mp
      ((contDiffOn_omega_iff_analyticOn (hV x).uniqueDiffOn).mp hγc)
  · intro hγ x hx
    have hxV : extChartAt 𝓘(K, P) x x ∈
        (extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U := by
      simpa only [mfld_simps] using hx
    have hc : ContMDiffOn 𝓘(K, P) 𝓘(K, G) ω
        (γ ∘ (extChartAt 𝓘(K, P) x).symm)
        ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) :=
      contMDiffOn_iff_contDiffOn.mpr ((hγ x).contDiffOn (hV x).uniqueDiffOn)
    apply ContMDiffAt.contMDiffWithinAt
    apply contMDiffAt_iff_source.mpr
    exact (hc.contMDiffAt ((hV x).mem_nhds hxV)).contMDiffWithinAt

variable {F₁ F₂ : Type*} {E₁ E₂ : M → Type*}
  [NormedAddCommGroup F₁] [NormedSpace K F₁]
  [NormedAddCommGroup F₂] [NormedSpace K F₂]
  [∀ b, AddCommGroup (E₁ b)] [∀ b, Module K (E₁ b)]
  [∀ b, TopologicalSpace (E₁ b)]
  [∀ b, AddCommGroup (E₂ b)] [∀ b, Module K (E₂ b)]
  [∀ b, TopologicalSpace (E₂ b)]
  [∀ b, IsTopologicalAddGroup (E₂ b)] [∀ b, ContinuousSMul K (E₂ b)]
  [TopologicalSpace (TotalSpace F₁ E₁)] [TopologicalSpace (TotalSpace F₂ E₂)]
  [FiberBundle F₁ E₁] [VectorBundle K F₁ E₁]
  [FiberBundle F₂ E₂] [VectorBundle K F₂ E₂]
  [ContMDiffVectorBundle ω F₁ E₁ 𝓘(K, P)]
  [ContMDiffVectorBundle ω F₂ E₂ 𝓘(K, P)]

/-- On an open subset of a common trivialization domain, a Hom section is analytic iff
its operator coordinates are analytic in every chart.-/
theorem contMDiffOn_hom_section_iff_analyticOnNhd
    (e₁ : Trivialization F₁ (π F₁ E₁)) (e₂ : Trivialization F₂ (π F₂ E₂))
    [MemTrivializationAtlas e₁] [MemTrivializationAtlas e₂]
    {U : Set M} (hU : IsOpen U) (hUe : U ⊆ e₁.baseSet ∩ e₂.baseSet)
    (f : ∀ b, E₁ b →L[K] E₂ b) :
    ContMDiffOn 𝓘(K, P) (𝓘(K, P).prod 𝓘(K, F₁ →L[K] F₂)) ω
      (fun b => TotalSpace.mk' (F₁ →L[K] F₂) b (f b)) U ↔
    ∀ x : M, AnalyticOnNhd K
      ((fun b => (e₂.continuousLinearMapAt K b).comp ((f b).comp (e₁.symmL K b))) ∘
        (extChartAt 𝓘(K, P) x).symm)
      ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹' U) := by
  rw [(e₁.continuousLinearMap (RingHom.id K) e₂).contMDiffOn_section_iff hU hUe]
  exact contMDiffOn_iff_analyticOnNhd_extChartAt hU

/-- A fiberwise operator family is an analytic Hom section iff its coordinates in the
chosen trivializations are analytic in every chart.-/
theorem contMDiff_hom_section_iff_analyticOnNhd
    (f : ∀ b, E₁ b →L[K] E₂ b) :
    ContMDiff 𝓘(K, P) (𝓘(K, P).prod 𝓘(K, F₁ →L[K] F₂)) ω
      (fun b => TotalSpace.mk' (F₁ →L[K] F₂) b (f b)) ↔
    ∀ z x : M, AnalyticOnNhd K
      ((fun b => ContinuousLinearMap.inCoordinates F₁ E₁ F₂ E₂ z b z b (f b)) ∘
        (extChartAt 𝓘(K, P) x).symm)
      ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹'
        ((trivializationAt F₁ E₁ z).baseSet ∩ (trivializationAt F₂ E₂ z).baseSet)) := by
  have hU (z : M) : IsOpen
      ((trivializationAt F₁ E₁ z).baseSet ∩ (trivializationAt F₂ E₂ z).baseSet) :=
    (trivializationAt F₁ E₁ z).open_baseSet.inter
      (trivializationAt F₂ E₂ z).open_baseSet
  constructor
  · intro hf z
    exact (contMDiffOn_hom_section_iff_analyticOnNhd
      (trivializationAt F₁ E₁ z) (trivializationAt F₂ E₂ z)
      (hU z) subset_rfl f).mp hf.contMDiffOn
  · intro hf z
    have hc := (contMDiffOn_hom_section_iff_analyticOnNhd
      (trivializationAt F₁ E₁ z) (trivializationAt F₂ E₂ z)
      (hU z) subset_rfl f).mpr (hf z)
    exact hc.contMDiffAt ((hU z).mem_nhds
      ⟨mem_baseSet_trivializationAt F₁ E₁ z, mem_baseSet_trivializationAt F₂ E₂ z⟩)

end OperatorCoordinates

variable {K P H : Type u} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P] [TopologicalSpace H]
  (I : ModelWithCorners K P H) (M : Type u) [TopologicalSpace M] [ChartedSpace H M]

/-- An analytic vector bundle over `M` with its atlas. Only the model fiber carries a
norm; the fibers are topological vector spaces.-/
structure AnalyticBundleCat : Type (u + 1) where
  /-- The normed model of the fibers.-/
  Model : Type u
  [modelNormedAddCommGroup : NormedAddCommGroup Model]
  [modelNormedSpace : NormedSpace K Model]
  /-- The fibers.-/
  Fiber : M → Type u
  [fiberAddCommGroup : ∀ b, AddCommGroup (Fiber b)]
  [fiberModule : ∀ b, Module K (Fiber b)]
  [fiberTopology : ∀ b, TopologicalSpace (Fiber b)]
  [fiberTopologicalAddGroup : ∀ b, IsTopologicalAddGroup (Fiber b)]
  [fiberContinuousSMul : ∀ b, ContinuousSMul K (Fiber b)]
  [totalSpaceTopology : TopologicalSpace (TotalSpace Model Fiber)]
  [fiberBundle : FiberBundle Model Fiber]
  [vectorBundle : VectorBundle K Model Fiber]
  [analyticVectorBundle : ContMDiffVectorBundle ω Model Fiber I]

attribute [instance] AnalyticBundleCat.modelNormedAddCommGroup
  AnalyticBundleCat.modelNormedSpace AnalyticBundleCat.fiberAddCommGroup
  AnalyticBundleCat.fiberModule AnalyticBundleCat.fiberTopology
  AnalyticBundleCat.fiberTopologicalAddGroup AnalyticBundleCat.fiberContinuousSMul
  AnalyticBundleCat.totalSpaceTopology AnalyticBundleCat.fiberBundle
  AnalyticBundleCat.vectorBundle AnalyticBundleCat.analyticVectorBundle

namespace AnalyticBundleCat

/-- The object of `AnalyticBundleCat` given by an analytic vector bundle.-/
abbrev of (F : Type u) [NormedAddCommGroup F] [NormedSpace K F]
    (E : M → Type u) [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
    [∀ b, TopologicalSpace (E b)] [∀ b, IsTopologicalAddGroup (E b)]
    [∀ b, ContinuousSMul K (E b)] [TopologicalSpace (TotalSpace F E)]
    [FiberBundle F E] [VectorBundle K F E] [ContMDiffVectorBundle ω F E I] :
    AnalyticBundleCat I M := ⟨F, E⟩

variable {I M}

/-- Morphisms are analytic sections of the Hom bundle.-/
abbrev Hom (X Y : AnalyticBundleCat I M) : Type u :=
  ContMDiffSection I (X.Model →L[K] Y.Model) ω (fun b ↦ X.Fiber b →L[K] Y.Fiber b)

variable {X Y Z : AnalyticBundleCat I M}

/-- In a single trivialization, the identity has coordinates the identity.-/
theorem inCoordinates_id (X : AnalyticBundleCat I M) {a b : M}
    (hb : b ∈ (trivializationAt X.Model X.Fiber a).baseSet) :
    ContinuousLinearMap.inCoordinates X.Model X.Fiber X.Model X.Fiber a b a b
        (ContinuousLinearMap.id K (X.Fiber b)) = ContinuousLinearMap.id K X.Model := by
  rw [ContinuousLinearMap.inCoordinates_eq hb hb]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

/-- On the common domain of three trivializations, coordinates respect composition.-/
theorem inCoordinates_comp {a b : M}
    (hX : b ∈ (trivializationAt X.Model X.Fiber a).baseSet)
    (hY : b ∈ (trivializationAt Y.Model Y.Fiber a).baseSet)
    (hZ : b ∈ (trivializationAt Z.Model Z.Fiber a).baseSet)
    (f : X.Fiber b →L[K] Y.Fiber b) (g : Y.Fiber b →L[K] Z.Fiber b) :
    ContinuousLinearMap.inCoordinates X.Model X.Fiber Z.Model Z.Fiber a b a b (g.comp f) =
      (ContinuousLinearMap.inCoordinates Y.Model Y.Fiber Z.Model Z.Fiber a b a b g).comp
        (ContinuousLinearMap.inCoordinates X.Model X.Fiber Y.Model Y.Fiber a b a b f) := by
  rw [ContinuousLinearMap.inCoordinates_eq hX hZ,
    ContinuousLinearMap.inCoordinates_eq hY hZ,
    ContinuousLinearMap.inCoordinates_eq hX hY]
  ext v
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
    ContinuousLinearEquiv.symm_apply_apply]

/-- The identity morphism.-/
def id (X : AnalyticBundleCat I M) : Hom X X where
  toFun b := ContinuousLinearMap.id K (X.Fiber b)
  contMDiff_toFun := by
    intro a
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    apply (contMDiffAt_const (c := ContinuousLinearMap.id K X.Model)).congr_of_eventuallyEq
    filter_upwards [(trivializationAt X.Model X.Fiber a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt X.Model X.Fiber a)] with b hb
    exact inCoordinates_id X hb

/-- Composition of morphisms, fiber by fiber.-/
def comp (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  toFun b := (g b).comp (f b)
  contMDiff_toFun := by
    intro a
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    have hf := ((contMDiffAt_hom_bundle _).mp (f.contMDiff a)).2
    have hg := ((contMDiffAt_hom_bundle _).mp (g.contMDiff a)).2
    apply (hg.clm_comp hf).congr_of_eventuallyEq
    filter_upwards [(trivializationAt X.Model X.Fiber a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt X.Model X.Fiber a),
      (trivializationAt Y.Model Y.Fiber a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt Y.Model Y.Fiber a),
      (trivializationAt Z.Model Z.Fiber a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt Z.Model Z.Fiber a)] with b hX hY hZ
    exact inCoordinates_comp hX hY hZ (f b) (g b)

/-- Objects live in `Type (u + 1)` and morphisms in `Type u`.-/
instance category : Category.{u} (AnalyticBundleCat I M) where
  Hom := Hom
  id := id
  comp := comp
  id_comp f := ContMDiffSection.ext fun b ↦ ContinuousLinearMap.comp_id (f b)
  comp_id f := ContMDiffSection.ext fun b ↦ ContinuousLinearMap.id_comp (f b)
  assoc f g h := ContMDiffSection.ext fun b ↦
    (ContinuousLinearMap.comp_assoc (h b) (g b) (f b)).symm

instance homDFunLike : DFunLike (X ⟶ Y) M (fun b ↦ X.Fiber b →L[K] Y.Fiber b) :=
  inferInstanceAs (DFunLike (Hom X Y) M (fun b ↦ X.Fiber b →L[K] Y.Fiber b))

/-- Morphisms are equal when their fiber operators are equal.-/
@[ext]
theorem hom_ext {f g : X ⟶ Y} (h : ∀ b, f b = g b) : f = g :=
  ContMDiffSection.ext h

@[simp]
theorem id_apply (X : AnalyticBundleCat I M) (b : M) :
    (𝟙 X : X ⟶ X) b = ContinuousLinearMap.id K (X.Fiber b) := rfl

@[simp]
theorem comp_apply (f : X ⟶ Y) (g : Y ⟶ Z) (b : M) :
    (f ≫ g) b = (g b).comp (f b) := rfl

/-- A morphism from a fiberwise family whose coordinates are analytic near each point.-/
def homOfCoordinates (f : ∀ b, X.Fiber b →L[K] Y.Fiber b)
    (hf : ∀ a, ContMDiffAt I 𝓘(K, X.Model →L[K] Y.Model) ω
      (fun b ↦ ContinuousLinearMap.inCoordinates X.Model X.Fiber Y.Model Y.Fiber
        a b a b (f b)) a) : X ⟶ Y :=
  ⟨f, fun a ↦ (contMDiffAt_hom_bundle _).mpr ⟨contMDiffAt_id, hf a⟩⟩

@[simp]
theorem homOfCoordinates_apply (f : ∀ b, X.Fiber b →L[K] Y.Fiber b)
    (hf : ∀ a, ContMDiffAt I 𝓘(K, X.Model →L[K] Y.Model) ω
      (fun b ↦ ContinuousLinearMap.inCoordinates X.Model X.Fiber Y.Model Y.Fiber
        a b a b (f b)) a) (b : M) : homOfCoordinates f hf b = f b := rfl

/-- Fiberwise equivalences that are analytic sections in both directions give an
isomorphism.-/
def isoOfFiberwiseContinuousLinearEquiv (e : ∀ b, X.Fiber b ≃L[K] Y.Fiber b)
    (he : ContMDiff I (I.prod 𝓘(K, X.Model →L[K] Y.Model)) ω
      (fun b ↦ TotalSpace.mk' (X.Model →L[K] Y.Model) b (e b).toContinuousLinearMap))
    (he_symm : ContMDiff I (I.prod 𝓘(K, Y.Model →L[K] X.Model)) ω
      (fun b ↦ TotalSpace.mk' (Y.Model →L[K] X.Model) b
        (e b).symm.toContinuousLinearMap)) : X ≅ Y where
  hom := ⟨fun b ↦ (e b).toContinuousLinearMap, he⟩
  inv := ⟨fun b ↦ (e b).symm.toContinuousLinearMap, he_symm⟩
  hom_inv_id := by
    apply hom_ext
    intro b
    ext v
    exact (e b).symm_apply_apply v
  inv_hom_id := by
    apply hom_ext
    intro b
    ext v
    exact (e b).apply_symm_apply v

@[simp]
theorem isoOfFiberwiseContinuousLinearEquiv_hom_apply
    (e : ∀ b, X.Fiber b ≃L[K] Y.Fiber b) (he he_symm) (b : M) :
    (isoOfFiberwiseContinuousLinearEquiv e he he_symm).hom b =
      (e b).toContinuousLinearMap := rfl

@[simp]
theorem isoOfFiberwiseContinuousLinearEquiv_inv_apply
    (e : ∀ b, X.Fiber b ≃L[K] Y.Fiber b) (he he_symm) (b : M) :
    (isoOfFiberwiseContinuousLinearEquiv e he he_symm).inv b =
      (e b).symm.toContinuousLinearMap := rfl

end AnalyticBundleCat
end AlternatingAnalytic

namespace AlternatingAnalytic.AnalyticBundleCat

variable {K P M : Type u} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P]
  [TopologicalSpace M] [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
  {X Y : AnalyticBundleCat 𝓘(K, P) M}

/-- A fiberwise operator family is operator analytic if its coordinates, as
operator-valued maps, are analytic in every chart and trivialization.-/
def OperatorAnalytic (f : ∀ b, X.Fiber b →L[K] Y.Fiber b) : Prop :=
  ∀ z x : M, AnalyticOnNhd K
    ((fun b ↦ ContinuousLinearMap.inCoordinates X.Model X.Fiber Y.Model Y.Fiber
      z b z b (f b)) ∘ (extChartAt 𝓘(K, P) x).symm)
    ((extChartAt 𝓘(K, P) x).target ∩ (extChartAt 𝓘(K, P) x).symm ⁻¹'
      ((trivializationAt X.Model X.Fiber z).baseSet ∩
        (trivializationAt Y.Model Y.Fiber z).baseSet))

/-- A fiberwise family is operator analytic iff it is an analytic Hom section.-/
theorem operatorAnalytic_iff_contMDiff (f : ∀ b, X.Fiber b →L[K] Y.Fiber b) :
    OperatorAnalytic (X := X) (Y := Y) f ↔
      ContMDiff 𝓘(K, P) (𝓘(K, P).prod 𝓘(K, X.Model →L[K] Y.Model)) ω
        (fun b ↦ TotalSpace.mk' (X.Model →L[K] Y.Model) b (f b)) :=
  (contMDiff_hom_section_iff_analyticOnNhd f).symm

/-- Every morphism is operator analytic.-/
theorem hom_operatorAnalytic (f : X ⟶ Y) :
    OperatorAnalytic (X := X) (Y := Y) (fun b ↦ f b) :=
  (operatorAnalytic_iff_contMDiff _).mpr (ContMDiffSection.contMDiff f)

/-- The morphism given by an operator-analytic fiberwise family.-/
def homOfOperatorAnalytic (f : ∀ b, X.Fiber b →L[K] Y.Fiber b)
    (hf : OperatorAnalytic (X := X) (Y := Y) f) : X ⟶ Y :=
  ⟨f, (operatorAnalytic_iff_contMDiff f).mp hf⟩

@[simp]
theorem homOfOperatorAnalytic_apply (f : ∀ b, X.Fiber b →L[K] Y.Fiber b)
    (hf : OperatorAnalytic (X := X) (Y := Y) f) (b : M) :
    homOfOperatorAnalytic f hf b = f b := rfl

/-- The morphisms are the operator-analytic families.-/
theorem exists_hom_iff_operatorAnalytic (f : ∀ b, X.Fiber b →L[K] Y.Fiber b) :
    (∃ g : X ⟶ Y, (fun b ↦ g b) = f) ↔ OperatorAnalytic (X := X) (Y := Y) f := by
  constructor
  · rintro ⟨g, rfl⟩
    exact hom_operatorAnalytic g
  · intro hf
    exact ⟨homOfOperatorAnalytic f hf, rfl⟩

/-- Fiberwise equivalences that are operator analytic in both directions give an
isomorphism. Taking `e b` to be the identity relates two presentations of the same
fibers with different models or atlases.-/
def isoOfOperatorAnalytic (e : ∀ b, X.Fiber b ≃L[K] Y.Fiber b)
    (he : OperatorAnalytic (X := X) (Y := Y) (fun b ↦ (e b).toContinuousLinearMap))
    (he_symm : OperatorAnalytic (X := Y) (Y := X)
      (fun b ↦ (e b).symm.toContinuousLinearMap)) : X ≅ Y :=
  isoOfFiberwiseContinuousLinearEquiv e
    ((operatorAnalytic_iff_contMDiff _).mp he)
    ((operatorAnalytic_iff_contMDiff _).mp he_symm)

@[simp]
theorem isoOfOperatorAnalytic_hom_apply (e : ∀ b, X.Fiber b ≃L[K] Y.Fiber b)
    (he he_symm) (b : M) :
    (isoOfOperatorAnalytic e he he_symm).hom b = (e b).toContinuousLinearMap := rfl

@[simp]
theorem isoOfOperatorAnalytic_inv_apply (e : ∀ b, X.Fiber b ≃L[K] Y.Fiber b)
    (he he_symm) (b : M) :
    (isoOfOperatorAnalytic e he he_symm).inv b = (e b).symm.toContinuousLinearMap := rfl

end AlternatingAnalytic.AnalyticBundleCat
