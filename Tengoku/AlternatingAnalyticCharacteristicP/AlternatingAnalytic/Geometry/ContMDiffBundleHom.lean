import Tengoku.Seed.Geometry.Manifold.VectorBundle.ContMDiffSection
import Tengoku.Seed.Geometry.Manifold.VectorBundle.Hom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Identity and composition of `C^n` bundle morphisms

The identity of a vector bundle and the composite of two `C^n` sections of Hom bundles are
`C^n` sections of the Hom bundle. The fibers are topological vector spaces; regularity is
measured in the normed model fibers.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff Topology

namespace AlternatingAnalytic

variable {K P H M : Type*} [NontriviallyNormedField K]
  [NormedAddCommGroup P] [NormedSpace K P] [TopologicalSpace H]
  {I : ModelWithCorners K P H} [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ∞ω}

section Identity

variable (A : Type*) [NormedAddCommGroup A] [NormedSpace K A]
  (E : M → Type*) [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)]
  [∀ b, TopologicalSpace (E b)] [∀ b, IsTopologicalAddGroup (E b)]
  [∀ b, ContinuousSMul K (E b)] [TopologicalSpace (TotalSpace A E)]
  [FiberBundle A E] [VectorBundle K A E]

/-- The identity of a vector bundle, as a `C^n` section of its Hom bundle.-/
def contMDiffHomId : ContMDiffSection I (A →L[K] A) n (fun b ↦ E b →L[K] E b) where
  toFun b := ContinuousLinearMap.id K (E b)
  contMDiff_toFun := by
    intro a
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    apply (contMDiffAt_const (c := ContinuousLinearMap.id K A)).congr_of_eventuallyEq
    filter_upwards [(trivializationAt A E a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt A E a)] with b hb
    rw [ContinuousLinearMap.inCoordinates_eq hb hb]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]

/--
@isnad1 id=eq.0h9v.s10.516b56e36329 from=translated src=- shape=e97b4daf vocab=a4245494
-/
@[simp]
theorem contMDiffHomId_apply (b : M) :
    contMDiffHomId (I := I) (n := n) A E b = ContinuousLinearMap.id K (E b) := rfl

end Identity

section Composition

variable {A B C : Type*}
  [NormedAddCommGroup A] [NormedSpace K A]
  [NormedAddCommGroup B] [NormedSpace K B]
  [NormedAddCommGroup C] [NormedSpace K C]
  {E F G : M → Type*}
  [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
  [∀ b, AddCommGroup (G b)] [∀ b, Module K (G b)] [∀ b, TopologicalSpace (G b)]
  [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
  [∀ b, IsTopologicalAddGroup (G b)] [∀ b, ContinuousSMul K (G b)]
  [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace B F)]
  [TopologicalSpace (TotalSpace C G)]
  [FiberBundle A E] [VectorBundle K A E]
  [FiberBundle B F] [VectorBundle K B F]
  [FiberBundle C G] [VectorBundle K C G]

/-- The fiberwise composite of two `C^n` Hom sections.-/
def contMDiffHomComp
    (f : ContMDiffSection I (A →L[K] B) n (fun b ↦ E b →L[K] F b))
    (g : ContMDiffSection I (B →L[K] C) n (fun b ↦ F b →L[K] G b)) :
    ContMDiffSection I (A →L[K] C) n (fun b ↦ E b →L[K] G b) where
  toFun b := (g b).comp (f b)
  contMDiff_toFun := by
    intro a
    apply (contMDiffAt_hom_bundle _).mpr
    refine ⟨contMDiffAt_id, ?_⟩
    have hf := ((contMDiffAt_hom_bundle _).mp (f.contMDiff a)).2
    have hg := ((contMDiffAt_hom_bundle _).mp (g.contMDiff a)).2
    apply (hg.clm_comp hf).congr_of_eventuallyEq
    filter_upwards [(trivializationAt A E a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt A E a),
      (trivializationAt B F a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt B F a),
      (trivializationAt C G a).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt C G a)] with b hE hF hG
    rw [ContinuousLinearMap.inCoordinates_eq hE hG,
      ContinuousLinearMap.inCoordinates_eq hF hG,
      ContinuousLinearMap.inCoordinates_eq hE hF]
    ext v
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.symm_apply_apply]

/--
@isnad1 id=eq.0h15v.s12.28aae205ea3a from=translated src=- shape=daf81554 vocab=adb0cf58
-/
@[simp]
theorem contMDiffHomComp_apply
    (f : ContMDiffSection I (A →L[K] B) n (fun b ↦ E b →L[K] F b))
    (g : ContMDiffSection I (B →L[K] C) n (fun b ↦ F b →L[K] G b)) (b : M) :
    contMDiffHomComp f g b = (g b).comp (f b) := rfl

end Composition

end AlternatingAnalytic
