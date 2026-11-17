import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Geometry.AnalyticAlternatingBundle
import Tengoku.Seed.Geometry.Manifold.VectorBundle.Hom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # The alternating action on bundle fibers

Defines the operator `m ↦ v ∘ m ∘ (u, …, u)` on spaces of continuous alternating maps
between topological vector spaces, proves the functor laws, and shows that in
bundle trivializations it is given by the model action `alternatingMapAction`.
This is the fiberwise construction behind Corollary 4.6.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalytic

section FiberMaps

variable {K E E' E'' F F' F'' : Type*} [NontriviallyNormedField K]
  [AddCommGroup E] [Module K E] [TopologicalSpace E]
  [AddCommGroup E'] [Module K E'] [TopologicalSpace E'] [ContinuousSMul K E']
  [AddCommGroup E''] [Module K E''] [TopologicalSpace E''] [ContinuousSMul K E'']
  [AddCommGroup F] [Module K F] [TopologicalSpace F]
  [IsTopologicalAddGroup F] [ContinuousSMul K F]
  [AddCommGroup F'] [Module K F'] [TopologicalSpace F']
  [IsTopologicalAddGroup F'] [ContinuousSMul K F']
  [AddCommGroup F''] [Module K F''] [TopologicalSpace F'']
  [IsTopologicalAddGroup F''] [ContinuousSMul K F'']

/-- Pull back each input by `u` and push forward the output by `v`.-/
def alternatingBundleMap (k : ℕ) (u : E' →L[K] E) (v : F →L[K] F') :
    (E [⋀^Fin k]→L[K] F) →L[K] (E' [⋀^Fin k]→L[K] F') :=
  (ContinuousLinearMap.compContinuousAlternatingMapCLM K E' F F' (Fin k) v).comp
    (ContinuousAlternatingMap.compContinuousLinearMapCLM u)

omit [ContinuousSMul K E'] in
@[simp]
theorem alternatingBundleMap_apply (k : ℕ) (u : E' →L[K] E) (v : F →L[K] F')
    (m : E [⋀^Fin k]→L[K] F) (x : Fin k → E') :
    alternatingBundleMap k u v m x = v (m fun i ↦ u (x i)) := rfl

/-- The identity pair acts as the identity operator.-/
@[simp]
theorem alternatingBundleMap_id [ContinuousSMul K E] (k : ℕ) :
    alternatingBundleMap k (ContinuousLinearMap.id K E) (ContinuousLinearMap.id K F) =
      ContinuousLinearMap.id K (E [⋀^Fin k]→L[K] F) := by
  ext m x
  rfl

omit [ContinuousSMul K E'] [ContinuousSMul K E''] in
/-- The action is contravariant in the inputs and covariant in the output.-/
@[simp]
theorem alternatingBundleMap_comp (k : ℕ)
    (u : E' →L[K] E) (u' : E'' →L[K] E')
    (v : F →L[K] F') (v' : F' →L[K] F'') :
    alternatingBundleMap k (u.comp u') (v'.comp v) =
      (alternatingBundleMap k u' v').comp (alternatingBundleMap k u v) := by
  ext m x
  rfl

end FiberMaps

section Coordinates

variable {K M A A' B B' : Type*} [NontriviallyNormedField K] [TopologicalSpace M]
  [NormedAddCommGroup A] [NormedSpace K A]
  [NormedAddCommGroup A'] [NormedSpace K A']
  [NormedAddCommGroup B] [NormedSpace K B]
  [NormedAddCommGroup B'] [NormedSpace K B']
  {E E' F F' : M → Type*}
  [∀ x, AddCommGroup (E x)] [∀ x, Module K (E x)] [∀ x, TopologicalSpace (E x)]
  [∀ x, IsTopologicalAddGroup (E x)] [∀ x, ContinuousSMul K (E x)]
  [∀ x, AddCommGroup (E' x)] [∀ x, Module K (E' x)] [∀ x, TopologicalSpace (E' x)]
  [∀ x, IsTopologicalAddGroup (E' x)] [∀ x, ContinuousSMul K (E' x)]
  [∀ x, AddCommGroup (F x)] [∀ x, Module K (F x)] [∀ x, TopologicalSpace (F x)]
  [∀ x, IsTopologicalAddGroup (F x)] [∀ x, ContinuousSMul K (F x)]
  [∀ x, AddCommGroup (F' x)] [∀ x, Module K (F' x)] [∀ x, TopologicalSpace (F' x)]
  [∀ x, IsTopologicalAddGroup (F' x)] [∀ x, ContinuousSMul K (F' x)]
  [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
  [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
  [FiberBundle A E] [VectorBundle K A E]
  [FiberBundle A' E'] [VectorBundle K A' E']
  [FiberBundle B F] [VectorBundle K B F]
  [FiberBundle B' F'] [VectorBundle K B' F']

omit [∀ x, IsTopologicalAddGroup (E' x)] [∀ x, ContinuousSMul K (E' x)] in
/-- In four atlas trivializations, on their common domain, the induced operator is
the model action of the trivialized pair `(u, v)`.-/
theorem alternatingBundleMap_coordinates (k : ℕ)
    (eA : Trivialization A (π A E)) (eA' : Trivialization A' (π A' E'))
    (eB : Trivialization B (π B F)) (eB' : Trivialization B' (π B' F'))
    [MemTrivializationAtlas eA] [MemTrivializationAtlas eA']
    [MemTrivializationAtlas eB] [MemTrivializationAtlas eB']
    (b : M) (hb : b ∈ (eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet))
    (u : E' b →L[K] E b) (v : F b →L[K] F' b) :
    (((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap (RingHom.id K)
        (eA'.continuousAlternatingMap K (Fin k) eB'))
      ⟨b, alternatingBundleMap k u v⟩).2 =
      alternatingMapAction k
        (((eA'.continuousLinearMap (RingHom.id K) eA) ⟨b, u⟩).2,
          ((eB.continuousLinearMap (RingHom.id K) eB') ⟨b, v⟩).2) := by
  rw [Trivialization.continuousLinearMap_apply]
  ext m x
  simp only [ContinuousLinearMap.comp_apply, alternatingMapAction_apply]
  rw [Trivialization.continuousLinearMapAt_apply_of_mem K _ hb.2]
  rw [Trivialization.continuousAlternatingMap_apply]
  rw [Trivialization.symmL_apply _ hb.1]
  change eB'.continuousLinearMapAt K b
      (v (((Pretrivialization.continuousAlternatingMap K (Fin k) eA eB).symm b m)
        (fun i ↦ u (eA'.symmL K b (x i))))) = _
  rw [Pretrivialization.continuousAlternatingMap_symm_apply' hb.1]
  rfl

end Coordinates

end AlternatingAnalytic
