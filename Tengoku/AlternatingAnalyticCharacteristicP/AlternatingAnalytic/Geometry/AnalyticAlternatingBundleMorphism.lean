import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Geometry.AlternatingBundleMorphismAlgebra
import Tengoku.AlternatingAnalyticCharacteristicP.AlternatingAnalytic.Geometry.ContMDiffBundleHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Alternating bundle morphisms

Given `C^n` bundle morphisms `u : E' → E` and `v : F → F'`, the fiberwise operators
`m ↦ v ∘ m ∘ (u, …, u)` form a `C^n` section of the Hom bundle from `Alt^k(E; F)` to
`Alt^k(E'; F')`, provided the model action preserves `C^n` families. Over an analytic
manifold with finite continuous coordinates this hypothesis always holds. This is the
morphism part of Corollary 4.6 in the finite-coordinate setting.

## Main results

- `alternatingBundleHom_of_family`: the induced `C^n` Hom section.
- `alternatingBundleHom_of_finiteCoordinates`: the induced analytic Hom section over a
  finite-coordinate base.
- `analyticAlternatingBundleMorphism_of_finiteCoordinates`: its fiber formula,
  coordinates and functor laws.
-/

noncomputable section

open Bundle Set
open scoped Bundle Manifold ContDiff

namespace AlternatingAnalytic

variable {K M A A' B B' : Type*} [NontriviallyNormedField K] [TopologicalSpace M]
  [NormedAddCommGroup A] [NormedSpace K A]
  [NormedAddCommGroup A'] [NormedSpace K A']
  [NormedAddCommGroup B] [NormedSpace K B]
  [NormedAddCommGroup B'] [NormedSpace K B']
  {E E' F F' : M → Type*}
  [∀ b, AddCommGroup (E b)] [∀ b, Module K (E b)] [∀ b, TopologicalSpace (E b)]
  [∀ b, AddCommGroup (E' b)] [∀ b, Module K (E' b)] [∀ b, TopologicalSpace (E' b)]
  [∀ b, AddCommGroup (F b)] [∀ b, Module K (F b)] [∀ b, TopologicalSpace (F b)]
  [∀ b, AddCommGroup (F' b)] [∀ b, Module K (F' b)] [∀ b, TopologicalSpace (F' b)]
  [∀ b, IsTopologicalAddGroup (E b)] [∀ b, ContinuousSMul K (E b)]
  [∀ b, IsTopologicalAddGroup (F b)] [∀ b, ContinuousSMul K (F b)]
  [∀ b, IsTopologicalAddGroup (F' b)] [∀ b, ContinuousSMul K (F' b)]
  [TopologicalSpace (TotalSpace A E)] [TopologicalSpace (TotalSpace A' E')]
  [TopologicalSpace (TotalSpace B F)] [TopologicalSpace (TotalSpace B' F')]
  [FiberBundle A E] [VectorBundle K A E]
  [FiberBundle A' E'] [VectorBundle K A' E']
  [FiberBundle B F] [VectorBundle K B F]
  [FiberBundle B' F'] [VectorBundle K B' F']

section Regularity

variable {P H : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [TopologicalSpace H] [ChartedSpace H M] {I : ModelWithCorners K P H} {n : ℕ∞ω}
  [ContMDiffVectorBundle n A E I] [ContMDiffVectorBundle n A' E' I]
  [ContMDiffVectorBundle n B F I] [ContMDiffVectorBundle n B' F' I]
  (k : ℕ)
  (hfamily : ∀ {U : Set M}, IsOpen U →
    ∀ {γ : M → (A' →L[K] A) × (B →L[K] B')},
      ContMDiffOn I 𝓘(K, (A' →L[K] A) × (B →L[K] B')) n γ U →
      ContMDiffOn I 𝓘(K, (A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B'))
        n (alternatingMapAction k ∘ γ) U)
  (u : ContMDiffSection I (A' →L[K] A) n (fun b ↦ E' b →L[K] E b))
  (v : ContMDiffSection I (B →L[K] B') n (fun b ↦ F b →L[K] F' b))

include hfamily

/-- In atlas trivializations, the coordinates of the induced operators are `C^n` on any
open subset of the common domain.-/
theorem contMDiffOn_alternatingBundleMap_coordinates_of_family
    (eA : Trivialization A (π A E)) (eA' : Trivialization A' (π A' E'))
    (eB : Trivialization B (π B F)) (eB' : Trivialization B' (π B' F'))
    [MemTrivializationAtlas eA] [MemTrivializationAtlas eA']
    [MemTrivializationAtlas eB] [MemTrivializationAtlas eB']
    {U : Set M} (hU : IsOpen U)
    (hUe : U ⊆ (eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet)) :
    ContMDiffOn I 𝓘(K, (A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) n
      (fun b ↦ (((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap
        (RingHom.id K) (eA'.continuousAlternatingMap K (Fin k) eB'))
          ⟨b, alternatingBundleMap k (u b) (v b)⟩).2) U := by
  have hu := ((eA'.continuousLinearMap (RingHom.id K) eA).contMDiffOn_section_iff
    (IB := I) (n := n) hU (fun b hb ↦ ⟨(hUe hb).2.1, (hUe hb).1.1⟩)).mp
    u.contMDiff.contMDiffOn
  have hv := ((eB.continuousLinearMap (RingHom.id K) eB').contMDiffOn_section_iff
    (IB := I) (n := n) hU (fun b hb ↦ ⟨(hUe hb).1.2, (hUe hb).2.2⟩)).mp
    v.contMDiff.contMDiffOn
  exact (hfamily hU (hu.prodMk_space hv)).congr fun b hb ↦
    alternatingBundleMap_coordinates k eA eA' eB eB' b (hUe hb) (u b) (v b)

variable
  [ContMDiffVectorBundle n (A [⋀^Fin k]→L[K] B)
    (fun b ↦ E b [⋀^Fin k]→L[K] F b) I]
  [ContMDiffVectorBundle n (A' [⋀^Fin k]→L[K] B')
    (fun b ↦ E' b [⋀^Fin k]→L[K] F' b) I]

/-- The induced `C^n` section of the alternating Hom bundle. The regularity of the two
alternating bundles is assumed as instances.-/
def alternatingBundleHom_of_family :
    ContMDiffSection I ((A [⋀^Fin k]→L[K] B) →L[K] (A' [⋀^Fin k]→L[K] B')) n
      (fun b ↦ (E b [⋀^Fin k]→L[K] F b) →L[K] (E' b [⋀^Fin k]→L[K] F' b)) where
  toFun b := alternatingBundleMap k (u b) (v b)
  contMDiff_toFun := by
    intro b
    let eA := trivializationAt A E b
    let eA' := trivializationAt A' E' b
    let eB := trivializationAt B F b
    let eB' := trivializationAt B' F' b
    let U := (eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet)
    have hU : IsOpen U := (eA.open_baseSet.inter eB.open_baseSet).inter
      (eA'.open_baseSet.inter eB'.open_baseSet)
    have hb : b ∈ U :=
      ⟨⟨mem_baseSet_trivializationAt A E b, mem_baseSet_trivializationAt B F b⟩,
        ⟨mem_baseSet_trivializationAt A' E' b, mem_baseSet_trivializationAt B' F' b⟩⟩
    have hcoords := contMDiffOn_alternatingBundleMap_coordinates_of_family
      k hfamily u v eA eA' eB eB' hU subset_rfl
    exact ((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap
      (RingHom.id K) (eA'.continuousAlternatingMap K (Fin k) eB')).contMDiffAt_section_iff
      hb |>.mpr (hcoords.contMDiffAt (hU.mem_nhds hb))

@[simp]
theorem alternatingBundleHom_of_family_apply (b : M) :
    alternatingBundleHom_of_family k hfamily u v b = alternatingBundleMap k (u b) (v b) :=
  rfl

/-- The section acts on each fiber by pullback in every input and postcomposition.-/
theorem alternatingBundleHom_of_family_apply_apply (b : M)
    (m : E b [⋀^Fin k]→L[K] F b) :
    alternatingBundleHom_of_family k hfamily u v b m =
      (v b).compContinuousAlternatingMap (m.compContinuousLinearMap (u b)) :=
  rfl

/-- In atlas trivializations, the section is the model action of the trivialized pair.-/
theorem alternatingBundleHom_of_family_coordinates
    (eA : Trivialization A (π A E)) (eA' : Trivialization A' (π A' E'))
    (eB : Trivialization B (π B F)) (eB' : Trivialization B' (π B' F'))
    [MemTrivializationAtlas eA] [MemTrivializationAtlas eA']
    [MemTrivializationAtlas eB] [MemTrivializationAtlas eB']
    (b : M) (hb : b ∈ (eA.baseSet ∩ eB.baseSet) ∩ (eA'.baseSet ∩ eB'.baseSet)) :
    (((eA.continuousAlternatingMap K (Fin k) eB).continuousLinearMap
      (RingHom.id K) (eA'.continuousAlternatingMap K (Fin k) eB'))
        ⟨b, alternatingBundleHom_of_family k hfamily u v b⟩).2 =
      alternatingMapAction k
        (((eA'.continuousLinearMap (RingHom.id K) eA) ⟨b, u b⟩).2,
          ((eB.continuousLinearMap (RingHom.id K) eB') ⟨b, v b⟩).2) :=
  alternatingBundleMap_coordinates k eA eA' eB eB' b hb (u b) (v b)

end Regularity

section FiniteCoordinates

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace K P]
  [ChartedSpace P M] [IsManifold 𝓘(K, P) ω M]
  [ContMDiffVectorBundle ω A E 𝓘(K, P)] [ContMDiffVectorBundle ω A' E' 𝓘(K, P)]
  [ContMDiffVectorBundle ω B F 𝓘(K, P)] [ContMDiffVectorBundle ω B' F' 𝓘(K, P)]
  {d : ℕ} (c : P ≃L[K] (Fin d → K)) (k : ℕ)
  (u : ContMDiffSection 𝓘(K, P) (A' →L[K] A) ω (fun b ↦ E' b →L[K] E b))
  (v : ContMDiffSection 𝓘(K, P) (B →L[K] B') ω (fun b ↦ F b →L[K] F' b))

include c

variable {A'' B'' : Type*}
  [NormedAddCommGroup A''] [NormedSpace K A'']
  [NormedAddCommGroup B''] [NormedSpace K B'']
  {E'' F'' : M → Type*}
  [∀ b, AddCommGroup (E'' b)] [∀ b, Module K (E'' b)]
  [∀ b, TopologicalSpace (E'' b)]
  [∀ b, AddCommGroup (F'' b)] [∀ b, Module K (F'' b)]
  [∀ b, TopologicalSpace (F'' b)]
  [∀ b, IsTopologicalAddGroup (F'' b)] [∀ b, ContinuousSMul K (F'' b)]
  [TopologicalSpace (TotalSpace A'' E'')] [TopologicalSpace (TotalSpace B'' F'')]
  [FiberBundle A'' E''] [VectorBundle K A'' E'']
  [FiberBundle B'' F''] [VectorBundle K B'' F'']
  [ContMDiffVectorBundle ω A'' E'' 𝓘(K, P)]
  [ContMDiffVectorBundle ω B'' F'' 𝓘(K, P)]
  [∀ b, IsTopologicalAddGroup (E' b)] [∀ b, ContinuousSMul K (E' b)]
  (u' : ContMDiffSection 𝓘(K, P) (A'' →L[K] A') ω (fun b ↦ E'' b →L[K] E' b))
  (v' : ContMDiffSection 𝓘(K, P) (B' →L[K] B'') ω (fun b ↦ F' b →L[K] F'' b))

end FiniteCoordinates

end AlternatingAnalytic
