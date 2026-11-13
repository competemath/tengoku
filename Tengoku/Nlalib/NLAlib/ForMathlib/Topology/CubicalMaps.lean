import Tengoku.Nlalib.NLAlib.ForMathlib.Topology.CubicalChains

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Continuous images and subtype lifts of normalized cubical chains

Continuous maps act on the actual singular cubes and commute with both
boundary maps and constant-edge normalization. A finite chain whose active
edges lie in a subset has an actual lift to that subset; no ambient
extension of a path or arbitrary base point is needed.
-/

noncomputable section
open scoped unitInterval
namespace Cubical

variable {X Y Z : Type*} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]

/-- Push forward a finite cubical one-chain along an actual continuous map.-/
def mapOne (f : C(X, Y)) : OneChain X →ₗ[ℤ] OneChain Y :=
  Finsupp.lmapDomain ℤ ℤ (fun γ => f.comp γ)

/-- Push forward a finite cubical two-chain along an actual continuous map.-/
def mapTwo (f : C(X, Y)) : TwoChain X →ₗ[ℤ] TwoChain Y :=
  Finsupp.lmapDomain ℤ ℤ (fun q => f.comp q)

/-- Push forward the finite endpoint chain.-/
def mapZero (f : C(X, Y)) : (X →₀ ℤ) →ₗ[ℤ] (Y →₀ ℤ) :=
  Finsupp.lmapDomain ℤ ℤ f

/--
@isnad1 id=eq.0h5v.s8.f0f1ae081b6e from=translated src=- shape=86e5e40b vocab=7adc40bc
-/
@[simp]
theorem mapOne_single (f : C(X, Y)) (γ : C(I, X)) (k : ℤ) :
    mapOne f (Finsupp.single γ k) = Finsupp.single (f.comp γ) k := by
  simp [mapOne]

/--
@isnad1 id=eq.0h5v.s9.694a105ea7c4 from=translated src=- shape=d56ccf86 vocab=66a47f99
-/
@[simp]
theorem mapTwo_single (f : C(X, Y)) (q : C(I × I, X)) (k : ℤ) :
    mapTwo f (Finsupp.single q k) = Finsupp.single (f.comp q) k := by
  simp [mapTwo]

/--
@isnad1 id=eq.0h5v.s7.4354c280b88a from=translated src=- shape=0a03539e vocab=2b2045d2
-/
@[simp]
theorem mapZero_single (f : C(X, Y)) (x : X) (k : ℤ) :
    mapZero f (Finsupp.single x k) = Finsupp.single (f x) k := by
  simp [mapZero]

/-- Actual one-chain pushforwards respect composition of continuous maps.
@isnad1 id=eq.0h6v.s9.ca2482f78fbb from=translated src=- shape=049dca28 vocab=fa26b803
-/
theorem mapOne_mapOne (f : C(X, Y)) (g : C(Y, Z)) (Γ : OneChain X) :
    mapOne g (mapOne f Γ) = mapOne (g.comp f) Γ := by
  have h : (mapOne g).comp (mapOne f) = mapOne (g.comp f) := by
    apply Finsupp.lhom_ext
    intro γ k
    simp only [LinearMap.comp_apply, mapOne_single]
    rfl
  exact LinearMap.congr_fun h Γ

/-- Mapping a square maps each of its four faces.
@isnad1 id=eq.0h4v.s8.2ea039855967 from=translated src=- shape=5c939954 vocab=48ba5f1c
-/
theorem mapOne_squareBoundary (f : C(X, Y)) (q : C(I × I, X)) :
    mapOne f (squareBoundary q) = squareBoundary (f.comp q) := by
  have hL : f.comp (left q) = left (f.comp q) := by ext t; rfl
  have hR : f.comp (right q) = right (f.comp q) := by ext t; rfl
  have hB : f.comp (bottom q) = bottom (f.comp q) := by ext t; rfl
  have hT : f.comp (top q) = top (f.comp q) := by ext t; rfl
  simp only [squareBoundary, map_add, map_sub, mapOne_single, hL, hR, hB, hT]

/-- Continuous pushforward commutes with the endpoint boundary.
@isnad1 id=eq.0h4v.s9.0f251ba00229 from=translated src=- shape=35cbfb54 vocab=29c8c903
-/
theorem boundaryOne_mapOne (f : C(X, Y)) (Γ : OneChain X) :
    boundaryOne (mapOne f Γ) = mapZero f (boundaryOne Γ) := by
  have h : boundaryOne.comp (mapOne f) = (mapZero f).comp boundaryOne := by
    apply Finsupp.lhom_ext
    intro γ k
    simp [boundaryOne]
  exact LinearMap.congr_fun h Γ

/-- Continuous pushforward commutes with the two-dimensional boundary.
@isnad1 id=eq.0h4v.s10.0ad1ff6d8fac from=translated src=- shape=8d3be4a5 vocab=48288bfc
-/
theorem boundaryTwo_mapTwo (f : C(X, Y)) (S : TwoChain X) :
    boundaryTwo (mapTwo f S) = mapOne f (boundaryTwo S) := by
  have h : boundaryTwo.comp (mapTwo f) = (mapOne f).comp boundaryTwo := by
    apply Finsupp.lhom_ext
    intro q k
    simp [boundaryTwo, mapOne_squareBoundary]
  exact LinearMap.congr_fun h S

/-- Continuous pushforward commutes with degenerate constant edges.
@isnad1 id=eq.0h4v.s9.bc29b4fab7e0 from=translated src=- shape=bd12fd9e vocab=b55fdaaa
-/
theorem constantChain_mapZero (f : C(X, Y)) (D : X →₀ ℤ) :
    constantChain (mapZero f D) = mapOne f (constantChain D) := by
  have h : constantChain.comp (mapZero f) = (mapOne f).comp constantChain := by
    apply Finsupp.lhom_ext
    intro x k
    simp [constantChain, ContinuousMap.comp_const]
  exact LinearMap.congr_fun h D

/-- An actual normalized filling pushes forward continuously.
@isnad1 id=isnullho.1h4v.s8.c106b7ea56c7 from=translated src=- shape=00ec461b vocab=1dd2c9a8
-/
theorem IsNullHomologous.map {Γ : OneChain X} (hΓ : IsNullHomologous Γ) (f : C(X, Y)) :
    IsNullHomologous (mapOne f Γ) := by
  obtain ⟨S, D, rfl⟩ := hΓ
  refine ⟨mapTwo f S, mapZero f D, ?_⟩
  rw [boundaryTwo_mapTwo, constantChain_mapZero, ← map_add]

/-- An injective continuous map is injective on actual interval maps.
@isnad1 id=injectiv.1h4v.s6.6a9e50ba1ca1 from=translated src=- shape=bf2db655 vocab=f6a6896f
-/
theorem comp_injective {A : Type*} [TopologicalSpace A]
    (f : C(X, Y)) (hf : Function.Injective f) :
    Function.Injective (fun γ : C(A, X) => f.comp γ) := by
  intro γ δ h
  ext t
  apply hf
  exact congrArg (fun p : C(A, Y) => p t) h

/-- An injective continuous map induces an injective one-chain map.
@isnad1 id=injectiv.1h3v.s8.3323e0457adf from=translated src=- shape=53613a6f vocab=d86615ef
-/
theorem mapOne_injective (f : C(X, Y)) (hf : Function.Injective f) :
    Function.Injective (mapOne f) :=
  Finsupp.mapDomain_injective (comp_injective f hf)

/-- An injective continuous map induces an injective endpoint-chain map.
@isnad1 id=injectiv.1h3v.s7.1e0c01753b8b from=translated src=- shape=86b8f78f vocab=6f969baa
-/
theorem mapZero_injective (f : C(X, Y)) (hf : Function.Injective f) :
    Function.Injective (mapZero f) :=
  Finsupp.mapDomain_injective hf

/-- A finite chain whose actual active paths lie in a subset lifts to that
subset. This also covers an empty chain in an empty subset.
@isnad1 id=ex.1h3v.s9.d1d53006273b from=translated src=- shape=9ee5e825 vocab=c90c9a3d
-/
theorem exists_mapOne_subtype_val_eq (Γ : OneChain X) (S : Set X)
    (hΓ : ∀ γ ∈ Γ.support, ∀ t, γ t ∈ S) :
    ∃ Δ : OneChain S,
      mapOne (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) Δ = Γ := by
  let j : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hj : Function.Injective (fun γ : C(I, S) => j.comp γ) :=
    comp_injective j Subtype.val_injective
  have hs : (↑Γ.support : Set C(I, X)) ⊆ Set.range (fun γ : C(I, S) => j.comp γ) := by
    intro γ hγ
    refine ⟨⟨fun t => ⟨γ t, hΓ γ hγ t⟩, γ.continuous.subtype_mk _⟩, ?_⟩
    ext t
    rfl
  refine ⟨Finsupp.comapDomain (fun γ : C(I, S) => j.comp γ) Γ hj.injOn, ?_⟩
  exact Finsupp.mapDomain_comapDomain _ hj Γ hs

/-- A finite two-chain whose active continuous squares lie in a subset has
an actual lift to that subset, including an empty subset and empty chain.
@isnad1 id=ex.1h3v.s10.d35457801258 from=translated src=- shape=6f179b9a vocab=49c1364c
-/
theorem exists_mapTwo_subtype_val_eq (Γ : TwoChain X) (S : Set X)
    (hΓ : ∀ q ∈ Γ.support, ∀ t, q t ∈ S) :
    ∃ Δ : TwoChain S,
      mapTwo (⟨Subtype.val, continuous_subtype_val⟩ : C(S, X)) Δ = Γ := by
  let j : C(S, X) := ⟨Subtype.val, continuous_subtype_val⟩
  have hj : Function.Injective (fun q : C(I × I, S) => j.comp q) :=
    comp_injective j Subtype.val_injective
  have hs : (↑Γ.support : Set C(I × I, X)) ⊆
      Set.range (fun q : C(I × I, S) => j.comp q) := by
    intro q hq
    refine ⟨⟨fun t => ⟨q t, hΓ q hq t⟩, q.continuous.subtype_mk _⟩, ?_⟩
    ext t
    rfl
  refine ⟨Finsupp.comapDomain (fun q : C(I × I, S) => j.comp q) Γ hj.injOn, ?_⟩
  exact Finsupp.mapDomain_comapDomain _ hj Γ hs

end Cubical
