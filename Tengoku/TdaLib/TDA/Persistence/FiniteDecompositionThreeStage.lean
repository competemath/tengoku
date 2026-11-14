import Tengoku.TdaLib.TDA.Persistence.FiniteDecomposition
import Tengoku.Seed.LinearAlgebra.Prod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Three-stage examples distinguishing composite ranks

The input modules have the fibers `k`, `k × k`, `k`. Both first maps send
`x` to `(x, 0)`. The second maps project to the second or first coordinate.
-/

universe u
namespace TDA.Persistence.ThreeStageExamples
open CategoryTheory
variable {k : Type u} [Field k]

private def threeStageFiber (i : Fin 3) : ModuleCat.{u} k :=
  match i.val with
  | 1 => ModuleCat.of k (k × k)
  | _ => ModuleCat.of k k

private def threeStageMap (p : (k × k) →ₗ[k] k) (i j : Fin 3) :
    threeStageFiber (k := k) i ⟶ threeStageFiber (k := k) j :=
  match i, j with
  | ⟨0, _⟩, ⟨0, _⟩ => 𝟙 _
  | ⟨0, _⟩, ⟨1, _⟩ => ModuleCat.ofHom (LinearMap.inl k k k)
  | ⟨0, _⟩, ⟨_ + 2, _⟩ => ModuleCat.ofHom (p.comp (LinearMap.inl k k k))
  | ⟨1, _⟩, ⟨0, _⟩ => 0
  | ⟨1, _⟩, ⟨1, _⟩ => 𝟙 _
  | ⟨1, _⟩, ⟨_ + 2, _⟩ => ModuleCat.ofHom p
  | ⟨_ + 2, _⟩, ⟨0, _⟩ => 0
  | ⟨_ + 2, _⟩, ⟨1, _⟩ => 0
  | ⟨_ + 2, _⟩, ⟨_ + 2, _⟩ => 𝟙 _

private def threeStage (p : (k × k) →ₗ[k] k) : PModule.{u,0,u} k (Fin 3) where
  obj := threeStageFiber
  map {i j} _ := threeStageMap p i j
  map_id i := by fin_cases i <;> rfl
  map_comp {i j l} f g := by
    have hij : i ≤ j := leOfHom f
    have hjl : j ≤ l := leOfHom g
    fin_cases i <;> fin_cases j <;> fin_cases l <;>
      simp_all [threeStageMap, Fin.reduceFinMk] <;> apply ModuleCat.hom_ext <;> rfl

/-- The module `k → k² → k` with inclusion into the first coordinate followed by
projection onto the second coordinate.-/
def compositeZero : PModule.{u,0,u} k (Fin 3) :=
  threeStage (LinearMap.snd k k k)

/-- The module `k → k² → k` with inclusion into the first coordinate followed by
projection onto the first coordinate.-/
def compositeIdentity : PModule.{u,0,u} k (Fin 3) :=
  threeStage (LinearMap.fst k k k)

/--
@isnad1 id=finitedi.0h2v.s7.82db3ff7572b from=translated src=- shape=80115c00 vocab=26cf6885
-/
instance compositeZeroFD (i : Fin 3) :
    FiniteDimensional k ((compositeZero (k := k)).obj i) := by
  fin_cases i
  · change FiniteDimensional k k; infer_instance
  · change FiniteDimensional k (k × k); infer_instance
  · change FiniteDimensional k k; infer_instance

/--
@isnad1 id=finitedi.0h2v.s7.ec19a59f4261 from=translated src=- shape=80115c00 vocab=eef78420
-/
instance compositeIdentityFD (i : Fin 3) :
    FiniteDimensional k ((compositeIdentity (k := k)).obj i) := by
  fin_cases i
  · change FiniteDimensional k k; infer_instance
  · change FiniteDimensional k (k × k); infer_instance
  · change FiniteDimensional k k; infer_instance

/-- Both first transitions are the inclusion `x ↦ (x, 0)`.
@isnad1 id=and.0h1v.s10.a928fbf0686a from=translated src=- shape=a21cbd76 vocab=144bdd42
-/
theorem first_maps :
    structureMapLinear (compositeZero (k := k)) (show (0 : Fin 3) ≤ 1 by decide) =
      LinearMap.inl k k k ∧
    structureMapLinear (compositeIdentity (k := k)) (show (0 : Fin 3) ≤ 1 by decide) =
      LinearMap.inl k k k := ⟨rfl, rfl⟩

/-- The second transitions are the second and first projections.
@isnad1 id=and.0h1v.s10.739f50b70fff from=translated src=- shape=5d574716 vocab=51f79a0e
-/
theorem second_maps :
    structureMapLinear (compositeZero (k := k)) (show (1 : Fin 3) ≤ 2 by decide) =
      LinearMap.snd k k k ∧
    structureMapLinear (compositeIdentity (k := k)) (show (1 : Fin 3) ≤ 2 by decide) =
      LinearMap.fst k k k := ⟨rfl, rfl⟩

/-- The three fiber dimensions of both modules are `1, 2, 1`.
@isnad1 id=and.0h2v.s9.6d1dc93cdd8a from=translated src=- shape=dba2adaa vocab=7a60026f
-/
theorem stage_dimensions (i : Fin 3) :
    Module.finrank k ((compositeZero (k := k)).obj i) = (if i = 1 then 2 else 1) ∧
    Module.finrank k ((compositeIdentity (k := k)).obj i) = (if i = 1 then 2 else 1) := by
  fin_cases i
  · change Module.finrank k k = 1 ∧ Module.finrank k k = 1
    simp [Module.finrank_self]
  · change Module.finrank k (k × k) = 2 ∧ Module.finrank k (k × k) = 2
    simp [Module.finrank_prod, Module.finrank_self]
  · change Module.finrank k k = 1 ∧ Module.finrank k k = 1
    simp [Module.finrank_self]

/-- Both first transitions have rank one.
@isnad1 id=and.0h1v.s6.9686f99d16f9 from=translated src=- shape=8e2d08ab vocab=004440f0
-/
theorem first_ranks :
    structureMapRank (compositeZero (k := k)) 0 1 (by decide) = 1 ∧
    structureMapRank (compositeIdentity (k := k)) 0 1 (by decide) = 1 := by
  constructor <;>
    change Module.finrank k (LinearMap.range (LinearMap.inl k k k)) = 1 <;>
    rw [LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_self]

/-- Both second transitions have rank one.
@isnad1 id=and.0h1v.s6.9bfd5b46468d from=translated src=- shape=8e2d08ab vocab=004440f0
-/
theorem second_ranks :
    structureMapRank (compositeZero (k := k)) 1 2 (by decide) = 1 ∧
    structureMapRank (compositeIdentity (k := k)) 1 2 (by decide) = 1 := by
  constructor
  · change Module.finrank k (LinearMap.range (LinearMap.snd k k k)) = 1
    rw [LinearMap.range_eq_top.mpr LinearMap.snd_surjective, finrank_top,
      Module.finrank_self]
  · change Module.finrank k (LinearMap.range (LinearMap.fst k k k)) = 1
    rw [LinearMap.range_eq_top.mpr LinearMap.fst_surjective, finrank_top,
      Module.finrank_self]

/-- The composites have rank zero and one, respectively.
@isnad1 id=and.0h1v.s6.abec80b68f57 from=translated src=- shape=8e2d08ab vocab=004440f0
-/
theorem composite_ranks :
    structureMapRank (compositeZero (k := k)) 0 2 (by decide) = 0 ∧
    structureMapRank (compositeIdentity (k := k)) 0 2 (by decide) = 1 := by
  constructor
  · change Module.finrank k (LinearMap.range
      ((LinearMap.snd k k k).comp (LinearMap.inl k k k))) = 0
    have h : (LinearMap.snd k k k).comp (LinearMap.inl k k k) = 0 := by ext; rfl
    rw [h]
    simp
  · change Module.finrank k (LinearMap.range
      ((LinearMap.fst k k k).comp (LinearMap.inl k k k))) = 1
    have h : (LinearMap.fst k k k).comp (LinearMap.inl k k k) = LinearMap.id := by
      ext; rfl
    rw [h, LinearMap.range_id, finrank_top, Module.finrank_self]

/-- The two inputs agree at every stage dimension and at both adjacent-map ranks.
@isnad1 id=and.0h1v.s9.a25ffc963808 from=translated src=- shape=0791a719 vocab=dd7c9d4c
-/
theorem dimensions_and_adjacent_ranks_agree :
    (∀ i : Fin 3, Module.finrank k ((compositeZero (k := k)).obj i) =
      Module.finrank k ((compositeIdentity (k := k)).obj i)) ∧
    structureMapRank (compositeZero (k := k)) 0 1 (by decide) =
      structureMapRank (compositeIdentity (k := k)) 0 1 (by decide) ∧
    structureMapRank (compositeZero (k := k)) 1 2 (by decide) =
      structureMapRank (compositeIdentity (k := k)) 1 2 (by decide) := by
  refine ⟨fun i => (stage_dimensions i).1.trans (stage_dimensions i).2.symm, ?_, ?_⟩
  · exact (first_ranks (k := k)).1.trans (first_ranks (k := k)).2.symm
  · exact (second_ranks (k := k)).1.trans (second_ranks (k := k)).2.symm

/-- Equal fiber dimensions and adjacent ranks do not imply natural isomorphism.
@isnad1 id=not.0h1v.s6.22b93058d313 from=translated src=- shape=1e2ad73c vocab=453c3c24
-/
theorem not_iso : ¬ Nonempty (compositeZero (k := k) ≅ compositeIdentity (k := k)) := by
  rintro ⟨e⟩
  have h := structureMapRank_eq_of_iso e (0 : Fin 3) 2 (by decide)
  rw [(composite_ranks (k := k)).1, (composite_ranks (k := k)).2] at h
  exact Nat.zero_ne_one h

private def bar02 : FiniteInterval 3 := ⟨0, 2, by omega, by omega⟩
private def bar13 : FiniteInterval 3 := ⟨1, 3, by omega, by omega⟩
private def bar03 : FiniteInterval 3 := ⟨0, 3, by omega, by omega⟩
private def bar12 : FiniteInterval 3 := ⟨1, 2, by omega, by omega⟩

/-- The proposed decomposition of the module with zero composite: `[0,2) + [1,3)`.-/
def zeroBarcode : Multiset (FiniteInterval 3) := [bar02, bar13]

/-- The proposed decomposition of the module with identity composite: `[0,3) + [1,2)`.-/
def identityBarcode : Multiset (FiniteInterval 3) := [bar03, bar12]

private theorem self_rank (M : PModule.{u,0,u} k (Fin 3))
    [∀ i, FiniteDimensional k (M.obj i)] (i : Fin 3) :
    structureMapRank M i i (le_refl _) = Module.finrank k (M.obj i) := by
  unfold structureMapRank
  rw [structureMapLinear_self, LinearMap.range_id, finrank_top]

/-- The canonical barcode of the module with zero composite.
@isnad1 id=eq.0h1v.s4.68719d129354 from=translated src=- shape=114678c2 vocab=232c9b4c
-/
theorem zero_rankBarcode : rankBarcode (compositeZero (k := k)) = zeroBarcode := by
  have h : rankBarcode (compositeZero (k := k)) =
      rankBarcode (barcodeModule (k := k) zeroBarcode) := by
    apply (rankBarcode_eq_iff _ _).2
    intro i j hij
    rw [rank_barcodeMap]
    fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk] at *
    · rw [self_rank, (stage_dimensions (k := k) 0).1]
      decide
    · rw [(first_ranks (k := k)).1]
      decide
    · rw [(composite_ranks (k := k)).1]
      decide
    · norm_num [Fin.le_def] at hij
    · rw [self_rank, (stage_dimensions (k := k) 1).1]
      decide
    · rw [(second_ranks (k := k)).1]
      decide
    · norm_num [Fin.le_def] at hij
    · norm_num [Fin.le_def] at hij
    · rw [self_rank, (stage_dimensions (k := k) 2).1]
      decide
  simpa only [rankBarcode_barcodeModule] using h

/-- The canonical barcode of the module with identity composite.
@isnad1 id=eq.0h1v.s4.171e325c524e from=translated src=- shape=114678c2 vocab=ec2b5e57
-/
theorem identity_rankBarcode :
    rankBarcode (compositeIdentity (k := k)) = identityBarcode := by
  have h : rankBarcode (compositeIdentity (k := k)) =
      rankBarcode (barcodeModule (k := k) identityBarcode) := by
    apply (rankBarcode_eq_iff _ _).2
    intro i j hij
    rw [rank_barcodeMap]
    fin_cases i <;> fin_cases j <;> simp only [Fin.reduceFinMk] at *
    · rw [self_rank, (stage_dimensions (k := k) 0).2]
      decide
    · rw [(first_ranks (k := k)).2]
      decide
    · rw [(composite_ranks (k := k)).2]
      decide
    · norm_num [Fin.le_def] at hij
    · rw [self_rank, (stage_dimensions (k := k) 1).2]
      decide
    · rw [(second_ranks (k := k)).2]
      decide
    · norm_num [Fin.le_def] at hij
    · norm_num [Fin.le_def] at hij
    · rw [self_rank, (stage_dimensions (k := k) 2).2]
      decide
  simpa only [rankBarcode_barcodeModule] using h

/-- A genuine natural isomorphism realizing the decomposition `[0,2) + [1,3)`.
It applies the arbitrary-module theorem to the explicitly defined input.-/
noncomputable def zero_decompositionIso :
    compositeZero (k := k) ≅ barcodeModule (k := k) zeroBarcode :=
  rankBarcodeIso (compositeZero (k := k)) ≪≫
    eqToIso (congrArg (barcodeModule (k := k)) (zero_rankBarcode (k := k)))

/-- A genuine natural isomorphism realizing the decomposition `[0,3) + [1,2)`.
It applies the arbitrary-module theorem to the explicitly defined input.-/
noncomputable def identity_decompositionIso :
    compositeIdentity (k := k) ≅ barcodeModule (k := k) identityBarcode :=
  rankBarcodeIso (compositeIdentity (k := k)) ≪≫
    eqToIso (congrArg (barcodeModule (k := k)) (identity_rankBarcode (k := k)))

/-- Both stated interval decompositions exist as all-map natural isomorphisms.
@isnad1 id=and.0h1v.s7.6115d0936344 from=translated src=- shape=9de0e87f vocab=06a4c234
-/
theorem decompositions :
    Nonempty (compositeZero (k := k) ≅ barcodeModule (k := k) zeroBarcode) ∧
    Nonempty (compositeIdentity (k := k) ≅ barcodeModule (k := k) identityBarcode) :=
  ⟨⟨zero_decompositionIso⟩, ⟨identity_decompositionIso⟩⟩

end TDA.Persistence.ThreeStageExamples
