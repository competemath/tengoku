import Tengoku.TdaLib.TDA.Persistence.MatrixSequence
import Tengoku.TdaLib.TDA.Persistence.FiniteDecompositionThreeStage
import Tengoku.TdaLib.TDA.Persistence.FiniteDecompositionExamples
import Tengoku.Seed.LinearAlgebra.Matrix.Notation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Consumers of finite matrix representations

The rectangular three-stage inputs distinguish composite ranks that adjacent ranks cannot
see. Coordinate changes and morphisms exercise the public finite-line and matrix APIs.
-/

namespace TDA.Persistence.MatrixSequenceExamples
open CategoryTheory
open scoped Matrix
noncomputable section

/-- A rectangular sequence with inclusion into the first coordinate and row `[a,b]`.-/
def threeStage (a b : ℚ) : MatrixSequence ℚ 3 where
  dim i := match i.val with | 1 => 2 | _ => 1
  step i j _ := match i, j with
    | ⟨0, _⟩, ⟨1, _⟩ => !![1; 0]
    | ⟨1, _⟩, ⟨_ + 2, _⟩ => !![a, b]
    | _, _ => 0

/-- Inclusion followed by the second projection, giving zero composite.-/
def compositeZero : MatrixSequence ℚ 3 := threeStage 0 1

/-- Inclusion followed by the first projection, giving identity composite.-/
def compositeIdentity : MatrixSequence ℚ 3 := threeStage 1 0

/-- Both rectangular inputs have dimensions `1,2,1`.
@isnad1 id=and.0h1v.s6.86b0da5cdee6 from=translated src=- shape=ca784a4e vocab=ad73d833
-/
theorem dimensions (i : Fin 3) :
    compositeZero.dim i = ![1, 2, 1] i ∧ compositeIdentity.dim i = ![1, 2, 1] i := by
  fin_cases i <;> exact ⟨rfl, rfl⟩

/-- The first transition matrix is the column inclusion.
@isnad1 id=eq.0h2v.s8.4954fc76bce7 from=translated src=- shape=10ba81d5 vocab=c3279208
-/
theorem first_matrix (a b : ℚ) :
    (threeStage a b).step 0 1 (by decide) = !![1; 0] := rfl

/-- The second transition matrix is the supplied row.
@isnad1 id=eq.0h2v.s8.68dc4fd820cc from=translated src=- shape=63a8aab6 vocab=c3279208
-/
theorem second_matrix (a b : ℚ) :
    (threeStage a b).step 1 2 (by decide) = !![a, b] := rfl

private def zeroStageIso (i : Fin 3) :
    compositeZero.toPModule.obj i ≅ (ThreeStageExamples.compositeZero (k := ℚ)).obj i :=
  match i with
  | ⟨0, _⟩ => (LinearEquiv.funUnique (Fin 1) ℚ ℚ).toModuleIso
  | ⟨1, _⟩ => (LinearEquiv.finTwoArrow ℚ ℚ).toModuleIso
  | ⟨_ + 2, _⟩ => (LinearEquiv.funUnique (Fin 1) ℚ ℚ).toModuleIso

private def identityStageIso (i : Fin 3) :
    compositeIdentity.toPModule.obj i ≅ (ThreeStageExamples.compositeIdentity (k := ℚ)).obj i :=
  match i with
  | ⟨0, _⟩ => (LinearEquiv.funUnique (Fin 1) ℚ ℚ).toModuleIso
  | ⟨1, _⟩ => (LinearEquiv.finTwoArrow ℚ ℚ).toModuleIso
  | ⟨_ + 2, _⟩ => (LinearEquiv.funUnique (Fin 1) ℚ ℚ).toModuleIso

/-- The zero-composite matrix input realizes the existing concrete three-stage module.-/
def compositeZeroIso :
    compositeZero.toPModule ≅ ThreeStageExamples.compositeZero (k := ℚ) :=
  FiniteLine.isoOfAdjacent zeroStageIso (by
    intro i j h
    apply ModuleCat.hom_ext
    change (zeroStageIso j).hom.hom.comp (structureMapLinear compositeZero.toPModule _) =
      (structureMapLinear (ThreeStageExamples.compositeZero (k := ℚ)) _).comp
        (zeroStageIso i).hom.hom
    rw [MatrixSequence.structureMapLinear_adjacent compositeZero i j h]
    fin_cases i <;> fin_cases j <;> simp at h
    · rw [(ThreeStageExamples.first_maps (k := ℚ)).1]
      apply LinearMap.ext
      intro x
      change (((!![1; 0] : Matrix (Fin 2) (Fin 1) ℚ) *ᵥ x) 0,
        ((!![1; 0] : Matrix (Fin 2) (Fin 1) ℚ) *ᵥ x) 1) = (x (0 : Fin 1), 0)
      simp [Matrix.mulVec, dotProduct]
      exact Finset.sum_singleton _ _
    · rw [(ThreeStageExamples.second_maps (k := ℚ)).1]
      apply LinearMap.ext
      intro x
      change ((!![0, 1] : Matrix (Fin 1) (Fin 2) ℚ) *ᵥ x) 0 = x (1 : Fin 2)
      simp [Matrix.mulVec, dotProduct])

/-- The identity-composite matrix input realizes the other concrete three-stage module.-/
def compositeIdentityIso :
    compositeIdentity.toPModule ≅ ThreeStageExamples.compositeIdentity (k := ℚ) :=
  FiniteLine.isoOfAdjacent identityStageIso (by
    intro i j h
    apply ModuleCat.hom_ext
    change (identityStageIso j).hom.hom.comp (structureMapLinear compositeIdentity.toPModule _) =
      (structureMapLinear (ThreeStageExamples.compositeIdentity (k := ℚ)) _).comp
        (identityStageIso i).hom.hom
    rw [MatrixSequence.structureMapLinear_adjacent compositeIdentity i j h]
    fin_cases i <;> fin_cases j <;> simp at h
    · rw [(ThreeStageExamples.first_maps (k := ℚ)).2]
      apply LinearMap.ext
      intro x
      change (((!![1; 0] : Matrix (Fin 2) (Fin 1) ℚ) *ᵥ x) 0,
        ((!![1; 0] : Matrix (Fin 2) (Fin 1) ℚ) *ᵥ x) 1) = (x (0 : Fin 1), 0)
      simp [Matrix.mulVec, dotProduct]
      exact Finset.sum_singleton _ _
    · rw [(ThreeStageExamples.second_maps (k := ℚ)).2]
      apply LinearMap.ext
      intro x
      change ((!![1, 0] : Matrix (Fin 1) (Fin 2) ℚ) *ᵥ x) 0 = x (0 : Fin 2)
      simp [Matrix.mulVec, dotProduct])

/-- The zero-composite input has barcode `[0,2)+[1,3)`.
@isnad1 id=eq.0h0v.s4.ccdd41a4c1d0 from=translated src=- shape=ace12cc1 vocab=63d8b44b
-/
theorem compositeZero_barcode : compositeZero.barcode = ThreeStageExamples.zeroBarcode := by
  exact (rankBarcode_eq_of_iso compositeZeroIso).trans ThreeStageExamples.zero_rankBarcode

/-- The identity-composite input has barcode `[0,3)+[1,2)`.
@isnad1 id=eq.0h0v.s4.4ff52e1a3e17 from=translated src=- shape=ace12cc1 vocab=afdda5e0
-/
theorem compositeIdentity_barcode :
    compositeIdentity.barcode = ThreeStageExamples.identityBarcode := by
  exact (rankBarcode_eq_of_iso compositeIdentityIso).trans ThreeStageExamples.identity_rankBarcode

/-- The two matrix barcodes are different.
@isnad1 id=ne.0h0v.s4.09061c3039b4 from=translated src=- shape=8262b056 vocab=7e80611a
-/
theorem barcodes_distinct : compositeZero.barcode ≠ compositeIdentity.barcode := by
  rw [compositeZero_barcode, compositeIdentity_barcode]
  decide

/-- Equal dimensions and adjacent ranks coexist with different composite ranks.
@isnad1 id=and.0h0v.s8.86da26af5d03 from=translated src=- shape=a97639e5 vocab=21819f2b
-/
theorem adjacent_ranks_and_composites :
    structureMapRank compositeZero.toPModule 0 1 (by decide) = 1 ∧
    structureMapRank compositeIdentity.toPModule 0 1 (by decide) = 1 ∧
    structureMapRank compositeZero.toPModule 1 2 (by decide) = 1 ∧
    structureMapRank compositeIdentity.toPModule 1 2 (by decide) = 1 ∧
    structureMapRank compositeZero.toPModule 0 2 (by decide) = 0 ∧
    structureMapRank compositeIdentity.toPModule 0 2 (by decide) = 1 := by
  simp only [structureMapRank_eq_of_iso compositeZeroIso,
    structureMapRank_eq_of_iso compositeIdentityIso]
  exact ⟨ThreeStageExamples.first_ranks.1, ThreeStageExamples.first_ranks.2,
    ThreeStageExamples.second_ranks.1, ThreeStageExamples.second_ranks.2,
    ThreeStageExamples.composite_ranks.1, ThreeStageExamples.composite_ranks.2⟩

/-- No vertices and no hidden nonemptiness requirement.-/
def empty : MatrixSequence ℚ 0 where
  dim := Fin.elim0
  step i := Fin.elim0 i

/-- Empty input has the empty canonical barcode.
@isnad1 id=eq.0h0v.s5.2d83f1577134 from=translated src=- shape=e4db5534 vocab=ad33001f
-/
theorem empty_barcode : empty.barcode = 0 :=
  FiniteDecompositionExamples.emptyIndex_barcode empty.toPModule

/-- One two-dimensional stage, which must retain a repeated interval.-/
def oneStagePair : MatrixSequence ℚ 1 where
  dim _ := 2
  step i j h := by have hi := i.isLt; have hj := j.isLt; omega

/-- The one-stage coordinate plane is the pair module.-/
def oneStagePairIso :
    oneStagePair.toPModule ≅ FiniteDecompositionExamples.oneStagePair (k := ℚ) :=
  FiniteLine.isoOfAdjacent (fun _ => (LinearEquiv.finTwoArrow ℚ ℚ).toModuleIso)
    (by intro i j h; have hi := i.isLt; have hj := j.isLt; omega)

/-- Two copies of the same interval survive with multiplicity two.
@isnad1 id=eq.0h0v.s4.3b27bf3fc06f from=translated src=- shape=36d02da6 vocab=fcffde22
-/
theorem oneStagePair_barcode : oneStagePair.barcode =
    Multiset.replicate 2 FiniteDecompositionExamples.bar01 :=
  (rankBarcode_eq_of_iso oneStagePairIso).trans FiniteDecompositionExamples.oneStagePair_barcode

/-- A nonempty input with a zero-dimensional stage.-/
def oneStageZero : MatrixSequence ℚ 1 where
  dim _ := 0
  step i j h := by have hi := i.isLt; have hj := j.isLt; omega

/-- The zero coordinate space realizes the zero diagram without a positive dimension assumption.-/
def oneStageZeroIso :
    oneStageZero.toPModule ≅ FiniteDecompositionExamples.zeroDiagram (k := ℚ) 1 :=
  FiniteLine.isoOfAdjacent (fun _ => Iso.refl _)
    (by intro i j h; have hi := i.isLt; have hj := j.isLt; omega)

/-- A zero-dimensional stage has no intervals.
@isnad1 id=eq.0h0v.s5.867d20414c39 from=translated src=- shape=e4db5534 vocab=caa3031a
-/
theorem oneStageZero_barcode : oneStageZero.barcode = 0 :=
  (rankBarcode_eq_of_iso oneStageZeroIso).trans (FiniteDecompositionExamples.zeroDiagram_barcode 1)

/-- A scalar transition whose coefficient is two.-/
def scalarTwo : MatrixSequence ℚ 2 where
  dim _ := 1
  step _ _ _ := !![2]

/-- The scalar transition acts by the supplied nonzero, nonidentity scalar.
@isnad1 id=eq.0h1v.s10.fba670bec0d1 from=translated src=- shape=d8f5a629 vocab=bcedcf3c
-/
theorem scalarTwo_apply (x : Fin 1 → ℚ) :
    structureMapLinear scalarTwo.toPModule (show (0 : Fin 2) ≤ 1 by decide) x (0 : Fin 1) = 2 * x 0 := by
  rw [MatrixSequence.structureMapLinear_adjacent scalarTwo 0 1 (by decide)]
  change ((!![2] : Matrix (Fin 1) (Fin 1) ℚ) *ᵥ x) 0 = 2 * x 0
  simp [Matrix.mulVec, dotProduct]

/-- The scalar transition is not the identity.
@isnad1 id=ne.0h0v.s9.5278377b8564 from=translated src=- shape=dff7925f vocab=571c4c03
-/
theorem scalarTwo_nonidentity :
    structureMapLinear scalarTwo.toPModule (show (0 : Fin 2) ≤ 1 by decide) ≠ LinearMap.id := by
  intro he
  have hx := congrArg (fun f : (Fin 1 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ) => f (fun _ => 1) 0) he
  erw [scalarTwo_apply] at hx
  change (2 : ℚ) * 1 = 1 at hx
  norm_num at hx

/-- The scalar transition is nonzero as a linear map.
@isnad1 id=ne.0h0v.s11.6ec9a3b32e87 from=translated src=- shape=fc83a0b3 vocab=0411470c
-/
theorem scalarTwo_nonzero :
    structureMapLinear scalarTwo.toPModule (show (0 : Fin 2) ≤ 1 by decide) ≠ 0 := by
  intro he
  have hx := congrArg (fun f : (Fin 1 → ℚ) →ₗ[ℚ] (Fin 1 → ℚ) => f (fun _ => 1) 0) he
  erw [scalarTwo_apply] at hx
  change (2 : ℚ) * 1 = 0 at hx
  norm_num at hx

/-- A matrix endomorphism multiplies every stage by two.-/
def doubleHom : MatrixSequence.Hom scalarTwo scalarTwo where
  app _ := !![2]
  comm i j h := by
    change (!![2] : Matrix (Fin 1) (Fin 1) ℚ) * !![2] = !![2] * !![2]
    rfl

/-- The stage matrices become the nonidentity natural transformation.
@isnad1 id=ne.0h0v.s7.1184d5da4a21 from=translated src=- shape=7764fd6f vocab=95c82196
-/
theorem doubleHom_nonidentity : doubleHom.toNatTrans ≠ 𝟙 scalarTwo.toPModule := by
  intro he
  have hx := congrArg (fun α : scalarTwo.toPModule ⟶ scalarTwo.toPModule =>
    (α.app 0).hom (fun _ => 1) (0 : Fin 1)) he
  change (doubleHom.app 0).toLin' (fun _ => 1) (0 : Fin 1) = 1 at hx
  change (∑ _ : Fin 1, (2 : ℚ) * 1) = 1 at hx
  norm_num [Fin.sum_univ_succ] at hx

/-- Supplied standard bases instantiate reconstruction through the public API.-/
def suppliedBasisIso :
    scalarTwo.toPModule ≅ (MatrixSequence.ofBases scalarTwo.toPModule scalarTwo.dim
      (fun i => Pi.basisFun ℚ (Fin (scalarTwo.dim i)))).toPModule :=
  MatrixSequence.coordinateIso scalarTwo.toPModule scalarTwo.dim
    (fun i => Pi.basisFun ℚ (Fin (scalarTwo.dim i)))

/-- Standard coordinates recover the original concrete input.
@isnad1 id=eq.0h0v.s5.496c0872ff88 from=translated src=- shape=2b97930f vocab=495ff22a
-/
theorem suppliedBasis_roundTrip :
    MatrixSequence.ofBases scalarTwo.toPModule scalarTwo.dim
      (fun i => Pi.basisFun ℚ (Fin (scalarTwo.dim i))) = scalarTwo :=
  MatrixSequence.ofBases_standard scalarTwo

/-- Morphism coordinates recover the nonidentity input matrices exactly.
@isnad1 id=eq.0h1v.s8.f11ccf5fdc44 from=translated src=- shape=be86725f vocab=c6c6dc60
-/
theorem morphism_roundTrip (i : Fin 2) :
    (MatrixSequence.coordinateHom doubleHom.toNatTrans scalarTwo.dim scalarTwo.dim
      (fun j => Pi.basisFun ℚ (Fin (scalarTwo.dim j)))
      (fun j => Pi.basisFun ℚ (Fin (scalarTwo.dim j)))).app i = doubleHom.app i :=
  MatrixSequence.coordinateHom_standard_app doubleHom i

/-- Swap the middle basis: the inclusion moves to the second coordinate and the projection to the first coordinate.-/
def basisSwapped : MatrixSequence ℚ 3 where
  dim i := match i.val with | 1 => 2 | _ => 1
  step i j _ := match i, j with
    | ⟨0, _⟩, ⟨1, _⟩ => !![0; 1]
    | ⟨1, _⟩, ⟨_ + 2, _⟩ => !![1, 0]
    | _, _ => 0

/-- The transformed adjacent matrices are the transformed inclusion and projection.
@isnad1 id=and.0h0v.s9.9646bcce429a from=translated src=- shape=9bf52b16 vocab=1e439189
-/
theorem basisSwapped_matrices :
    basisSwapped.step 0 1 (by decide) = !![0; 1] ∧
      basisSwapped.step 1 2 (by decide) = !![1, 0] := ⟨rfl, rfl⟩

private def swapTwo : (Fin 2 → ℚ) ≃ₗ[ℚ] (Fin 2 → ℚ) where
  toFun x := ![x 1, x 0]
  invFun x := ![x 1, x 0]
  left_inv x := by ext i; fin_cases i <;> rfl
  right_inv x := by ext i; fin_cases i <;> rfl
  map_add' x y := by ext i; fin_cases i <;> rfl
  map_smul' r x := by ext i; fin_cases i <;> rfl

/-- An explicit invertible coordinate change, nontrivial in the middle fiber.-/
def swapStage (i : Fin 3) :
    (Fin (compositeZero.dim i) → ℚ) ≃ₗ[ℚ] (Fin (basisSwapped.dim i) → ℚ) :=
  match i with
  | ⟨0, _⟩ => LinearEquiv.refl _ _
  | ⟨1, _⟩ => swapTwo
  | ⟨_ + 2, _⟩ => LinearEquiv.refl _ _

/-- The basis change interchanges the middle coordinate vectors.
@isnad1 id=eq.0h0v.s10.db92afe7cc48 from=translated src=- shape=ad80b41e vocab=aaae58b9
-/
theorem swapStage_nontrivial : swapStage 1 ![1, 0] = ![0, 1] := rfl

/-- The explicit coordinate change intertwines the transformed adjacent matrices.
@isnad1 id=eq.1h2v.s12.546624a7f852 from=translated src=- shape=b1e35f19 vocab=62762217
-/
theorem swapStage_comm (i j : Fin 3) (h : i.val + 1 = j.val) :
    (swapStage j).toLinearMap.comp (compositeZero.step i j h).toLin' =
      (basisSwapped.step i j h).toLin'.comp (swapStage i).toLinearMap := by
  fin_cases i <;> fin_cases j <;> simp at h
  · apply LinearMap.ext
    intro x
    funext a
    fin_cases a
    · change ((!![1; 0] : Matrix (Fin 2) (Fin 1) ℚ) *ᵥ x) 1 =
        ((!![0; 1] : Matrix (Fin 2) (Fin 1) ℚ) *ᵥ x) 0
      simp [Matrix.mulVec, dotProduct]
    · change ((!![1; 0] : Matrix (Fin 2) (Fin 1) ℚ) *ᵥ x) 0 =
        ((!![0; 1] : Matrix (Fin 2) (Fin 1) ℚ) *ᵥ x) 1
      simp [Matrix.mulVec, dotProduct]
  · apply LinearMap.ext
    intro x
    funext a
    fin_cases a
    change ((!![0, 1] : Matrix (Fin 1) (Fin 2) ℚ) *ᵥ x) 0 =
      ((!![1, 0] : Matrix (Fin 1) (Fin 2) ℚ) *ᵥ ![x (1 : Fin 2), x (0 : Fin 2)]) 0
    simp [Matrix.mulVec, dotProduct]

/-- A genuine natural isomorphism implements the nontrivial invertible basis change.-/
def basisSwapIso : compositeZero.toPModule ≅ basisSwapped.toPModule :=
  MatrixSequence.isoOfLinearEquiv compositeZero basisSwapped swapStage swapStage_comm

/-- The transformed matrices have exactly the same canonical barcode.
@isnad1 id=eq.0h0v.s4.10226dfc49d3 from=translated src=- shape=8262b056 vocab=7cbe7b5b
-/
theorem basisSwap_barcode : basisSwapped.barcode = compositeZero.barcode :=
  (rankBarcode_eq_of_iso basisSwapIso).symm

end
end TDA.Persistence.MatrixSequenceExamples
