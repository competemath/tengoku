import Tengoku.TdaLib.TDA.Persistence.FiniteLine
import Tengoku.TdaLib.TDA.Persistence.FiniteDecomposition
import Tengoku.Seed.LinearAlgebra.Matrix.ToLin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite based matrix persistence modules

Matrices have target rows and source columns. No injectivity or boundary-map condition is
imposed. All structure maps are chronological products of the adjacent matrices. Supplied
bases give natural coordinate isomorphisms; interval decomposition reuses the existing finite
classification. These theory constructions do not assert executable barcode extraction.
-/

universe u

namespace TDA.Persistence
open CategoryTheory Module Matrix

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Finite dimensions and arbitrary rectangular adjacent transition matrices.-/
@[ext]
structure MatrixSequence (R : Type u) (N : ℕ) where
  dim : Fin N → ℕ
  step : ∀ i j : Fin N, i.val + 1 = j.val → Matrix (Fin (dim j)) (Fin (dim i)) R

namespace MatrixSequence
variable {R : Type u} [CommRing R] {N : ℕ}
noncomputable section

/-- The coordinate module at a stage.-/
def stage (A : MatrixSequence R N) (i : Fin N) : ModuleCat.{u} R :=
  ModuleCat.of R (Fin (A.dim i) → R)

/-- Interpret adjacent matrices as linear maps and extend along the finite line.-/
def toPModule (A : MatrixSequence R N) : PModule.{u,0,u} R (Fin N) :=
  FiniteLine.moduleOfAdjacent A.stage (fun i j h => ModuleCat.ofHom (A.step i j h).toLin')

/--
@isnad1 id=eq.0h4v.s5.23c6c0a9f421 from=translated src=- shape=689ba0da vocab=8b83970c
-/
@[simp] theorem toPModule_obj (A : MatrixSequence R N) (i : Fin N) :
    A.toPModule.obj i = A.stage i := rfl

/-- An adjacent structure map is multiplication by the supplied rectangular matrix.
@isnad1 id=eq.1h5v.s11.addd932e93d8 from=translated src=- shape=91af0580 vocab=2f9f8528
-/
@[simp] theorem structureMapLinear_adjacent (A : MatrixSequence R N)
    (i j : Fin N) (h : i.val + 1 = j.val) :
    structureMapLinear A.toPModule (show i ≤ j by omega) = (A.step i j h).toLin' := by
  unfold structureMapLinear toPModule
  rw [FiniteLine.structureMap_moduleOfAdjacent_adjacent]
  rfl

/-- The composite matrix between any two ordered stages.-/
def compositeMatrix (A : MatrixSequence R N) {i j : Fin N} (h : i ≤ j) :
    Matrix (Fin (A.dim j)) (Fin (A.dim i)) R :=
  LinearMap.toMatrix' (structureMapLinear A.toPModule h)

/--
@isnad1 id=eq.1h5v.s11.53e6d53ef172 from=translated src=- shape=9218b74c vocab=273f43bb
-/
@[simp] theorem toLin_compositeMatrix (A : MatrixSequence R N) {i j : Fin N} (h : i ≤ j) :
    (A.compositeMatrix h).toLin' = structureMapLinear A.toPModule h := by
  exact Matrix.toLin'_toMatrix' _

/-- Apply an arbitrary structure map directly by its chronological composite matrix.
@isnad1 id=eq.1h6v.s9.738b4931bc04 from=translated src=- shape=387635ca vocab=bd73cbbf
-/
theorem structureMapLinear_apply (A : MatrixSequence R N) {i j : Fin N}
    (h : i ≤ j) (x : Fin (A.dim i) → R) :
    structureMapLinear A.toPModule h x = A.compositeMatrix h *ᵥ x := by
  rw [← toLin_compositeMatrix]
  rfl

/--
@isnad1 id=eq.0h4v.s6.43d5fa5723a7 from=translated src=- shape=3c40024a vocab=071225c4
-/
@[simp] theorem compositeMatrix_self (A : MatrixSequence R N) (i : Fin N) :
    A.compositeMatrix (le_refl i) = 1 := by
  unfold compositeMatrix
  rw [structureMapLinear_self, LinearMap.toMatrix'_id]

/--
@isnad1 id=eq.1h5v.s6.c488a454702d from=translated src=- shape=e866f9c2 vocab=b1f75459
-/
@[simp] theorem compositeMatrix_adjacent (A : MatrixSequence R N)
    (i j : Fin N) (h : i.val + 1 = j.val) :
    A.compositeMatrix (show i ≤ j by omega) = A.step i j h := by
  simp [compositeMatrix, structureMapLinear_adjacent A i j h]

/-- Chronological composition: the later matrix multiplies on the left.
@isnad1 id=eq.2h6v.s7.0ded015b5838 from=translated src=- shape=2b540e28 vocab=7f5c1071
-/
theorem compositeMatrix_comp (A : MatrixSequence R N) {i j l : Fin N}
    (hij : i ≤ j) (hjl : j ≤ l) :
    A.compositeMatrix (hij.trans hjl) = A.compositeMatrix hjl * A.compositeMatrix hij := by
  unfold compositeMatrix
  rw [structureMapLinear_comp A.toPModule hij hjl, LinearMap.toMatrix'_comp]
  rfl

/-- One-step recurrence, together with `compositeMatrix_self`, computes every structure map.
@isnad1 id=eq.2h6v.s7.01cf6e72c8e9 from=translated src=- shape=0f288bc2 vocab=f78c9a29
-/
theorem compositeMatrix_succ (A : MatrixSequence R N) {i j l : Fin N}
    (hij : i ≤ j) (hjl : j.val + 1 = l.val) :
    A.compositeMatrix (hij.trans (show j ≤ l by omega)) =
      A.step j l hjl * A.compositeMatrix hij := by
  rw [compositeMatrix_comp A hij (show j ≤ l by omega), compositeMatrix_adjacent A j l hjl]

/-- Stage matrices commuting with adjacent transitions.-/
structure Hom (A B : MatrixSequence R N) where
  app : ∀ i, Matrix (Fin (B.dim i)) (Fin (A.dim i)) R
  comm : ∀ i j (h : i.val + 1 = j.val), B.step i j h * app i = app j * A.step i j h

namespace Hom
variable {A B C : MatrixSequence R N}

/-- Matrix morphisms are determined by their stage matrices.
@isnad1 id=eq.1h6v.s6.4f475310f777 from=translated src=- shape=0d74ad0f vocab=e9e744ed
-/
@[ext] theorem ext {F G : Hom A B} (h : ∀ i, F.app i = G.app i) : F = G := by
  cases F with
  | mk f hf =>
    cases G with
    | mk g hg =>
      have he : f = g := funext h
      cases he
      rfl

/-- Identity matrix morphism.-/
def id (A : MatrixSequence R N) : Hom A A where
  app _ := 1
  comm _ _ _ := by simp

/-- Composition of stage matrices, in chronological order.-/
def comp (F : Hom A B) (G : Hom B C) : Hom A C where
  app i := G.app i * F.app i
  comm i j h := by
    rw [← Matrix.mul_assoc, G.comm i j h, Matrix.mul_assoc, F.comm i j h,
      ← Matrix.mul_assoc]

/--
@isnad1 id=eq.0h4v.s6.797e9074c1fa from=translated src=- shape=bf9ad90d vocab=6c5153aa
-/
@[simp] theorem id_app (A : MatrixSequence R N) (i : Fin N) : (id A).app i = 1 := rfl

/--
@isnad1 id=eq.0h8v.s7.b4974d44f150 from=translated src=- shape=35526384 vocab=e2bc2f46
-/
@[simp] theorem comp_app (F : Hom A B) (G : Hom B C) (i : Fin N) :
    (F.comp G).app i = G.app i * F.app i := rfl

/--
@isnad1 id=eq.0h5v.s5.ac780ae16302 from=translated src=- shape=1acee8d7 vocab=291d6ee0
-/
@[simp] theorem id_comp (F : Hom A B) : (id A).comp F = F := by
  ext i
  simp

/--
@isnad1 id=eq.0h5v.s5.f011ce9f97a9 from=translated src=- shape=3376d402 vocab=291d6ee0
-/
@[simp] theorem comp_id (F : Hom A B) : F.comp (id B) = F := by
  ext i
  simp

/--
@isnad1 id=eq.0h9v.s6.dd807c96947e from=translated src=- shape=0d8fedfd vocab=58610b18
-/
theorem comp_assoc {D : MatrixSequence R N} (F : Hom A B) (G : Hom B C) (H : Hom C D) :
    (F.comp G).comp H = F.comp (G.comp H) := by
  ext i
  simp [Matrix.mul_assoc]

/-- Extend adjacent commuting squares to a genuine natural transformation.-/
def toNatTrans (F : Hom A B) : A.toPModule ⟶ B.toPModule :=
  FiniteLine.homMk (fun i => ModuleCat.ofHom (F.app i).toLin') (by
    intro i j h
    apply ModuleCat.hom_ext
    change (F.app j).toLin'.comp (structureMapLinear A.toPModule _) =
      (structureMapLinear B.toPModule _).comp (F.app i).toLin'
    rw [structureMapLinear_adjacent A i j h, structureMapLinear_adjacent B i j h,
      ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, F.comm i j h])

/--
@isnad1 id=eq.0h6v.s11.beabf0068b24 from=translated src=- shape=3016e002 vocab=25fef0cb
-/
@[simp] theorem toNatTrans_app (F : Hom A B) (i : Fin N) :
    (F.toNatTrans.app i).hom = (F.app i).toLin' := rfl

/--
@isnad1 id=eq.0h3v.s7.62e8f9fb5600 from=translated src=- shape=a3bb4834 vocab=800b1fb1
-/
@[simp] theorem toNatTrans_id (A : MatrixSequence R N) :
    (id A).toNatTrans = 𝟙 A.toPModule := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  change Matrix.toLin' (1 : Matrix (Fin (A.dim i)) (Fin (A.dim i)) R) = LinearMap.id
  exact Matrix.toLin'_one

/--
@isnad1 id=eq.0h7v.s7.93efd5ca4e31 from=translated src=- shape=a3b240e9 vocab=032f3270
-/
@[simp] theorem toNatTrans_comp (F : Hom A B) (G : Hom B C) :
    (F.comp G).toNatTrans = F.toNatTrans ≫ G.toNatTrans := by
  apply NatTrans.ext
  funext i
  apply ModuleCat.hom_ext
  change (G.app i * F.app i).toLin' = (G.app i).toLin'.comp (F.app i).toLin'
  exact Matrix.toLin'_mul _ _

/-- Matrix naturality holds for every composite transition.
@isnad1 id=eq.1h7v.s7.50db971ee701 from=translated src=- shape=ca9fe13a vocab=0cb73297
-/
theorem compositeMatrix_comm (F : Hom A B) {i j : Fin N} (h : i ≤ j) :
    B.compositeMatrix h * F.app i = F.app j * A.compositeMatrix h := by
  apply Matrix.toLin'.injective
  simp only [Matrix.toLin'_mul, toLin_compositeMatrix]
  exact (congrArg (fun f => f.hom) (F.toNatTrans.naturality (homOfLE h))).symm
end Hom

/-- Explicit intertwining stage linear equivalences give a natural isomorphism.-/
def isoOfLinearEquiv (A B : MatrixSequence R N)
    (e : ∀ i, (Fin (A.dim i) → R) ≃ₗ[R] (Fin (B.dim i) → R))
    (he : ∀ i j (h : i.val + 1 = j.val),
      (e j).toLinearMap.comp (A.step i j h).toLin' =
        (B.step i j h).toLin'.comp (e i).toLinearMap) : A.toPModule ≅ B.toPModule :=
  FiniteLine.isoOfAdjacent (fun i => (e i).toModuleIso) (by
    intro i j h
    apply ModuleCat.hom_ext
    change (e j).toLinearMap.comp (structureMapLinear A.toPModule _) =
      (structureMapLinear B.toPModule _).comp (e i).toLinearMap
    rw [structureMapLinear_adjacent A i j h, structureMapLinear_adjacent B i j h]
    exact he i j h)

/-- Coordinates in supplied finite bases, with no choice of bases hidden in the input.-/
def ofBases (M : PModule.{u,0,u} R (Fin N)) (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i)) : MatrixSequence R N where
  dim := d
  step i j h := LinearMap.toMatrix'
    ((b j).equivFun.toLinearMap.comp ((structureMapLinear M (show i ≤ j by omega)).comp
      (b i).equivFun.symm.toLinearMap))

/--
@isnad1 id=eq.0h6v.s7.281aa530486b from=translated src=- shape=7e854ad2 vocab=80251d3b
-/
@[simp] theorem ofBases_dim (M : PModule.{u,0,u} R (Fin N)) (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i)) (i : Fin N) :
    (ofBases M d b).dim i = d i := rfl

/-- The supplied-basis matrix is the usual matrix of the original adjacent map.
@isnad1 id=eq.1h7v.s11.fa6614a0b849 from=translated src=- shape=427304cc vocab=831d2c86
-/
theorem ofBases_step (M : PModule.{u,0,u} R (Fin N)) (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i)) (i j : Fin N)
    (h : i.val + 1 = j.val) :
    (ofBases M d b).step i j h =
      LinearMap.toMatrix (b i) (b j) (structureMapLinear M (show i ≤ j by omega)) := rfl

/-- Coordinate transition matrices evaluate by conjugating the original linear maps.
@isnad1 id=eq.1h7v.s12.f2abadaafa66 from=translated src=- shape=01041542 vocab=7e362836
-/
@[simp] theorem ofBases_step_toLin (M : PModule.{u,0,u} R (Fin N)) (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i)) (i j : Fin N)
    (h : i.val + 1 = j.val) :
    ((ofBases M d b).step i j h).toLin' =
      (b j).equivFun.toLinearMap.comp ((structureMapLinear M (show i ≤ j by omega)).comp
        (b i).equivFun.symm.toLinearMap) := by
  exact Matrix.toLin'_toMatrix' _

/-- Supplied coordinates recover the entire persistence module naturally.-/
def coordinateIso (M : PModule.{u,0,u} R (Fin N)) (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i)) : M ≅ (ofBases M d b).toPModule :=
  FiniteLine.isoOfAdjacent (fun i => (b i).equivFun.toModuleIso) (by
    intro i j h
    apply ModuleCat.hom_ext
    change (b j).equivFun.toLinearMap.comp (structureMapLinear M _) =
      (structureMapLinear (ofBases M d b).toPModule _).comp (b i).equivFun.toLinearMap
    rw [structureMapLinear_adjacent _ i j h, ofBases_step_toLin]
    apply LinearMap.ext
    intro x
    change (b j).equivFun ((structureMapLinear M _) x) =
      (b j).equivFun ((structureMapLinear M _) ((b i).equivFun.symm ((b i).equivFun x)))
    rw [LinearEquiv.symm_apply_apply])

/--
@isnad1 id=eq.0h6v.s9.17fef80a62a0 from=translated src=- shape=a57ec6ad vocab=73112327
-/
@[simp] theorem coordinateIso_hom_app (M : PModule.{u,0,u} R (Fin N)) (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i)) (i : Fin N) :
    ((coordinateIso M d b).hom.app i).hom = (b i).equivFun.toLinearMap := rfl

/--
@isnad1 id=eq.0h6v.s10.6fa3eb8c2ae4 from=translated src=- shape=906015af vocab=28222faf
-/
@[simp] theorem coordinateIso_inv_app (M : PModule.{u,0,u} R (Fin N)) (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i)) (i : Fin N) :
    ((coordinateIso M d b).inv.app i).hom = (b i).equivFun.symm.toLinearMap := rfl

/-- Every structure map, including long composites, is conjugated by supplied coordinates.
@isnad1 id=eq.1h7v.s10.ee1e889135ba from=translated src=- shape=34ff7a1b vocab=ad6bb30e
-/
theorem coordinateIso_naturality (M : PModule.{u,0,u} R (Fin N)) (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i)) {i j : Fin N} (h : i ≤ j) :
    (b j).equivFun.toLinearMap.comp (structureMapLinear M h) =
      (structureMapLinear (ofBases M d b).toPModule h).comp (b i).equivFun.toLinearMap :=
  congrArg (fun f => f.hom) ((coordinateIso M d b).hom.naturality (homOfLE h))

/-- A change of supplied bases acts through a genuine natural isomorphism.-/
def basisChangeIso (M : PModule.{u,0,u} R (Fin N)) (d e : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i))
    (c : ∀ i, Basis (Fin (e i)) R (M.obj i)) :
    (ofBases M d b).toPModule ≅ (ofBases M e c).toPModule :=
  (coordinateIso M d b).symm ≪≫ coordinateIso M e c

/-- The component of a basis change is the coordinate change.
@isnad1 id=eq.0h8v.s10.4583b65d7b44 from=translated src=- shape=800a1842 vocab=0ffb832b
-/
@[simp] theorem basisChangeIso_hom_app (M : PModule.{u,0,u} R (Fin N)) (d e : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) R (M.obj i))
    (c : ∀ i, Basis (Fin (e i)) R (M.obj i)) (i : Fin N) :
    ((basisChangeIso M d e b c).hom.app i).hom =
      (c i).equivFun.toLinearMap.comp (b i).equivFun.symm.toLinearMap := rfl

/-- Standard coordinates return the supplied adjacent matrices exactly.
@isnad1 id=eq.0h3v.s5.cfa19b1e909c from=translated src=- shape=4a2b4b5a vocab=63eb2402
-/
@[simp] theorem ofBases_standard (A : MatrixSequence R N) :
    ofBases A.toPModule A.dim (fun i => Pi.basisFun R (Fin (A.dim i))) = A := by
  cases A with
  | mk d s =>
    change MatrixSequence.mk d _ = MatrixSequence.mk d s
    congr 1
    funext i j h
    dsimp [ofBases]
    rw [Pi.basisFun_equivFun, Pi.basisFun_equivFun]
    change LinearMap.toMatrix' (structureMapLinear (MatrixSequence.mk d s).toPModule _) = s i j h
    rw [structureMapLinear_adjacent _ i j h]
    change LinearMap.toMatrix' (s i j h).toLin' = s i j h
    exact LinearMap.toMatrix'_toLin' _

/-- Matrix coordinates of a natural transformation in supplied bases.-/
def coordinateHom {M L : PModule.{u,0,u} R (Fin N)} (α : M ⟶ L)
    (d e : Fin N → ℕ) (b : ∀ i, Basis (Fin (d i)) R (M.obj i))
    (c : ∀ i, Basis (Fin (e i)) R (L.obj i)) : Hom (ofBases M d b) (ofBases L e c) where
  app i := LinearMap.toMatrix' ((c i).equivFun.toLinearMap.comp
    ((α.app i).hom.comp (b i).equivFun.symm.toLinearMap))
  comm i j h := by
    apply Matrix.toLin'.injective
    simp only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', ofBases_step_toLin]
    have hn := congrArg (fun f => f.hom) (α.naturality (homOfLE (show i ≤ j by omega)))
    apply LinearMap.ext
    intro x
    have hx := congrArg (fun f : M.obj i →ₗ[R] L.obj j => f ((b i).equivFun.symm x)) hn
    change (c j).equivFun ((structureMapLinear L _)
      ((c i).equivFun.symm ((c i).equivFun ((α.app i).hom ((b i).equivFun.symm x))))) =
      (c j).equivFun ((α.app j).hom ((b j).equivFun.symm
        ((b j).equivFun ((structureMapLinear M _) ((b i).equivFun.symm x)))))
    rw [LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]
    exact congrArg (c j).equivFun hx.symm

/-- Coordinate conversion of morphisms agrees with conjugation by the natural coordinate isos.
@isnad1 id=eq.0h9v.s9.604b7e73d958 from=translated src=- shape=ae54984f vocab=51d608e9
-/
theorem coordinateHom_toNatTrans {M L : PModule.{u,0,u} R (Fin N)} (α : M ⟶ L)
    (d e : Fin N → ℕ) (b : ∀ i, Basis (Fin (d i)) R (M.obj i))
    (c : ∀ i, Basis (Fin (e i)) R (L.obj i)) :
    (coordinateHom α d e b c).toNatTrans =
      (coordinateIso M d b).inv ≫ α ≫ (coordinateIso L e c).hom := by
  ext i x
  change (Matrix.toLin' (LinearMap.toMatrix' _)) x = _
  rw [Matrix.toLin'_toMatrix']
  rfl

/-- Morphism coordinates in the standard bases return each original stage matrix.
@isnad1 id=eq.0h6v.s7.70d65954b434 from=translated src=- shape=e8c2203c vocab=e400ab65
-/
@[simp] theorem coordinateHom_standard_app {A B : MatrixSequence R N} (F : Hom A B)
    (i : Fin N) :
    (coordinateHom F.toNatTrans A.dim B.dim
      (fun j => Pi.basisFun R (Fin (A.dim j)))
      (fun j => Pi.basisFun R (Fin (B.dim j)))).app i = F.app i := by
  dsimp [coordinateHom]
  rw [Pi.basisFun_equivFun, Pi.basisFun_equivFun]
  change LinearMap.toMatrix' (F.app i).toLin' = F.app i
  exact LinearMap.toMatrix'_toLin' _

section Field
variable {k : Type u} [Field k]

/--
@isnad1 id=finitedi.0h4v.s7.e4bf501f35c8 from=translated src=- shape=69240382 vocab=334289b8
-/
instance toPModule_finiteDimensional (A : MatrixSequence k N) (i : Fin N) :
    FiniteDimensional k (A.toPModule.obj i) := by
  change FiniteDimensional k (Fin (A.dim i) → k)
  infer_instance

/-- The canonical finite barcode, retaining interval multiplicities and half-open endpoints.-/
def barcode (A : MatrixSequence k N) : Multiset (FiniteInterval N) := rankBarcode A.toPModule

/-- Existing finite decomposition applied to the matrix representation. A death at `N` means
survival to the final observed stage; no infinite continuation is asserted.-/
def decompositionIso (A : MatrixSequence k N) :
    A.toPModule ≅ barcodeModule (k := k) A.barcode := rankBarcodeIso A.toPModule

/-- Supplied finite bases give an interval decomposition without a separate dimension instance.-/
def decompositionIsoOfBases (M : PModule.{u,0,u} k (Fin N)) (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) k (M.obj i)) :
    M ≅ barcodeModule (k := k) (ofBases M d b).barcode :=
  coordinateIso M d b ≪≫ (ofBases M d b).decompositionIso

/-- Intertwining coordinate equivalences preserve the canonical barcode.
@isnad1 id=eq.1h5v.s12.95e45c8c44c1 from=translated src=- shape=e47b1719 vocab=45d5073a
-/
theorem barcode_eq_of_linearEquiv (A B : MatrixSequence k N)
    (e : ∀ i, (Fin (A.dim i) → k) ≃ₗ[k] (Fin (B.dim i) → k))
    (he : ∀ i j (h : i.val + 1 = j.val),
      (e j).toLinearMap.comp (A.step i j h).toLin' =
        (B.step i j h).toLin'.comp (e i).toLinearMap) : A.barcode = B.barcode :=
  rankBarcode_eq_of_iso (isoOfLinearEquiv A B e he)

/-- The supplied-basis representation has the original module’s canonical barcode.
@isnad1 id=eq.0h5v.s8.e0f25e18d408 from=translated src=- shape=27944356 vocab=31b18028
-/
theorem barcode_ofBases (M : PModule.{u,0,u} k (Fin N))
    [∀ i, FiniteDimensional k (M.obj i)] (d : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) k (M.obj i)) :
    (ofBases M d b).barcode = rankBarcode M :=
  (rankBarcode_eq_of_iso (coordinateIso M d b)).symm

/-- Barcode invariance under arbitrary supplied basis changes.
@isnad1 id=eq.0h7v.s8.01440f03d5db from=translated src=- shape=7e927614 vocab=415c90e7
-/
theorem barcode_basisChange (M : PModule.{u,0,u} k (Fin N)) (d e : Fin N → ℕ)
    (b : ∀ i, Basis (Fin (d i)) k (M.obj i))
    (c : ∀ i, Basis (Fin (e i)) k (M.obj i)) :
    (ofBases M d b).barcode = (ofBases M e c).barcode :=
  rankBarcode_eq_of_iso (basisChangeIso M d e b c)
end Field
end
end MatrixSequence
end TDA.Persistence
