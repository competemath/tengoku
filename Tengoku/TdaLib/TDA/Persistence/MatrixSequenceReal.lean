import Tengoku.TdaLib.TDA.Persistence.MatrixSequence
import Tengoku.TdaLib.TDA.Persistence.ConstructibleRefinementBarcode

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Real critical values for finite matrix persistence

A padded matrix sequence has a zero initial stage followed by the observations at the
supplied critical values. Pullback along `cellIndex` supplies a zero left tail and an
explicitly constant last cell. Its real barcode retains the original critical values.
The construction uses the existing finite-constructible reconstruction and decomposition.
-/

universe u

set_option backward.isDefEq.respectTransparency false

namespace TDA.Persistence.MatrixSequence

open CategoryTheory CategoryTheory.Limits FiniteConstructible

variable {k : Type u} [Field k] {n m : ℕ}

noncomputable section

/-- Extend the supplied finite observations through the cells of the real grid.
The initial stage is the entire left tail, so constructibility requires it to be zero.-/
def realModule (A : MatrixSequence k (n + 1)) (c : Fin n ↪o ℝ) :
    PModule.{u,0,u} k ℝ := reindex (cellIndex c) A.toPModule

/-- Evaluation selects the coordinate space of the grid cell containing the real parameter.
@isnad1 id=eq.0h5v.s7.9e6e37902daf from=translated src=- shape=b7f37f73 vocab=39e121c2
-/
@[simp] theorem realModule_obj (A : MatrixSequence k (n + 1))
    (c : Fin n ↪o ℝ) (t : ℝ) :
    (A.realModule c).obj t = A.stage (cellIndex c t) := rfl

/-- Every real structure map is the chronological matrix product between its selected cells.
@isnad1 id=eq.1h6v.s14.8c759aad50d3 from=translated src=- shape=5bf7705a vocab=9515f27c
-/
theorem realModule_structureMapLinear (A : MatrixSequence k (n + 1))
    (c : Fin n ↪o ℝ) {s t : ℝ} (h : s ≤ t) :
    structureMapLinear (A.realModule c) h =
      (A.compositeMatrix ((cellIndex c).monotone h)).toLin' := by
  exact (A.toLin_compositeMatrix _).symm

/-- A critical value is included in its new, positive-indexed cell.
@isnad1 id=eq.0h5v.s6.eed148b2bd2f from=translated src=- shape=d70e7f8c vocab=560c201c
-/
@[simp] theorem realModule_obj_critical (A : MatrixSequence k (n + 1))
    (c : Fin n ↪o ℝ) (i : Fin n) :
    (A.realModule c).obj (c i) = A.stage i.succ := by
  rw [realModule_obj, cellIndex_critical]

/-- Every real fiber is one of the finite coordinate spaces.
@isnad1 id=finitedi.0h5v.s7.847a193d1d21 from=translated src=- shape=f31dd751 vocab=0fc83708
-/
instance realModule_finiteDimensional (A : MatrixSequence k (n + 1))
    (c : Fin n ↪o ℝ) (t : ℝ) : FiniteDimensional k ((A.realModule c).obj t) := by
  change FiniteDimensional k (A.toPModule.obj (cellIndex c t))
  infer_instance

/-- Zero initial coordinates give the zero stage required by reconstruction.
@isnad1 id=iszero.1h3v.s7.f432f0051e3c from=translated src=- shape=5d5793af vocab=931d851b
-/
theorem isZero_initial (A : MatrixSequence k (n + 1)) (hA : A.dim 0 = 0) :
    IsZero (A.toPModule.obj 0) := by
  have : Subsingleton (A.toPModule.obj 0) := by
    change Subsingleton (Fin (A.dim 0) → k)
    rw [hA]
    infer_instance
  exact ModuleCat.isZero_of_subsingleton _

/-- The grid extension has the existing left-zero, half-open constructibility contract.
@isnad1 id=isconstr.1h4v.s6.e4d2b0fe9130 from=translated src=- shape=d7396bbd vocab=5c6b7005
-/
theorem realModule_isConstructible (A : MatrixSequence k (n + 1))
    (c : Fin n ↪o ℝ) (hA : A.dim 0 = 0) : IsConstructible c (A.realModule c) :=
  isConstructible_reindex c A.toPModule (A.isZero_initial hA)

private theorem criticalIndex (c : Fin n ↪o ℝ) :
    (cellIndex c).comp c.toOrderHom = (Fin.succOrderEmb n).toOrderHom := by
  apply DFunLike.ext
  intro i
  exact cellIndex_critical c i

/-- Restricting the real extension to its critical values recovers the positive stages,
including every structure map.-/
def criticalSampleIso (A : MatrixSequence k (n + 1)) (c : Fin n ↪o ℝ) :
    reindex c.toOrderHom (A.realModule c) ≅
      reindex (Fin.succOrderEmb n).toOrderHom A.toPModule :=
  eqToIso (by rw [realModule, reindex_comp, criticalIndex])

/-- The existing real endpoint diagram of the matrix observations.-/
def realDiagram (A : MatrixSequence k (n + 1)) (c : Fin n ↪o ℝ) : Diagram ℝ :=
  moduleDiagram c (A.realModule c) (fun _ => inferInstance)

/-- Real endpoints are obtained from the barcode of the positive observed stages.
In particular, the critical values are retained instead of their ordinal labels.
@isnad1 id=eq.0h4v.s7.a16d326c7a07 from=translated src=- shape=29b47180 vocab=85ca049d
-/
theorem realDiagram_eq_ofIndexBars (A : MatrixSequence k (n + 1)) (c : Fin n ↪o ℝ) :
    A.realDiagram c = ofIndexBars c c.strictMono
      (rankBarcode (reindex (Fin.succOrderEmb n).toOrderHom A.toPModule)) := by
  letI : ∀ i : Fin n, FiniteDimensional k
      ((reindex c.toOrderHom (A.realModule c)).obj i) := fun i =>
    show FiniteDimensional k ((A.realModule c).obj (c i)) from inferInstance
  letI : ∀ i : Fin n, FiniteDimensional k
      ((reindex (Fin.succOrderEmb n).toOrderHom A.toPModule).obj i) := fun i =>
    show FiniteDimensional k (A.toPModule.obj i.succ) from inferInstance
  unfold realDiagram moduleDiagram
  rw [rankBarcode_eq_of_iso (A.criticalSampleIso c)]

/-- The matrix extension is naturally isomorphic to its real endpoint realization.-/
def realBarcodeIso (A : MatrixSequence k (n + 1)) (c : Fin n ↪o ℝ)
    (hA : A.dim 0 = 0) :
    A.realModule c ≅ RealBarcode.realize (k := k) (A.realDiagram c) :=
  barcodeRealizationIso c (A.realModule c) (A.realModule_isConstructible c hA)
    (fun _ => inferInstance)

/-- Inserting critical observations changes neither real endpoints nor multiplicities.
@isnad1 id=eq.2h6v.s8.3da0528e288f from=translated src=- shape=ef7e8cae vocab=cd149520
-/
theorem realDiagram_refinement (A : MatrixSequence k (n + 1))
    (c : Fin n ↪o ℝ) (d : Fin m ↪o ℝ) (hA : A.dim 0 = 0) (h : Refines c d) :
    moduleDiagram d (A.realModule c) (fun _ => inferInstance) = A.realDiagram c :=
  moduleDiagram_refinement (A.realModule c) h (A.realModule_isConstructible c hA)
    (fun _ => inferInstance)

end
end TDA.Persistence.MatrixSequence
