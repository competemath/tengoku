import Tengoku
import Tengoku.OpenaiMath.OAI.Probability.CoordinateSweeps.Decomposition
import Tengoku.OpenaiMath.OAI.RepresentationTheory.SignedTensor.Resolution

namespace OAI

noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexConjugate Matrix.Norms.L2Operator
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ComplexOrder MatrixOrder
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators ENNReal
open MeasureTheory
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
attribute [local instance] Classical.propDecidable
noncomputable section
attribute [local instance] Classical.propDecidable
noncomputable section
open Set Complex
open scoped BigOperators Topology
open scoped Matrix.Norms.L2Operator
noncomputable section
open scoped BigOperators Matrix.Norms.L2Operator ComplexOrder
namespace CoordinateSweeps.Grid.Holes
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma onLine_row_iff (j : Fin A.b) (L : A.Line j) (y : B.Slot) (i : Fin h) :
    H.OnLine (Fin.castAdd B.b j) (rowLines A B j (L,y)) i ↔
      H.rowOf i=y ∧ (fun k : {k : Fin A.b // k≠j} =>
        (splitSlots A B (H.path i (prefixTime A B j.castSucc))).1 k.val)=L := by
  have hh := rowLines_evaluation A B j (H.path i (prefixTime A B j.castSucc))
  constructor
  · intro hi
    have he := congrArg (rowLines A B j).symm hi
    change (rowLines A B j).symm (fun k => H.path i (prefixTime A B j.castSucc) k.val)=
      (rowLines A B j).symm (rowLines A B j (L,y)) at he
    rw [hh,Equiv.symm_apply_apply] at he
    exact ⟨(H.row_constant i j.castSucc).symm.trans (congrArg Prod.snd he),congrArg Prod.fst he⟩
  · rintro ⟨hi,hl⟩
    apply (rowLines A B j).symm.injective
    change (rowLines A B j).symm (fun k => H.path i (prefixTime A B j.castSucc) k.val)=
      (rowLines A B j).symm (rowLines A B j (L,y))
    rw [hh,Equiv.symm_apply_apply]
    exact Prod.ext hl ((H.row_constant i j.castSucc).trans hi)

lemma onLine_column_iff (j : Fin B.b) (x : A.Slot) (L : B.Line j) (i : Fin h) :
    H.OnLine (Fin.natAdd A.b j) (columnLines A B j (x,L)) i ↔
      H.columnOf i=x ∧ (fun k : {k : Fin B.b // k≠j} =>
        (splitSlots A B (H.path i (suffixTime A B j.castSucc))).2 k.val)=L := by
  have hh := columnLines_evaluation A B j (H.path i (suffixTime A B j.castSucc))
  constructor
  · intro hi
    have he := congrArg (columnLines A B j).symm hi
    change (columnLines A B j).symm (fun k => H.path i (suffixTime A B j.castSucc) k.val)=
      (columnLines A B j).symm (columnLines A B j (x,L)) at he
    rw [hh,Equiv.symm_apply_apply] at he
    exact ⟨(H.column_constant i j.castSucc).symm.trans (congrArg Prod.fst he),congrArg Prod.snd he⟩
  · rintro ⟨hi,hl⟩
    apply (columnLines A B j).symm.injective
    change (columnLines A B j).symm (fun k => H.path i (suffixTime A B j.castSucc) k.val)=
      (columnLines A B j).symm (columnLines A B j (x,L))
    rw [hh,Equiv.symm_apply_apply]
    exact Prod.ext ((H.column_constant i j.castSucc).trans hi) hl

def rowOnLineEquiv (j : Fin A.b) (L : A.Line j) (y : B.Slot) :
    {k : Fin (H.rowCount y) // (H.rowHoles y).OnLine j L k} ≃
      {i : Fin h // H.OnLine (Fin.castAdd B.b j) (rowLines A B j (L,y)) i} where
  toFun k := ⟨(H.rowCards y k.val).val,(H.onLine_row_iff j L y _).mpr
    ⟨(H.rowCards y k.val).property,k.property⟩⟩
  invFun i := ⟨(H.rowCards y).symm ⟨i.val,((H.onLine_row_iff j L y _).mp i.property).1⟩,by
    change (fun (k : {k : Fin A.b // k ≠ j}) => (splitSlots A B (H.path
      (H.rowCards y ((H.rowCards y).symm _)).val (prefixTime A B j.castSucc))).1 k.val)=L
    simp only [Equiv.apply_symm_apply]
    exact ((H.onLine_row_iff j L y _).mp i.property).2⟩
  left_inv k := by
    apply Subtype.ext
    apply (H.rowCards y).injective
    simp only [Equiv.apply_symm_apply]
  right_inv i := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]

def columnOnLineEquiv (j : Fin B.b) (x : A.Slot) (L : B.Line j) :
    {k : Fin (H.columnCount x) // (H.columnHoles x).OnLine j L k} ≃
      {i : Fin h // H.OnLine (Fin.natAdd A.b j) (columnLines A B j (x,L)) i} where
  toFun k := ⟨(H.columnCards x k.val).val,(H.onLine_column_iff j x L _).mpr
    ⟨(H.columnCards x k.val).property,k.property⟩⟩
  invFun i := ⟨(H.columnCards x).symm ⟨i.val,((H.onLine_column_iff j x L _).mp i.property).1⟩,by
    change (fun (k : {k : Fin B.b // k ≠ j}) => (splitSlots A B (H.path
      (H.columnCards x ((H.columnCards x).symm _)).val (suffixTime A B j.castSucc))).2 k.val)=L
    simp only [Equiv.apply_symm_apply]
    exact ((H.onLine_column_iff j x L _).mp i.property).2⟩
  left_inv k := by
    apply Subtype.ext
    apply (H.columnCards x).injective
    simp only [Equiv.apply_symm_apply]
  right_inv i := by
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply]

lemma lineCount_row (j : Fin A.b) (L : A.Line j) (y : B.Slot) :
    H.lineCount (Fin.castAdd B.b j) (rowLines A B j (L,y))=(H.rowHoles y).lineCount j L := by
  exact (H.card_onLine _ _).symm.trans ((Fintype.card_congr (H.rowOnLineEquiv j L y)).symm.trans
    ((H.rowHoles y).card_onLine j L))
lemma lineCount_column (j : Fin B.b) (x : A.Slot) (L : B.Line j) :
    H.lineCount (Fin.natAdd A.b j) (columnLines A B j (x,L))=(H.columnHoles x).lineCount j L := by
  exact (H.card_onLine _ _).symm.trans ((Fintype.card_congr (H.columnOnLineEquiv j x L)).symm.trans
    ((H.columnHoles x).card_onLine j L))

/- One head stage contributes exactly the sum of its child row potentials. -/
lemma cost_stage_row (j : Fin A.b) :
    (∑ L : (concat A B).Line (Fin.castAdd B.b j),
      Real.log (((2 ^ (concat A B).bits (Fin.castAdd B.b j) : ℕ) : ℝ) ^
          H.lineCount (Fin.castAdd B.b j) L /
        ((2 ^ (concat A B).bits (Fin.castAdd B.b j)).descFactorial
          (H.lineCount (Fin.castAdd B.b j) L) : ℝ)))=
      ∑ y : B.Slot, ∑ L : A.Line j,
        Real.log (((2^A.bits j : ℕ) : ℝ)^(H.rowHoles y).lineCount j L /
          ((2^A.bits j).descFactorial ((H.rowHoles y).lineCount j L) : ℝ)) := by
  rw [← (rowLines A B j).sum_comp,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro L _
  rw [H.lineCount_row,concat_bits_left]

lemma cost_stage_column (j : Fin B.b) :
    (∑ L : (concat A B).Line (Fin.natAdd A.b j),
      Real.log (((2 ^ (concat A B).bits (Fin.natAdd A.b j) : ℕ) : ℝ) ^
          H.lineCount (Fin.natAdd A.b j) L /
        ((2 ^ (concat A B).bits (Fin.natAdd A.b j)).descFactorial
          (H.lineCount (Fin.natAdd A.b j) L) : ℝ)))=
      ∑ x : A.Slot, ∑ L : B.Line j,
        Real.log (((2^B.bits j : ℕ) : ℝ)^(H.columnHoles x).lineCount j L /
          ((2^B.bits j).descFactorial ((H.columnHoles x).lineCount j L) : ℝ)) := by
  rw [← (columnLines A B j).sum_comp,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro L _
  rw [H.lineCount_column,concat_bits_right]

/- No conditioning cost is discarded in the induction split. -/
theorem cost_split : H.cost=(∑ y, (H.rowHoles y).cost)+(∑ x, (H.columnHoles x).cost) := by
  unfold cost
  erw [Fin.sum_univ_add]
  congr 1
  · trans ∑ j : Fin A.b, ∑ y : B.Slot, ∑ L : A.Line j,
      Real.log (((2^A.bits j : ℕ) : ℝ)^(H.rowHoles y).lineCount j L /
        ((2^A.bits j).descFactorial ((H.rowHoles y).lineCount j L) : ℝ))
    · apply Finset.sum_congr rfl
      intro j _
      convert H.cost_stage_row j using 1
      congr 3
      exact Subsingleton.elim _ _
    · exact Finset.sum_comm
  · trans ∑ j : Fin B.b, ∑ x : A.Slot, ∑ L : B.Line j,
      Real.log (((2^B.bits j : ℕ) : ℝ)^(H.columnHoles x).lineCount j L /
        ((2^B.bits j).descFactorial ((H.columnHoles x).lineCount j L) : ℝ))
    · apply Finset.sum_congr rfl
      intro j _
      convert H.cost_stage_column j using 1
      congr 3
      exact Subsingleton.elim _ _
    · exact Finset.sum_comm

end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open FiberBlocks SignedTensor UnitaryIrrep
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)

lemma row_column_index_injective : Function.Injective (fun x : H.JunctionFree => (H.rowIndex x,H.columnIndex x)) := by
  intro x y he
  apply Subtype.ext
  apply (splitSlots A B).injective
  exact Prod.ext ((Fintype.equivFin A.Slot).injective (congrArg Prod.snd he))
    ((Fintype.equivFin B.Slot).injective (congrArg Prod.fst he))

lemma row_entropy_sum {p : ℕ} (α : BlockType (FiberBlocks.size H.rowIndex) p) (c e : ℝ) :
    (∑ i, (-c*Real.log (activeIrrep (α i)).dimension+
      e*H.rowCount (H.rowSite i)*Real.log A.size-(H.rowHoles (H.rowSite i)).cost))=
      -c*blockEntropy α+e*h*Real.log A.size-∑ y, (H.rowHoles y).cost := by
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
    blockEntropy]
  have hc : (∑ i, (H.rowCount (H.rowSite i) : ℝ))=h := by
    rw [← Nat.cast_sum]
    congr 1
    exact ((Fintype.equivFin B.Slot).symm.sum_comp H.rowCount).trans H.sum_rowCount
  rw [hc]
  congr 1
  exact (Fintype.equivFin B.Slot).symm.sum_comp (fun y => (H.rowHoles y).cost)

lemma column_entropy_sum {p : ℕ} (β : BlockType (FiberBlocks.size H.columnIndex) p) (c e : ℝ) :
    (∑ i, (-c*Real.log (activeIrrep (β i)).dimension+
      e*H.columnCount (H.columnSite i)*Real.log B.size-(H.columnHoles (H.columnSite i)).cost))=
      -c*blockEntropy β+e*h*Real.log B.size-∑ x, (H.columnHoles x).cost := by
  simp only [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.sum_mul,
    blockEntropy]
  have hc : (∑ i, (H.columnCount (H.columnSite i) : ℝ))=h := by
    rw [← Nat.cast_sum]
    congr 1
    exact ((Fintype.equivFin A.Slot).symm.sum_comp H.columnCount).trans H.sum_columnCount
  rw [hc]
  congr 1
  exact (Fintype.equivFin A.Slot).symm.sum_comp (fun x => (H.columnHoles x).cost)

variable (p : ℕ) (eF : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree)
    (hf : H.Feasible) (z : ℝ) (q : ℕ) (hq : 0 < q) (c e : ℝ) (s : ℕ)
/- Exact row/column induction estimate on the literal free junction board.
Only smaller-grid conditional estimates enter as hypotheses. -/
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep SignedTensor YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
def junctionChart (hf : H.Feasible) (e : Fin (Fintype.card H.JunctionFree) ≃ H.JunctionFree) :
    H.stabilizer ≃* Equiv.Perm (Fin (Fintype.card H.JunctionFree)) :=
  (H.junctionEquiv hf).trans (H.junctionFreeEquiv.trans e.symm.permCongrHom)

/- The exact projected tensor moment on the literal junction board equals
its genuine Hom multiplicity times the main theorem's conditional moment. -/

/- Hook occurrence removes the multiplicity without normalizing the trace. -/
end CoordinateSweeps.Grid.Holes

namespace CoordinateSweeps.Grid.Holes
open UnitaryIrrep SignedTensor YoungCorner
variable {A B : Grid} {h : ℕ} (H : (concat A B).Holes h)
end CoordinateSweeps.Grid.Holes
end
end
end
end
end
end
end
end
end
end

open scoped Matrix.Norms.L2Operator

end OAI
