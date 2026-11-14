import Tengoku.TdaLib.TDA.Persistence.Reduction.ColumnReduction
import Tengoku.Seed.Data.List.FinRange
import Tengoku.Seed.Algebra.BigOperators.Fin

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms matrixReductionTrace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixReductionTrace_step_spec` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixReductionTrace_pivots_distinct` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixReductionTrace_length_le` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixReductionTrace_respectsDegree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixReductionTrace_certificate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms matrixReductionTrace_graded_certificate` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Chronological all-column reduction

The traversal applies the existing deterministic single-column reducer to each current
matrix in index order. The prefix invariant tracks untouched future columns, distinct
completed pivots and the original-height operation budget. No square-zero or grading
assumption is needed for reduction. Certificates reuse the trace algebra.
-/

namespace TDA.Persistence.Reduction

open scoped BigOperators

variable {m : ℕ} {k : Type*} [Field k] [DecidableEq k]

private def matrixReductionTraceAux :
    Matrix (Fin m) (Fin m) k → List (Fin m) → List (EarlierColumnOp m k)
  | _, [] => []
  | M, j :: js =>
      let ops := columnReductionTrace M j
      ops ++ matrixReductionTraceAux (replay M ops) js

/-- Reduce each column against the current earlier columns in chronological order.-/
def matrixReductionTrace (M : Matrix (Fin m) (Fin m) k) :
    List (EarlierColumnOp m k) :=
  matrixReductionTraceAux M (List.finRange m)

private theorem matrixReductionTraceAux_append
    (M : Matrix (Fin m) (Fin m) k) (xs ys : List (Fin m)) :
    matrixReductionTraceAux M (xs ++ ys) =
      matrixReductionTraceAux M xs ++
        matrixReductionTraceAux (replay M (matrixReductionTraceAux M xs)) ys := by
  induction xs generalizing M with
  | nil => simp [matrixReductionTraceAux, replay_nil]
  | cons j js ih =>
      simp only [List.cons_append, matrixReductionTraceAux]
      rw [ih, List.append_assoc, replay_append]

private theorem prefix_succ (M : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (ht : t < m) :
    matrixReductionTraceAux M ((List.finRange m).take (t + 1)) =
      matrixReductionTraceAux M ((List.finRange m).take t) ++
      columnReductionTrace
        (replay M (matrixReductionTraceAux M ((List.finRange m).take t)))
        ⟨t, ht⟩ := by
  have hlen : t < (List.finRange m).length := by simpa using ht
  rw [List.take_succ_eq_append_getElem hlen, matrixReductionTraceAux_append]
  simp only [matrixReductionTraceAux, List.append_nil]
  congr 1
  simp [List.getElem_finRange]

private theorem prefix_state_succ (M : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (ht : t < m) :
    replay M (matrixReductionTraceAux M ((List.finRange m).take (t + 1))) =
      replay (replay M (matrixReductionTraceAux M ((List.finRange m).take t)))
        (columnReductionTrace
          (replay M (matrixReductionTraceAux M ((List.finRange m).take t)))
          ⟨t, ht⟩) := by
  rw [prefix_succ M t ht, replay_append]

private theorem prefix_full (M : Matrix (Fin m) (Fin m) k) :
    matrixReductionTraceAux M ((List.finRange m).take m) = matrixReductionTrace M := by
  have h : (List.finRange m).take m = List.finRange m :=
    List.take_of_length_le (by simp)
  simp [matrixReductionTrace, h]

private theorem matrixReductionTraceAux_prefix_invariant
    (M : Matrix (Fin m) (Fin m) k) (t : ℕ) (ht : t ≤ m) :
    let ops := matrixReductionTraceAux M ((List.finRange m).take t)
    let A := replay M ops
    (∀ op ∈ ops, op.1.j.val < t) ∧
    (∀ q : Fin m, t ≤ q.val → A.col q = M.col q) ∧
    (∀ i j p : Fin m, i.val < t → j.val < t →
      columnPivot (A.col i) = some p →
      columnPivot (A.col j) = some p → i = j) ∧
    ops.length ≤
      (((List.finRange m).take t).map
        (fun j => pivotHeight (columnPivot (M.col j)))).sum := by
  induction t with
  | zero =>
      simp [matrixReductionTraceAux, replay_nil]
  | succ t ih =>
      have hlt : t < m := by omega
      have hle : t ≤ m := by omega
      obtain ⟨hops, hfuture, hpiv, hlen⟩ := ih hle
      let P := matrixReductionTraceAux M ((List.finRange m).take t)
      let A := replay M P
      let j : Fin m := ⟨t, hlt⟩
      let block := columnReductionTrace A j
      have hP : matrixReductionTraceAux M ((List.finRange m).take (t + 1)) =
          P ++ block := prefix_succ M t hlt
      have hA : replay M (matrixReductionTraceAux M ((List.finRange m).take (t + 1))) =
          replay A block := prefix_state_succ M t hlt
      have hsum : (((List.finRange m).take (t + 1)).map
          (fun q => pivotHeight (columnPivot (M.col q)))).sum =
          (((List.finRange m).take t).map
          (fun q => pivotHeight (columnPivot (M.col q)))).sum +
          pivotHeight (columnPivot (M.col j)) := by
        have hh : t < (List.finRange m).length := by simpa using hlt
        rw [List.take_succ_eq_append_getElem hh, List.map_append, List.sum_append]
        simp [j, List.getElem_finRange]
      dsimp
      rw [hP, replay_append, hsum]
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro op hop
        rcases List.mem_append.mp hop with h | h
        · exact Nat.lt_succ_of_lt (hops op h)
        · have hj := columnReductionTrace_target A j op h
          simp [hj, j]
      · intro q hq
        have hne : q ≠ j := by intro heq; subst q; simp [j] at hq
        rw [columnReductionTrace_col_of_ne A j q hne]
        exact hfuture q (by omega)
      · intro i q p hi hq hpi hpq
        have hile : i.val ≤ t := by omega
        have hqle : q.val ≤ t := by omega
        rcases (Nat.lt_or_eq_of_le hile) with hio | hij
        · rcases (Nat.lt_or_eq_of_le hqle) with hqo | hqj
          · have hiNe : i ≠ j := by intro heq; subst i; exact (Nat.lt_irrefl t) hio
            have hqNe : q ≠ j := by intro heq; subst q; exact (Nat.lt_irrefl t) hqo
            rw [columnReductionTrace_col_of_ne A j i hiNe] at hpi
            rw [columnReductionTrace_col_of_ne A j q hqNe] at hpq
            exact hpiv i q p hio hqo hpi hpq
          · have qeq : q = j := Fin.ext hqj
            subst q
            have hiNe : i ≠ j := by intro heq; subst i; exact (Nat.lt_irrefl t) hio
            rw [columnReductionTrace_col_of_ne A j i hiNe] at hpi
            have hij' : i < j := hio
            exact False.elim ((columnReductionTrace_terminal A j i hij' p hpi) hpq)
        · rcases (Nat.lt_or_eq_of_le hqle) with hqo | hqj
          · have ieq : i = j := Fin.ext hij
            subst i
            have hqNe : q ≠ j := by intro heq; subst q; exact (Nat.lt_irrefl t) hqo
            rw [columnReductionTrace_col_of_ne A j q hqNe] at hpq
            have hqj' : q < j := hqo
            exact False.elim ((columnReductionTrace_terminal A j q hqj' p hpq) hpi)
          · exact (Fin.ext (hij.trans hqj.symm))
      · have hlocal := columnReductionTrace_length_le A j
        have hjcol : A.col j = M.col j := hfuture j (by simp [j])
        rw [hjcol] at hlocal
        simpa only [List.length_append, hsum] using Nat.add_le_add hlen hlocal

/-- Present pivots of distinct final columns cannot agree.
@isnad1 id=eq.2h6v.s6.887b4ab7045a from=translated src=- shape=53ac6499 vocab=4493614f
-/
theorem matrixReductionTrace_pivots_distinct
    (M : Matrix (Fin m) (Fin m) k) (i j p : Fin m)
    (hi : columnPivot ((replay M (matrixReductionTrace M)).col i) = some p)
    (hj : columnPivot ((replay M (matrixReductionTrace M)).col j) = some p) :
    i = j := by
  obtain ⟨_, _, hp, _⟩ := matrixReductionTraceAux_prefix_invariant M m (le_refl m)
  rw [prefix_full] at hp
  exact hp i j p i.isLt j.isLt hi hj

/-- The number of emitted operations is bounded by original column heights.
@isnad1 id=le.0h3v.s5.524d5cec2abb from=translated src=- shape=91dd5d5c vocab=86dea8dc
-/
theorem matrixReductionTrace_length_le
    (M : Matrix (Fin m) (Fin m) k) :
    (matrixReductionTrace M).length ≤
      ∑ j : Fin m, pivotHeight (columnPivot (M.col j)) := by
  obtain ⟨_, _, _, hlen⟩ := matrixReductionTraceAux_prefix_invariant M m (le_refl m)
  rw [prefix_full] at hlen
  have htake : (List.finRange m).take m = List.finRange m :=
    List.take_of_length_le (by simp)
  rw [htake] at hlen
  simpa only [Fin.sum_univ_def] using hlen

private theorem matrixReductionTraceAux_respectsDegree
    (degree : Fin m → ℕ) (M : Matrix (Fin m) (Fin m) k)
    (js : List (Fin m)) (hM : LowersDegree degree M) :
    TraceRespectsDegree degree (matrixReductionTraceAux M js) := by
  induction js generalizing M with
  | nil => simp [matrixReductionTraceAux, TraceRespectsDegree]
  | cons j js ih =>
      let block := columnReductionTrace M j
      have hb : TraceRespectsDegree degree block :=
        columnReductionTrace_respectsDegree degree M j hM
      have hM' : LowersDegree degree (replay M block) :=
        replay_lowersDegree degree M block hM hb
      have ht := ih (replay M block) hM'
      intro op hop
      change op ∈ block ++ matrixReductionTraceAux (replay M block) js at hop
      rcases List.mem_append.mp hop with h | h
      · exact hb op h
      · exact ht op h

/-- Every emitted operation joins columns of equal degree.
@isnad1 id=traceres.1h4v.s5.eecd87048e43 from=translated src=- shape=495f4f77 vocab=883be4ea
-/
theorem matrixReductionTrace_respectsDegree
    (degree : Fin m → ℕ) (M : Matrix (Fin m) (Fin m) k)
    (hM : LowersDegree degree M) :
    TraceRespectsDegree degree (matrixReductionTrace M) := by
  exact matrixReductionTraceAux_respectsDegree degree M (List.finRange m) hM

/-- The generated ungraded trace has the existing product, inverse and prefix certificates.
@isnad1 id=other.0h3v.s9.c0ea493360f5 from=translated src=- shape=dfa1dfcd vocab=faf367d4
-/
theorem matrixReductionTrace_certificate
    (M : Matrix (Fin m) (Fin m) k) :
    let ops := matrixReductionTrace M
    let R := replay M ops
    let V := traceChange ops
    let W := traceChangeInv ops
    R = M * V ∧ V * W = 1 ∧ W * V = 1 ∧
    V.IsUpperTriangular ∧ (∀ i, V i i = 1) ∧
    W.IsUpperTriangular ∧ (∀ i, W i i = 1) ∧
    replay R (inverseTrace ops) = M ∧
    (∀ s : ℕ, prefixSpan R s = prefixSpan M s) := by
  let ops := matrixReductionTrace M
  exact ⟨replay_eq_mul_traceChange M ops,
    traceChange_mul_traceChangeInv ops,
    traceChangeInv_mul_traceChange ops,
    traceChange_isUpperTriangular ops,
    traceChange_apply_diag ops,
    traceChange_isUpperTriangular (inverseTrace ops),
    traceChange_apply_diag (inverseTrace ops),
    replay_inverseTrace M ops,
    fun s => prefixSpan_replay M ops s⟩

/-- The generated graded trace also preserves degree lowering.
@isnad1 id=other.1h4v.s9.b37f1e7c6026 from=translated src=- shape=463acf46 vocab=ed7f2e81
-/
theorem matrixReductionTrace_graded_certificate
    (degree : Fin m → ℕ) (M : Matrix (Fin m) (Fin m) k)
    (hM : LowersDegree degree M) :
    let ops := matrixReductionTrace M
    let R := replay M ops
    let V := traceChange ops
    let W := traceChangeInv ops
    R = M * V ∧ V * W = 1 ∧ W * V = 1 ∧
    V.IsUpperTriangular ∧ (∀ i, V i i = 1) ∧
    W.IsUpperTriangular ∧ (∀ i, W i i = 1) ∧
    replay R (inverseTrace ops) = M ∧
    (∀ s : ℕ, prefixSpan R s = prefixSpan M s) ∧
    TraceChangeCertificate degree V W ∧ LowersDegree degree R := by
  let ops := matrixReductionTrace M
  have hd := matrixReductionTrace_respectsDegree degree M hM
  have hc := traceChange_certificate degree ops hd
  exact ⟨replay_eq_mul_traceChange M ops,
    traceChange_mul_traceChangeInv ops,
    traceChangeInv_mul_traceChange ops,
    hc.upper, hc.diag, hc.inv_upper, hc.inv_diag,
    replay_inverseTrace M ops,
    fun s => prefixSpan_replay M ops s,
    hc, replay_lowersDegree degree M ops hM hd⟩

private theorem split_append_occurrence {α : Type*}
    (xs ys pre post : List α) (op : α)
    (h : xs ++ ys = pre ++ op :: post) :
    (∃ a b, xs = a ++ op :: b ∧ pre = a ∧ post = b ++ ys) ∨
    (∃ a b, ys = a ++ op :: b ∧ pre = xs ++ a ∧ post = b) := by
  induction xs generalizing pre with
  | nil =>
      exact Or.inr ⟨pre, post, by simpa using h, rfl, rfl⟩
  | cons x xs ih =>
      cases pre with
      | nil =>
          have hx : x = op := (List.cons.inj h).1
          have ht : xs ++ ys = post := (List.cons.inj h).2
          subst x
          exact Or.inl ⟨[], xs, rfl, rfl, ht.symm⟩
      | cons y ps =>
          have hxy : x = y := (List.cons.inj h).1
          have ht : xs ++ ys = ps ++ op :: post := (List.cons.inj h).2
          subst y
          rcases ih ps ht with ⟨a,b,ha,hpre,hpost⟩ | ⟨a,b,ha,hpre,hpost⟩
          · exact Or.inl ⟨x :: a, b, by simp [ha], by simp [hpre], hpost⟩
          · exact Or.inr ⟨a, b, ha, by simp [hpre], hpost⟩

private theorem matrixReductionTraceAux_step_spec
    (M : Matrix (Fin m) (Fin m) k) (js : List (Fin m))
    (pre post : List (EarlierColumnOp m k)) (op : EarlierColumnOp m k)
    (htrace : matrixReductionTraceAux M js = pre ++ (op :: post)) :
    let A := replay M pre
    ∃ p : Fin m,
      columnPivot (A.col op.1.j) = some p ∧
      columnPivot (A.col op.1.i) = some p ∧
      (∀ i : Fin m, i < op.1.j →
        columnPivot (A.col i) = some p → op.1.i ≤ i) ∧
      op.1.c = -(A p op.1.j / A p op.1.i) ∧
      pivotHeight (columnPivot ((A * op.1.toMatrix).col op.1.j)) <
        pivotHeight (columnPivot (A.col op.1.j)) := by
  induction js generalizing M pre post with
  | nil => simp [matrixReductionTraceAux] at htrace
  | cons j js ih =>
      let block := columnReductionTrace M j
      let M' := replay M block
      have hs : block ++ matrixReductionTraceAux M' js = pre ++ op :: post := htrace
      rcases split_append_occurrence block (matrixReductionTraceAux M' js)
        pre post op hs with ⟨a,b,hblock,hpre,_⟩ | ⟨a,b,htail,hpre,_⟩
      · subst pre
        obtain ⟨ht,p,hpj,hpi,hmin,hc,hdec⟩ :=
          columnReductionTrace_step_spec M j a b op hblock
        simpa only [ht] using
          (show ∃ p : Fin m,
            columnPivot ((replay M a).col j) = some p ∧
            columnPivot ((replay M a).col op.1.i) = some p ∧
            (∀ i : Fin m, i < j →
              columnPivot ((replay M a).col i) = some p → op.1.i ≤ i) ∧
            op.1.c = -((replay M a) p j / (replay M a) p op.1.i) ∧
            pivotHeight (columnPivot (((replay M a) * op.1.toMatrix).col j)) <
              pivotHeight (columnPivot ((replay M a).col j)) from
            ⟨p,hpj,hpi,hmin,hc,hdec⟩)
      · subst pre
        have htail' := ih M' a b htail
        simpa only [replay_append] using htail'

/-- Each operation is selected from the matrix after precisely the preceding operations.
@isnad1 id=other.1h6v.s9.aca9b01168a0 from=translated src=- shape=0a3dadd4 vocab=38d6d608
-/
theorem matrixReductionTrace_step_spec
    (M : Matrix (Fin m) (Fin m) k)
    (pre post : List (EarlierColumnOp m k)) (op : EarlierColumnOp m k)
    (htrace : matrixReductionTrace M = pre ++ (op :: post)) :
    let A := replay M pre
    ∃ p : Fin m,
      columnPivot (A.col op.1.j) = some p ∧
      columnPivot (A.col op.1.i) = some p ∧
      (∀ i : Fin m, i < op.1.j →
        columnPivot (A.col i) = some p → op.1.i ≤ i) ∧
      op.1.c = -(A p op.1.j / A p op.1.i) ∧
      pivotHeight (columnPivot ((A * op.1.toMatrix).col op.1.j)) <
        pivotHeight (columnPivot (A.col op.1.j)) := by
  exact matrixReductionTraceAux_step_spec M (List.finRange m) pre post op htrace

end TDA.Persistence.Reduction
