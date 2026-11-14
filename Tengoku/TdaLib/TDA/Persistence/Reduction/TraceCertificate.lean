import Tengoku.TdaLib.TDA.Persistence.Reduction.Trace
import Tengoku.Seed.LinearAlgebra.Matrix.Block

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms inverseEarlierColumnOp` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms inverseTrace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChangeInv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceRespectsDegree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms LowersDegree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChangeInv_nil` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChangeInv_cons` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChangeInv_append` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChange_mul_traceChangeInv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChangeInv_mul_traceChange` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms single_upper` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChange_isUpperTriangular` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChange_apply_diag` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceRespectsDegree_inverseTrace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms single_degree_support` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms degree_support_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChange_apply_of_degree_ne` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms traceChange_certificate` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms replay_inverseTrace` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms lowersDegree_mul_degree_support` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms replay_lowersDegree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms degree_eq_of_common_pivot` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.mk` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.rec` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.recOn` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.casesOn` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.mul_inv` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.inv_mul` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.upper` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.diag` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.inv_upper` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.inv_diag` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.degree_support` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms TraceChangeCertificate.inv_degree_support` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Certificates for graded finite column traces

The inverse is an explicit list of reverse-ordered, negated transvections. The supplied
trace is not assumed to have been selected by a reduction algorithm.
-/

namespace TDA.Persistence.Reduction

variable {m : ℕ} {k : Type*} [Field k]

/-- Invert an earlier-column operation without changing its source or target.-/
def inverseEarlierColumnOp (op : EarlierColumnOp m k) : EarlierColumnOp m k :=
  ⟨op.1.inv, by simpa only [Matrix.TransvectionStruct.inv_i,
    Matrix.TransvectionStruct.inv_j] using op.2⟩

/-- Undo a chronological trace in reverse order.-/
def inverseTrace (ops : List (EarlierColumnOp m k)) : List (EarlierColumnOp m k) :=
  ops.reverse.map inverseEarlierColumnOp

/-- The explicit change matrix of the inverse trace.-/
def traceChangeInv (ops : List (EarlierColumnOp m k)) : Matrix (Fin m) (Fin m) k :=
  traceChange (inverseTrace ops)

/-- Every supplied operation joins columns of the same homological dimension.-/
def TraceRespectsDegree (degree : Fin m → ℕ)
    (ops : List (EarlierColumnOp m k)) : Prop :=
  ∀ op ∈ ops, degree op.1.i = degree op.1.j

/-- Entry support of a boundary-shaped matrix, with natural successor rather than subtraction.-/
def LowersDegree (degree : Fin m → ℕ)
    (M : Matrix (Fin m) (Fin m) k) : Prop :=
  ∀ r c, M r c ≠ 0 → degree c = degree r + 1

/-- Two-sided, upper-unitriangular, degree-preserving change-of-basis data.-/
structure TraceChangeCertificate (degree : Fin m → ℕ)
    (V W : Matrix (Fin m) (Fin m) k) : Prop where
  mul_inv : V * W = 1
  inv_mul : W * V = 1
  upper : V.IsUpperTriangular
  diag : ∀ i, V i i = 1
  inv_upper : W.IsUpperTriangular
  inv_diag : ∀ i, W i i = 1
  degree_support : ∀ i j, degree i ≠ degree j → V i j = 0
  inv_degree_support : ∀ i j, degree i ≠ degree j → W i j = 0

/--
@isnad1 id=eq.0h2v.s6.68779254312d from=translated src=- shape=51a4295c vocab=55545f89
-/
theorem traceChangeInv_nil :
    traceChangeInv ([] : List (EarlierColumnOp m k)) = 1 := rfl

/--
@isnad1 id=eq.0h4v.s7.9a2a12262f4d from=translated src=- shape=dbbb4c02 vocab=ad5cb4e4
-/
theorem traceChangeInv_cons (op : EarlierColumnOp m k)
    (ops : List (EarlierColumnOp m k)) :
    traceChangeInv (op :: ops) = traceChangeInv ops * op.1.inv.toMatrix := by
  simp [traceChangeInv, inverseTrace, inverseEarlierColumnOp, traceChange]

/--
@isnad1 id=eq.0h4v.s6.cfece0785fd0 from=translated src=- shape=d6d01503 vocab=54d55f91
-/
theorem traceChangeInv_append (xs ys : List (EarlierColumnOp m k)) :
    traceChangeInv (xs ++ ys) = traceChangeInv ys * traceChangeInv xs := by
  simp [traceChangeInv, inverseTrace, List.reverse_append, List.map_append,
    traceChange_append]

/--
@isnad1 id=eq.0h3v.s6.491e435e0a5d from=translated src=- shape=755441ff vocab=6e4db751
-/
theorem traceChange_mul_traceChangeInv (ops : List (EarlierColumnOp m k)) :
    traceChange ops * traceChangeInv ops = 1 := by
  let L := ops.map Subtype.val
  have h := Matrix.TransvectionStruct.prod_mul_reverse_inv_prod L
  simpa [traceChange, traceChangeInv, inverseTrace, inverseEarlierColumnOp,
    L, List.map_reverse, List.map_map, Function.comp_def] using h

/--
@isnad1 id=eq.0h3v.s6.be8c64ed223c from=translated src=- shape=755441ff vocab=6e4db751
-/
theorem traceChangeInv_mul_traceChange (ops : List (EarlierColumnOp m k)) :
    traceChangeInv ops * traceChange ops = 1 := by
  let L := ops.map Subtype.val
  have h := Matrix.TransvectionStruct.reverse_inv_prod_mul_prod L
  simpa [traceChange, traceChangeInv, inverseTrace, inverseEarlierColumnOp,
    L, List.map_reverse, List.map_map, Function.comp_def] using h

private theorem single_upper (op : EarlierColumnOp m k) :
    op.1.toMatrix.IsUpperTriangular := by
  simpa only [Matrix.TransvectionStruct.toMatrix] using
    (Matrix.blockTriangular_transvection (b := id) (le_of_lt op.2) op.1.c)

/--
@isnad1 id=isuppert.0h3v.s5.cc9f0061f62a from=translated src=- shape=a1d00d71 vocab=4e59c83b
-/
theorem traceChange_isUpperTriangular (ops : List (EarlierColumnOp m k)) :
    (traceChange ops).IsUpperTriangular := by
  induction ops with
  | nil => simpa only [traceChange_nil] using (Matrix.blockTriangular_one (b := id) (R := k))
  | cons op ops ih =>
      rw [traceChange_cons]
      exact (single_upper op).mul ih

/--
@isnad1 id=eq.0h4v.s5.1f312a1c2b21 from=translated src=- shape=ed9171ea vocab=40814653
-/
theorem traceChange_apply_diag (ops : List (EarlierColumnOp m k)) (i : Fin m) :
    traceChange ops i i = 1 := by
  induction ops with
  | nil => simp [traceChange_nil]
  | cons op ops ih =>
      rw [traceChange_cons, Matrix.TransvectionStruct.toMatrix]
      by_cases h : i = op.1.i
      · subst i
        rw [Matrix.transvection_mul_apply_same]
        have hz : traceChange ops op.1.j op.1.i = 0 :=
          traceChange_isUpperTriangular ops op.2
        simp [ih, hz]
      · rw [Matrix.transvection_mul_apply_of_ne (ha := h)]
        exact ih

/--
@isnad1 id=traceres.1h4v.s5.3e5a1fe7a9c4 from=translated src=- shape=681f607f vocab=07c494e9
-/
theorem traceRespectsDegree_inverseTrace (degree : Fin m → ℕ)
    (ops : List (EarlierColumnOp m k)) (hops : TraceRespectsDegree degree ops) :
    TraceRespectsDegree degree (inverseTrace ops) := by
  intro op hop
  rcases List.mem_map.mp hop with ⟨old, hold, rfl⟩
  have hmem : old ∈ ops := List.mem_reverse.mp hold
  simpa [inverseEarlierColumnOp] using hops old hmem

private theorem single_degree_support (degree : Fin m → ℕ)
    (op : EarlierColumnOp m k) (hdegree : degree op.1.i = degree op.1.j)
    (r c : Fin m) (hrc : degree r ≠ degree c) : op.1.toMatrix r c = 0 := by
  simp only [Matrix.TransvectionStruct.toMatrix, Matrix.transvection, Matrix.add_apply]
  rw [Matrix.single_apply]
  by_cases h : r = c
  · exact (hrc (congrArg degree h)).elim
  · simp only [Matrix.one_apply, ite_eq_right h, zero_add]
    split
    · next heq =>
        rcases heq with ⟨rfl, rfl⟩
        exact (hrc hdegree).elim
    · rfl

private theorem degree_support_mul (degree : Fin m → ℕ)
    (A B : Matrix (Fin m) (Fin m) k)
    (hA : ∀ i j, degree i ≠ degree j → A i j = 0)
    (hB : ∀ i j, degree i ≠ degree j → B i j = 0)
    (r c : Fin m) (hrc : degree r ≠ degree c) : (A * B) r c = 0 := by
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro q _
  by_cases hrq : degree r = degree q
  · have hqc : degree q ≠ degree c := by
      intro h
      exact hrc (hrq.trans h)
    simp [hB q c hqc]
  · simp [hA r q hrq]

/--
@isnad1 id=eq.2h6v.s5.cb8274f4493b from=translated src=- shape=3fa202c8 vocab=ba4a095c
-/
theorem traceChange_apply_of_degree_ne (degree : Fin m → ℕ)
    (ops : List (EarlierColumnOp m k)) (hops : TraceRespectsDegree degree ops)
    (i j : Fin m) (hij : degree i ≠ degree j) :
    traceChange ops i j = 0 := by
  induction ops generalizing i j with
  | nil =>
      rw [traceChange_nil]
      have h : i ≠ j := by intro heq; exact hij (congrArg degree heq)
      simp [h]
  | cons op ops ih =>
      rw [traceChange_cons]
      apply degree_support_mul degree op.1.toMatrix (traceChange ops)
      · exact single_degree_support degree op (hops op (by simp))
      · intro r c h
        exact ih (by intro x hx; exact hops x (by simp [hx])) r c h
      · exact hij

/--
@isnad1 id=tracecha.1h4v.s5.8dcf6a16c9c3 from=translated src=- shape=098e742b vocab=12d63528
-/
theorem traceChange_certificate (degree : Fin m → ℕ)
    (ops : List (EarlierColumnOp m k)) (hops : TraceRespectsDegree degree ops) :
    TraceChangeCertificate degree (traceChange ops) (traceChangeInv ops) := by
  refine ⟨traceChange_mul_traceChangeInv ops, traceChangeInv_mul_traceChange ops,
    traceChange_isUpperTriangular ops, traceChange_apply_diag ops, ?_, ?_, ?_, ?_⟩
  · exact traceChange_isUpperTriangular (inverseTrace ops)
  · exact traceChange_apply_diag (inverseTrace ops)
  · exact traceChange_apply_of_degree_ne degree ops hops
  · exact traceChange_apply_of_degree_ne degree (inverseTrace ops)
      (traceRespectsDegree_inverseTrace degree ops hops)

/--
@isnad1 id=eq.0h4v.s5.cadb618c2fb7 from=translated src=- shape=8c3c1b75 vocab=f80c94a8
-/
theorem replay_inverseTrace (M : Matrix (Fin m) (Fin m) k)
    (ops : List (EarlierColumnOp m k)) :
    replay (replay M ops) (inverseTrace ops) = M := by
  rw [replay_eq_mul_traceChange, replay_eq_mul_traceChange, Matrix.mul_assoc]
  rw [← traceChangeInv, traceChange_mul_traceChangeInv, mul_one]

private theorem lowersDegree_mul_degree_support (degree : Fin m → ℕ)
    (M V : Matrix (Fin m) (Fin m) k) (hM : LowersDegree degree M)
    (hV : ∀ i j, degree i ≠ degree j → V i j = 0) :
    LowersDegree degree (M * V) := by
  intro r c hn
  by_contra hdegree
  have hz : (M * V) r c = 0 := by
    rw [Matrix.mul_apply]
    apply Finset.sum_eq_zero
    intro q _
    by_cases hMq : M r q = 0
    · simp [hMq]
    · have hqc : degree q ≠ degree c := by
        intro h
        exact hdegree (h.symm.trans (hM r q hMq))
      simp [hV q c hqc]
  exact hn hz

/--
@isnad1 id=lowersde.2h5v.s5.4c42751b49c8 from=translated src=- shape=500c0ba1 vocab=3b68a12d
-/
theorem replay_lowersDegree (degree : Fin m → ℕ)
    (M : Matrix (Fin m) (Fin m) k) (ops : List (EarlierColumnOp m k))
    (hM : LowersDegree degree M) (hops : TraceRespectsDegree degree ops) :
    LowersDegree degree (replay M ops) := by
  rw [replay_eq_mul_traceChange]
  exact lowersDegree_mul_degree_support degree M (traceChange ops) hM
    (traceChange_apply_of_degree_ne degree ops hops)

/--
@isnad1 id=eq.3h7v.s6.0c4d54c4c97c from=translated src=- shape=64b6768a vocab=410ff95f
-/
theorem degree_eq_of_common_pivot [DecidableEq k] (degree : Fin m → ℕ)
    (M : Matrix (Fin m) (Fin m) k) (hM : LowersDegree degree M)
    (i j p : Fin m) (hi : columnPivot (M.col i) = some p)
    (hj : columnPivot (M.col j) = some p) : degree i = degree j := by
  have hi' : M p i ≠ 0 := (columnPivot_some_iff (M.col i) p).mp hi |>.1
  have hj' : M p j ≠ 0 := (columnPivot_some_iff (M.col j) p).mp hj |>.1
  exact (hM p i hi').trans (hM p j hj').symm

/-! Complete local trust inventory, including private helpers and fixture data. -/

end TDA.Persistence.Reduction
