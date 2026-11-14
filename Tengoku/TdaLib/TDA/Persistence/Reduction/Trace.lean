import Tengoku.TdaLib.TDA.Persistence.Reduction.PrefixSpan

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite earlier-column traces

An earlier-column trace is a supplied finite list of transvections whose source index is
strictly less than its target index. `replay` applies those operations in list order by
right-multiplication. `traceChange` is the corresponding chronological product, so the final
matrix is the initial matrix multiplied on the right by that product.
-/

namespace TDA.Persistence.Reduction

/-- A transvection together with the strict order needed for prefix-span preservation.-/
abbrev EarlierColumnOp (m : ℕ) (k : Type*) :=
  { op : Matrix.TransvectionStruct (Fin m) k // op.i < op.j }

variable {m : ℕ} {k : Type*} [Field k]

/-- Apply a supplied finite list of earlier-column operations from left to right.-/
def replay (M : Matrix (Fin m) (Fin m) k)
    (ops : List (EarlierColumnOp m k)) : Matrix (Fin m) (Fin m) k :=
  ops.foldl (fun A op => A * op.1.toMatrix) M

/-- The chronological right-product for a supplied finite list of operations.-/
def traceChange (ops : List (EarlierColumnOp m k)) :
    Matrix (Fin m) (Fin m) k :=
  (ops.map (fun op => op.1.toMatrix)).prod

/-- Replaying the empty trace leaves its input unchanged.
@isnad1 id=eq.0h3v.s4.f17bd9c5646e from=translated src=- shape=05069cd1 vocab=25e80dce
-/
theorem replay_nil (M : Matrix (Fin m) (Fin m) k) : replay M [] = M := rfl

/-- Replaying a cons first performs its head operation, then its tail.
@isnad1 id=eq.0h5v.s7.7cd560949d1c from=translated src=- shape=e7c3c156 vocab=c22930d8
-/
theorem replay_cons (M : Matrix (Fin m) (Fin m) k)
    (op : EarlierColumnOp m k) (ops : List (EarlierColumnOp m k)) :
    replay M (op :: ops) = replay (M * op.1.toMatrix) ops := rfl

/-- The empty trace has identity change matrix.
@isnad1 id=eq.0h2v.s6.2632be5f323f from=translated src=- shape=51a4295c vocab=8f9fa80b
-/
theorem traceChange_nil : traceChange ([] : List (EarlierColumnOp m k)) = 1 := rfl

/-- A trace change matrix is the head operation followed by the tail product.
@isnad1 id=eq.0h4v.s6.6ad325a20948 from=translated src=- shape=a3198e2c vocab=c4cf642d
-/
theorem traceChange_cons (op : EarlierColumnOp m k)
    (ops : List (EarlierColumnOp m k)) :
    traceChange (op :: ops) = op.1.toMatrix * traceChange ops := rfl

/-- The replayed matrix is the initial matrix multiplied by the chronological trace product.
@isnad1 id=eq.0h4v.s6.d94f58fee15a from=translated src=- shape=90b690ce vocab=e9ba2e53
-/
theorem replay_eq_mul_traceChange (M : Matrix (Fin m) (Fin m) k)
    (ops : List (EarlierColumnOp m k)) :
    replay M ops = M * traceChange ops := by
  induction ops generalizing M with
  | nil => simp [replay, traceChange]
  | cons op ops ih =>
      rw [replay_cons, ih, traceChange_cons, Matrix.mul_assoc]

/-- Replaying a concatenated trace is replaying the first part and then the second.
@isnad1 id=eq.0h5v.s6.a89a26f52caf from=translated src=- shape=da67e4d6 vocab=a0604ea8
-/
theorem replay_append (M : Matrix (Fin m) (Fin m) k)
    (xs ys : List (EarlierColumnOp m k)) :
    replay M (xs ++ ys) = replay (replay M xs) ys := by
  induction xs generalizing M with
  | nil => rfl
  | cons op xs ih =>
      simp only [List.cons_append, replay_cons]
      exact ih (M * op.1.toMatrix)

/-- Concatenating traces concatenates their chronological right-products.
@isnad1 id=eq.0h4v.s6.153b68aba8f3 from=translated src=- shape=6f6ada91 vocab=79b29fd4
-/
theorem traceChange_append (xs ys : List (EarlierColumnOp m k)) :
    traceChange (xs ++ ys) = traceChange xs * traceChange ys := by
  have replay_one (ops : List (EarlierColumnOp m k)) :
      replay (1 : Matrix (Fin m) (Fin m) k) ops = traceChange ops := by
    rw [replay_eq_mul_traceChange, one_mul]
  calc
    traceChange (xs ++ ys) = replay (1 : Matrix (Fin m) (Fin m) k) (xs ++ ys) :=
      (replay_one (xs ++ ys)).symm
    _ = replay (replay (1 : Matrix (Fin m) (Fin m) k) xs) ys := replay_append _ _ _
    _ = replay (traceChange xs) ys := by rw [replay_one xs]
    _ = traceChange xs * traceChange ys := replay_eq_mul_traceChange _ _

/-- Every replayed finite trace preserves every natural-number column prefix.
@isnad1 id=eq.0h5v.s6.8b86f84a1399 from=translated src=- shape=a9b12e67 vocab=35f14f22
-/
theorem prefixSpan_replay (M : Matrix (Fin m) (Fin m) k)
    (ops : List (EarlierColumnOp m k)) (t : ℕ) :
    prefixSpan (replay M ops) t = prefixSpan M t := by
  induction ops generalizing M with
  | nil => rfl
  | cons op ops ih =>
      rw [replay_cons]
      calc
        prefixSpan (replay (M * op.1.toMatrix) ops) t =
            prefixSpan (M * op.1.toMatrix) t := ih _
        _ = prefixSpan M t := by
          simpa only [Matrix.TransvectionStruct.toMatrix] using
            prefixSpan_mul_transvection M op.1.i op.1.j op.1.c op.2 t

/-- The product form of a trace also preserves every natural-number column prefix.
@isnad1 id=eq.0h5v.s7.1c5569ef0b0e from=translated src=- shape=6223a946 vocab=aa4aa304
-/
theorem prefixSpan_mul_traceChange (M : Matrix (Fin m) (Fin m) k)
    (ops : List (EarlierColumnOp m k)) (t : ℕ) :
    prefixSpan (M * traceChange ops) t = prefixSpan M t := by
  rw [← replay_eq_mul_traceChange M ops]
  exact prefixSpan_replay M ops t

end TDA.Persistence.Reduction
