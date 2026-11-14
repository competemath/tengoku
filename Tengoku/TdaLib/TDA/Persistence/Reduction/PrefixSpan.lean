import Tengoku.TdaLib.TDA.Persistence.Reduction.Pivot
import Tengoku.Seed.LinearAlgebra.Span.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms prefixSpan_range_update_add_smul` (it only prints; the queue checks the axioms of every declaration). -/

/-!
# Prefix spans under an earlier-column operation

`prefixSpan M t` is the span of the first `t` columns that exist in the finite square matrix
`M`. Right multiplication by a transvection from an earlier source column into a later target
preserves every such prefix: whenever the target is included, its source is included too, and
the pinned span-update lemma applies to the resulting generator update.
-/

namespace TDA.Persistence.Reduction

variable {m : ℕ} {k : Type*} [Field k]

/-- The span of the columns of `M` whose zero-based indices are below the prefix length `t`.-/
noncomputable def prefixSpan (M : Matrix (Fin m) (Fin m) k) (t : ℕ) :
    Submodule k (Fin m → k) :=
  Submodule.span k
    (Set.range (fun q : {q : Fin m // q.val < t} => M.col q.1))

/-- Every column whose index is in the prefix is a member of its span.
@isnad1 id=mem.1h5v.s7.08448e3bbbab from=translated src=- shape=c8d1a861 vocab=076f3c11
-/
theorem col_mem_prefixSpan (M : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (q : Fin m) (hq : q.val < t) :
    M.col q ∈ prefixSpan M t := by
  exact Submodule.subset_span ⟨⟨q, hq⟩, rfl⟩

/-- The empty prefix spans only the zero vector.
@isnad1 id=eq.0h3v.s7.d99c7847cd0e from=translated src=- shape=6859a5a8 vocab=d8385402
-/
theorem prefixSpan_zero (M : Matrix (Fin m) (Fin m) k) :
    prefixSpan M 0 = ⊥ := by
  have h : (Set.range (fun q : {q : Fin m // q.val < 0} => M.col q.1)) = ∅ := by
    ext v
    constructor
    · rintro ⟨q, _⟩
      exact (Nat.not_lt_zero _ q.2).elim
    · simp
  simp [prefixSpan, h]

/-- Increasing the prefix length can only enlarge its column span.
@isnad1 id=le.1h5v.s8.1087bf51437d from=translated src=- shape=615f9536 vocab=00a5cfbe
-/
theorem prefixSpan_mono (M : Matrix (Fin m) (Fin m) k)
    (s t : ℕ) (hst : s ≤ t) :
    prefixSpan M s ≤ prefixSpan M t := by
  apply Submodule.span_mono
  rintro x ⟨q, rfl⟩
  exact ⟨⟨q.1, lt_of_lt_of_le q.2 hst⟩, rfl⟩

/-- A prefix of length at least the matrix dimension contains every column.
@isnad1 id=eq.1h4v.s7.cb870e89da63 from=translated src=- shape=86b64447 vocab=37c3a7d0
-/
theorem prefixSpan_eq_full (M : Matrix (Fin m) (Fin m) k)
    (t : ℕ) (ht : m ≤ t) :
    prefixSpan M t = Submodule.span k (Set.range M.col) := by
  have hrange :
      Set.range (fun q : {q : Fin m // q.val < t} => M.col q.1) = Set.range M.col := by
    ext x
    constructor
    · rintro ⟨q, rfl⟩
      exact ⟨q.1, rfl⟩
    · rintro ⟨q, rfl⟩
      exact ⟨⟨q, lt_of_lt_of_le q.isLt ht⟩, rfl⟩
  simp [prefixSpan, hrange]

private theorem prefixSpan_range_update_add_smul (M : Matrix (Fin m) (Fin m) k)
    (i j : Fin m) (c : k) (hij : i < j) (t : ℕ) (hj : j.val < t) :
    let ii : {q : Fin m // q.val < t} := ⟨i, lt_trans hij hj⟩
    let jj : {q : Fin m // q.val < t} := ⟨j, hj⟩
    let v : {q : Fin m // q.val < t} → (Fin m → k) := fun q => M.col q.1
    Submodule.span k (Set.range (Function.update v jj (v jj + c • v ii))) =
      prefixSpan M t := by
  dsimp only
  let ii : {q : Fin m // q.val < t} := ⟨i, lt_trans hij hj⟩
  let jj : {q : Fin m // q.val < t} := ⟨j, hj⟩
  have hne : ii ≠ jj := by
    intro h
    exact (ne_of_lt hij) (congrArg Subtype.val h)
  simpa only [ii, jj, prefixSpan] using
    (Submodule.span_range_update_add_smul hne
      (fun q : {q : Fin m // q.val < t} => M.col q.1) c)

/-- Right multiplication by an earlier-column transvection preserves every column prefix.
@isnad1 id=eq.1h7v.s7.489ba7d8742c from=translated src=- shape=2343d54e vocab=f27dfa71
-/
theorem prefixSpan_mul_transvection (M : Matrix (Fin m) (Fin m) k)
    (i j : Fin m) (c : k) (hij : i < j) (t : ℕ) :
    prefixSpan (M * Matrix.transvection i j c) t = prefixSpan M t := by
  by_cases hj : j.val < t
  · let ii : {q : Fin m // q.val < t} := ⟨i, lt_trans hij hj⟩
    let jj : {q : Fin m // q.val < t} := ⟨j, hj⟩
    let v : {q : Fin m // q.val < t} → (Fin m → k) := fun q => M.col q.1
    have hfun :
        (fun q : {q : Fin m // q.val < t} =>
          (M * Matrix.transvection i j c).col q.1) =
        Function.update v jj (v jj + c • v ii) := by
      funext q
      by_cases hq : q.1 = j
      · have hq' : q = jj := Subtype.ext hq
        subst q
        simp only [Function.update_self]
        exact col_mul_transvection M i j c
      · have hq' : q ≠ jj := by
          intro h
          exact hq (congrArg Subtype.val h)
        rw [col_mul_transvection_of_ne M i j q.1 c hq]
        simp [Function.update_of_ne hq']
        rfl
    unfold prefixSpan
    rw [hfun]
    exact prefixSpan_range_update_add_smul M i j c hij t hj
  · have hfun :
        (fun q : {q : Fin m // q.val < t} =>
          (M * Matrix.transvection i j c).col q.1) =
        (fun q => M.col q.1) := by
      funext q
      apply col_mul_transvection_of_ne
      intro hq
      exact hj (by simpa [hq] using q.2)
    unfold prefixSpan
    rw [hfun]

/-- The cancellation coefficient is a specialization of the universal scalar operation.
@isnad1 id=eq.1h7v.s7.4b607efd0966 from=translated src=- shape=84751593 vocab=f9df586e
-/
theorem prefixSpan_cancel (M : Matrix (Fin m) (Fin m) k)
    (i j p : Fin m) (hij : i < j) (t : ℕ) :
    prefixSpan (M * Matrix.transvection i j (-(M p j / M p i))) t =
      prefixSpan M t := by
  exact prefixSpan_mul_transvection M i j (-(M p j / M p i)) hij t

end TDA.Persistence.Reduction
