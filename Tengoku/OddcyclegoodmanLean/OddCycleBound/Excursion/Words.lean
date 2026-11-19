import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Words in `P` and `Q`, blocks, and excursions (combinatorics of Section 3)

A word is a sequence of letters `P` (`false`) and `Q` (`true`).

* *Cyclic words* of length `n + 1` are functions `Fin (n + 1) → Bool`; positions are added modulo
  `n + 1`. A *mark* of a cyclic word is a position `j` with a `Q` immediately before it and a `P`
  at it; the number of marks is the number of cyclic `Q`-blocks, i.e. of excursions.
  `sum_numMarks_mul` is the paper's marked-word count: for a rotation-invariant weight,
  summing over marked words in two ways gives `r · ∑_{r excursions} = m · ∑_{P…Q, r excursions}`.
* *Linear words* are lists. A list not starting with `Q` is uniquely
  `blockWord t ++ replicate a P`, where `blockWord` concatenates blocks `P^{α+1} Q^{β+1}`
  (run-length decoding, `exists_blockWord`, `blockWord_append_injective`).
-/

open Finset

namespace OddCycleBound.Excursion

/-! ### Cyclic words and marks -/

section Cyclic

variable {n : ℕ}

/-- `j` is a mark of the cyclic word `w`: the letter before position `j` is `Q`, the letter at
position `j` is `P`.-/
def IsMark (w : Fin (n + 1) → Bool) (j : Fin (n + 1)) : Prop := w (j - 1) = true ∧ w j = false

instance (w : Fin (n + 1) → Bool) : DecidablePred (IsMark w) :=
  fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- The marks of a cyclic word.-/
def marks (w : Fin (n + 1) → Bool) : Finset (Fin (n + 1)) := univ.filter (IsMark w)

/-- The number of excursions (cyclic `Q`-blocks) of a cyclic word.-/
def numMarks (w : Fin (n + 1) → Bool) : ℕ := (marks w).card

/-- Rotation: the cyclic word `w` read from position `j`.-/
def rot (j : Fin (n + 1)) (w : Fin (n + 1) → Bool) : Fin (n + 1) → Bool := fun i => w (i + j)

/--
@isnad1 id=iff.0h4v.s7.0c15f4f9489c from=translated src=- shape=619691de vocab=69bbd252
-/
lemma isMark_rot (j i : Fin (n + 1)) (w : Fin (n + 1) → Bool) :
    IsMark (rot j w) i ↔ IsMark w (i + j) := by
  simp only [IsMark, rot, sub_add_eq_add_sub]

/--
@isnad1 id=eq.0h4v.s7.033e0afd7b16 from=translated src=- shape=6cfb243d vocab=ccb296bd
-/
lemma rot_rot (i j : Fin (n + 1)) (w : Fin (n + 1) → Bool) : rot i (rot j w) = rot (j + i) w := by
  funext x; simp only [rot]; congr 1; abel

/--
@isnad1 id=eq.0h2v.s6.b4d2385359fb from=translated src=- shape=3336dfc2 vocab=ccb296bd
-/
lemma rot_zero (w : Fin (n + 1) → Bool) : rot 0 w = w := by
  funext x; simp [rot]

/--
@isnad1 id=eq.0h3v.s5.fb2f17fcc142 from=translated src=- shape=3a4d025b vocab=9b6ec35c
-/
lemma numMarks_rot (j : Fin (n + 1)) (w : Fin (n + 1) → Bool) :
    numMarks (rot j w) = numMarks w := by
  unfold numMarks marks
  refine Finset.card_nbij' (fun i => i + j) (fun i => i - j) ?_ ?_ ?_ ?_
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi ⊢
    exact (isMark_rot j i w).mp hi
  · intro i hi
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi ⊢
    rw [isMark_rot, sub_add_cancel]; exact hi
  · intro i _; simp
  · intro i _; simp

/-- A cyclic word without excursions is constant.-/
lemma eq_const_of_numMarks_eq_zero {w : Fin (n + 1) → Bool} (h : numMarks w = 0) :
    w = (fun _ => false) ∨ w = (fun _ => true) := by
  have hno : ∀ j, w (j - 1) = true → w j = true := by
    intro j hj
    by_contra hjf
    have hmem : j ∈ marks w := by
      simp only [marks, Finset.mem_filter, Finset.mem_univ, true_and, IsMark]
      exact ⟨hj, by simpa using hjf⟩
    rw [numMarks, Finset.card_eq_zero] at h
    rw [h] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  by_cases hall : ∀ i, w i = false
  · left; funext i; exact hall i
  · right
    simp only [not_forall] at hall
    obtain ⟨i, hi⟩ := hall
    have hi' : w i = true := by simpa using hi
    have hstep : ∀ d : Fin (n + 1), w (i + d) = true := by
      intro d
      induction d using Fin.induction with
      | zero => simpa using hi'
      | succ k ih =>
          apply hno
          rw [← Fin.coeSucc_eq_succ, ← add_assoc, add_sub_cancel_right]
          exact ih
    funext j
    have := hstep (j - i)
    rwa [add_sub_cancel] at this

end Cyclic

/-! ### Lists of letters -/

section Lists

variable {α : Type*} [DecidableEq α]

/-- All lists of length `r` with entries in `s`.-/
def listsOf (s : Finset α) : ℕ → Finset (List α)
  | 0 => {[]}
  | r + 1 => (s ×ˢ listsOf s r).image fun p => p.1 :: p.2

/--
@isnad1 id=iff.0h4v.s6.282fbab57646 from=translated src=- shape=cdf61110 vocab=8336ee3c
-/
lemma mem_listsOf {s : Finset α} : ∀ {r : ℕ} {l : List α},
    l ∈ listsOf s r ↔ l.length = r ∧ ∀ x ∈ l, x ∈ s
  | 0, l => by cases l <;> simp [listsOf]
  | r + 1, l => by
      cases l with
      | nil => simp [listsOf]
      | cons a l =>
          simp only [listsOf, Finset.mem_image, Finset.mem_product, Prod.exists,
            List.cons.injEq, List.length_cons, List.mem_cons, forall_eq_or_imp]
          constructor
          · rintro ⟨b, l', ⟨hb, hl'⟩, rfl, rfl⟩
            exact ⟨by rw [(mem_listsOf.mp hl').1], hb, (mem_listsOf.mp hl').2⟩
          · rintro ⟨hlen, ha, hl⟩
            exact ⟨a, l, ⟨ha, mem_listsOf.mpr ⟨by omega, hl⟩⟩, rfl, rfl⟩

/--
@isnad1 id=eq.0h5v.s6.8213eae45303 from=translated src=- shape=2bf38b49 vocab=51180691
-/
lemma sum_listsOf_succ {β : Type*} [AddCommMonoid β] (s : Finset α) (r : ℕ)
    (G : List α → β) :
    ∑ l ∈ listsOf s (r + 1), G l = ∑ a ∈ s, ∑ l ∈ listsOf s r, G (a :: l) := by
  rw [listsOf, Finset.sum_image, Finset.sum_product]
  rintro ⟨a, l⟩ _ ⟨b, l'⟩ _ h
  simp only [List.cons.injEq] at h
  rw [h.1, h.2]

end Lists

/-- All words of length `L`.-/
def allWords (L : ℕ) : Finset (List Bool) := listsOf univ L

/--
@isnad1 id=iff.0h2v.s4.3dd366e72f70 from=translated src=- shape=4df08e09 vocab=bde47a33
-/
lemma mem_allWords {L : ℕ} {l : List Bool} : l ∈ allWords L ↔ l.length = L := by
  simp [allWords, mem_listsOf]

/--
@isnad1 id=eq.0h3v.s6.494772b60201 from=translated src=- shape=0e4968c6 vocab=4d2d89b1
-/
lemma sum_allWords_succ {β : Type*} [AddCommMonoid β] (L : ℕ) (G : List Bool → β) :
    ∑ l ∈ allWords (L + 1), G l = ∑ l ∈ allWords L, (G (false :: l) + G (true :: l)) := by
  rw [allWords, sum_listsOf_succ, Fintype.sum_bool, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => add_comm _ _

/-- Sums over cyclic words `Fin L → Bool` are sums over lists of length `L`.
@isnad1 id=eq.0h3v.s6.32d74c9ad3f3 from=translated src=- shape=1aa740f7 vocab=89bbcbef
-/
lemma sum_fin_eq_sum_allWords {β : Type*} [AddCommMonoid β] :
    ∀ (L : ℕ) (G : List Bool → β), ∑ w : Fin L → Bool, G (List.ofFn w) = ∑ l ∈ allWords L, G l
  | 0, G => by simp [allWords, listsOf]
  | L + 1, G => by
      rw [← (Fin.consEquiv fun _ : Fin (L + 1) => Bool).sum_comp, Fintype.sum_prod_type,
        allWords, sum_listsOf_succ]
      refine Finset.sum_congr rfl fun b _ => ?_
      show _ = ∑ l ∈ allWords L, G (b :: l)
      rw [← sum_fin_eq_sum_allWords L (fun l => G (b :: l))]
      refine Finset.sum_congr rfl fun w _ => ?_
      simp [Fin.consEquiv, List.ofFn_succ]

/-! ### Blocks and run-length decoding -/

/-- The block pair `P^{α+1} Q^{β+1}`.-/
def blk (p : ℕ × ℕ) : List Bool := List.replicate (p.1 + 1) false ++ List.replicate (p.2 + 1) true

/-- The linear word with block pairs `(α₁+1, β₁+1), …, (α_r+1, β_r+1)`.-/
def blockWord (t : List (ℕ × ℕ)) : List Bool := t.flatMap blk

/-- The total excess `∑ (αᵢ + βᵢ)` of a block-length tuple.-/
def excess (t : List (ℕ × ℕ)) : ℕ := (t.map fun p => p.1 + p.2).sum

/--
@isnad1 id=eq.0h0v.s3.635c056916dd from=translated src=- shape=ec35f9df vocab=47a1a404
-/
@[simp] lemma blockWord_nil : blockWord [] = [] := rfl

/--
@isnad1 id=eq.0h2v.s5.aa05c5af8530 from=translated src=- shape=f4d9f142 vocab=e9a096ff
-/
@[simp] lemma blockWord_cons (p : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    blockWord (p :: t) = blk p ++ blockWord t := by simp [blockWord]

/--
@isnad1 id=eq.0h0v.s3.7949ff53fdbe from=translated src=- shape=9b0cc7f6 vocab=fff72fb3
-/
@[simp] lemma excess_nil : excess [] = 0 := rfl

/--
@isnad1 id=eq.0h2v.s5.82d9efa0cddc from=translated src=- shape=03797bc9 vocab=8466cb97
-/
@[simp] lemma excess_cons (p : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    excess (p :: t) = p.1 + p.2 + excess t := by simp [excess]

/--
@isnad1 id=eq.0h1v.s5.5ebbb684c1f9 from=translated src=- shape=e6133613 vocab=2f9b9e3c
-/
lemma length_blockWord : ∀ t : List (ℕ × ℕ), (blockWord t).length = excess t + 2 * t.length
  | [] => rfl
  | p :: t => by
      simp only [blockWord_cons, List.length_append, blk, List.length_replicate,
        length_blockWord t, excess_cons, List.length_cons]
      ring

/--
@isnad1 id=ne.0h2v.s5.bc3c522a896a from=translated src=- shape=b036c8ef vocab=ed0f7b49
-/
lemma head?_blockWord_append (t : List (ℕ × ℕ)) (a : ℕ) :
    (blockWord t ++ List.replicate a false).head? ≠ some true := by
  cases t with
  | nil => cases a <;> simp [List.replicate_succ]
  | cons p t => simp [blk, List.replicate_succ]

/-- Splitting off a maximal run.
@isnad1 id=ex.0h2v.s5.4e0a3fd57f2f from=translated src=- shape=27cd0df1 vocab=7e63ea2f
-/
lemma exists_run (a : Bool) : ∀ l : List Bool,
    ∃ k l', l = List.replicate k a ++ l' ∧ l'.head? ≠ some a
  | [] => ⟨0, [], by simp⟩
  | b :: l => by
      by_cases hb : b = a
      · obtain ⟨k, l', hl, hl'⟩ := exists_run a l
        exact ⟨k + 1, l', by rw [hl, hb]; simp [List.replicate_succ], hl'⟩
      · exact ⟨0, b :: l, by simp, by simpa using hb⟩

/-- Uniqueness of a maximal run.
@isnad1 id=and.3h5v.s6.374219c1be19 from=translated src=- shape=a3121b36 vocab=7e63ea2f
-/
lemma run_unique (a : Bool) : ∀ (k k' : ℕ) (l l' : List Bool),
    l.head? ≠ some a → l'.head? ≠ some a →
    List.replicate k a ++ l = List.replicate k' a ++ l' → k = k' ∧ l = l'
  | 0, 0, l, l', _, _, h => ⟨rfl, by simpa using h⟩
  | k + 1, 0, l, l', _, h', h => by
      simp only [List.replicate_succ, List.replicate_zero, List.nil_append, List.cons_append] at h
      rw [← h] at h'; simp at h'
  | 0, k' + 1, l, l', hl, _, h => by
      simp only [List.replicate_succ, List.replicate_zero, List.nil_append, List.cons_append] at h
      rw [h] at hl; simp at hl
  | k + 1, k' + 1, l, l', hl, hl', h => by
      simp only [List.replicate_succ, List.cons_append, List.cons.injEq, true_and] at h
      obtain ⟨h1, h2⟩ := run_unique a k k' l l' hl hl' h
      exact ⟨by rw [h1], h2⟩

/-- **Run-length decoding.** Every word not starting with `Q` is `blockWord t ++ P^a`.
@isnad1 id=ex.2h2v.s5.adfaa9925530 from=translated src=- shape=c6713ef0 vocab=b7562b5d
-/
lemma exists_blockWord : ∀ (L : ℕ) (l : List Bool), l.length ≤ L → l.head? ≠ some true →
    ∃ t a, l = blockWord t ++ List.replicate a false
  | L, l, hL, hl => by
      obtain ⟨k, l₁, rfl, hl₁⟩ := exists_run false l
      cases l₁ with
      | nil => exact ⟨[], k, by simp⟩
      | cons b l₁ =>
          have hb : b = true := by simpa using hl₁
          subst hb
          obtain ⟨k', l₂, hl₂eq, hl₂⟩ := exists_run true (true :: l₁)
          have hk : k ≠ 0 := by
            rintro rfl; simp at hl
          have hk' : k' ≠ 0 := by
            rintro rfl
            simp only [List.replicate_zero, List.nil_append] at hl₂eq
            rw [← hl₂eq] at hl₂; simp at hl₂
          obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by
            simp only [List.length_append, List.length_replicate, List.length_cons] at hL
            omega⟩
          have hlen : l₂.length ≤ L' := by
            have := congrArg List.length hl₂eq
            simp only [List.length_append, List.length_replicate, List.length_cons] at this hL
            omega
          obtain ⟨t, a, rfl⟩ := exists_blockWord L' l₂ hlen hl₂
          refine ⟨(k - 1, k' - 1) :: t, a, ?_⟩
          rw [hl₂eq]
          simp only [blockWord_cons, blk, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk),
            Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk'), List.append_assoc]

/--
@isnad1 id=and.1h4v.s6.9a4880c68a3d from=translated src=- shape=368bb2f6 vocab=cfc9bba0
-/
lemma blockWord_append_injective : ∀ (t t' : List (ℕ × ℕ)) (a a' : ℕ),
    blockWord t ++ List.replicate a false = blockWord t' ++ List.replicate a' false →
      t = t' ∧ a = a'
  | [], [], a, a', h => by
      simp only [blockWord_nil, List.nil_append] at h
      exact ⟨rfl, by simpa using congrArg List.length h⟩
  | [], p :: t', a, a', h => by
      exfalso
      have hmem : true ∈ blockWord (p :: t') ++ List.replicate a' false := by
        simp [blk, List.mem_replicate]
      rw [← h] at hmem
      simp [List.mem_replicate] at hmem
  | p :: t, [], a, a', h => by
      exfalso
      have hmem : true ∈ blockWord (p :: t) ++ List.replicate a false := by
        simp [blk, List.mem_replicate]
      rw [h] at hmem
      simp [List.mem_replicate] at hmem
  | p :: t, p' :: t', a, a', h => by
      simp only [blockWord_cons, blk, List.append_assoc] at h
      have hhd : ∀ (s : List (ℕ × ℕ)) (b : ℕ),
          (blockWord s ++ List.replicate b false).head? ≠ some true :=
        head?_blockWord_append
      obtain ⟨h1, h2⟩ := run_unique false (p.1 + 1) (p'.1 + 1) _ _ (by simp [List.replicate_succ])
        (by simp [List.replicate_succ]) h
      obtain ⟨h3, h4⟩ := run_unique true (p.2 + 1) (p'.2 + 1) _ _ (hhd t a) (hhd t' a') h2
      obtain ⟨h5, h6⟩ := blockWord_append_injective t t' a a' h4
      refine ⟨?_, h6⟩
      rw [h5]
      congr 1
      exact Prod.ext (by omega) (by omega)

end OddCycleBound.Excursion
