import Tengoku.OddcyclegoodmanLean.OddCycleBound.Excursion.Tuples

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Words versus block-length tuples

* For a linear word `P … Q`, the number of `Q`-blocks is one more than the number of internal
  boundaries `Q P` (`qpCount`); for the cyclic word with the same letters this is the number of
  marks (`numMarks_eq`).
* Linear words from `P` to `Q` with `r` `Q`-blocks are in bijection with `tuples r (L - 2r)`
  via `blockWord` (`sum_pq_eq_sum_tuples`); this is the bijection in the proof of
  Lemma `lem:cycle-excursions`.
* Linear words not starting with `Q` are in bijection with pairs of a tuple and a final
  `P`-block via `blockWord t ++ P^a` (`sum_head_ne_true_eq`); this is the bijection in the proof
  of Lemma `lem:path-excursions`.
-/

open Finset

namespace OddCycleBound.Excursion

/-- The number of boundaries where `Q` is followed by `P` in a linear word.-/
def qpCount : List Bool → ℕ
  | [] => 0
  | [_] => 0
  | a :: b :: l => (if a = true ∧ b = false then 1 else 0) + qpCount (b :: l)

lemma qpCount_append : ∀ l₁ l₂ : List Bool, qpCount (l₁ ++ l₂) =
    qpCount l₁ + qpCount l₂ +
      (if l₁.getLast? = some true ∧ l₂.head? = some false then 1 else 0)
  | [], l₂ => by simp [qpCount]
  | [a], [] => by simp [qpCount]
  | [a], b :: l₂ => by
      simp only [List.cons_append, List.nil_append, qpCount, List.getLast?_singleton,
        List.head?_cons, Option.some.injEq]
      ring
  | a :: b :: l₁, l₂ => by
      simp only [List.cons_append, qpCount]
      rw [← List.cons_append, qpCount_append (b :: l₁) l₂, List.getLast?_cons_cons]
      ring

lemma qpCount_replicate (a : Bool) : ∀ k, qpCount (List.replicate k a) = 0
  | 0 => rfl
  | 1 => rfl
  | k + 2 => by
      rw [List.replicate_succ, List.replicate_succ, qpCount, ← List.replicate_succ,
        qpCount_replicate a (k + 1)]
      cases a <;> simp

lemma getLast?_replicate_succ (a : Bool) (k : ℕ) :
    (List.replicate (k + 1) a).getLast? = some a := by
  rw [List.replicate_succ', List.getLast?_concat]

lemma qpCount_blk (p : ℕ × ℕ) : qpCount (blk p) = 0 := by
  rw [blk, qpCount_append, qpCount_replicate, qpCount_replicate, getLast?_replicate_succ]
  simp

lemma getLast?_blk (p : ℕ × ℕ) : (blk p).getLast? = some true := by
  rw [blk, List.getLast?_append_of_ne_nil _ (by simp), getLast?_replicate_succ]

lemma head?_blk_append (p : ℕ × ℕ) (l : List Bool) : (blk p ++ l).head? = some false := by
  simp [blk, List.replicate_succ]

lemma getLast?_blockWord : ∀ {t : List (ℕ × ℕ)}, t ≠ [] → (blockWord t).getLast? = some true
  | [p], _ => by simp [getLast?_blk]
  | p :: p' :: t, _ => by
      rw [blockWord_cons, List.getLast?_append_of_ne_nil]
      · exact getLast?_blockWord (List.cons_ne_nil _ _)
      · simp [blk]

lemma qpCount_blockWord : ∀ {t : List (ℕ × ℕ)}, t ≠ [] → qpCount (blockWord t) + 1 = t.length
  | [p], _ => by simp [qpCount_blk]
  | p :: p' :: t, _ => by
      rw [blockWord_cons, qpCount_append, qpCount_blk, getLast?_blk, blockWord_cons,
        head?_blk_append, ← blockWord_cons]
      have := qpCount_blockWord (t := p' :: t) (List.cons_ne_nil _ _)
      simp only [and_self, ite_true, List.length_cons] at this ⊢
      omega

/-- A linear word reading `P … Q`.-/
def IsPQ (l : List Bool) : Prop := l.head? = some false ∧ l.getLast? = some true

instance : DecidablePred IsPQ := fun _ => inferInstanceAs (Decidable (_ ∧ _))

lemma isPQ_blockWord {t : List (ℕ × ℕ)} (ht : t ≠ []) : IsPQ (blockWord t) := by
  obtain ⟨p, t', rfl⟩ := List.exists_cons_of_ne_nil ht
  exact ⟨by rw [blockWord_cons, head?_blk_append], getLast?_blockWord ht⟩

/-! ### Marks of cyclic words and boundaries of linear words -/

lemma getLast?_ofFn {n : ℕ} (v : Fin (n + 1) → Bool) :
    (List.ofFn v).getLast? = some (v (Fin.last n)) := by
  rw [List.ofFn_succ', List.concat_eq_append, List.getLast?_concat]

lemma sum_lin_qp : ∀ {n : ℕ} (v : Fin (n + 1) → Bool),
    (∑ i : Fin n, if v i.castSucc = true ∧ v i.succ = false then 1 else 0) =
      qpCount (List.ofFn v)
  | 0, v => by simp [List.ofFn_succ, qpCount]
  | n + 1, v => by
      rw [Fin.sum_univ_succ, List.ofFn_succ, List.ofFn_succ]
      have ih := sum_lin_qp (n := n) (fun i => v i.succ)
      rw [List.ofFn_succ] at ih
      simp only [qpCount]
      rw [← ih]
      simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one, Fin.succ_castSucc]
      rfl

/-! ### The bijections -/

/-- **Linear words `P … Q` with `r` `Q`-blocks biject with block-length tuples.**-/
theorem sum_pq_eq_sum_tuples {L r : ℕ} (hr : 1 ≤ r) (h2r : 2 * r ≤ L) (H : List Bool → ℝ) :
    ∑ l ∈ (allWords L).filter (fun l => IsPQ l ∧ qpCount l + 1 = r), H l =
      ∑ t ∈ tuples r (L - 2 * r), H (blockWord t) := by
  symm
  refine Finset.sum_bij (fun t _ => blockWord t) ?_ ?_ ?_ fun _ _ => rfl
  · intro t ht
    rw [mem_tuples] at ht
    have hne : t ≠ [] := by rintro rfl; simp at ht; omega
    rw [Finset.mem_filter, mem_allWords, length_blockWord]
    refine ⟨by omega, isPQ_blockWord hne, ?_⟩
    rw [qpCount_blockWord hne, ht.1]
  · intro t ht t' ht' h
    have := blockWord_append_injective t t' 0 0 (by simpa using h)
    exact this.1
  · intro l hl
    rw [Finset.mem_filter, mem_allWords] at hl
    obtain ⟨hlen, hpq, hqp⟩ := hl
    obtain ⟨t, hne, rfl⟩ := blockWord_of_pq hpq.1 hpq.2
    refine ⟨t, ?_, rfl⟩
    rw [qpCount_blockWord hne] at hqp
    rw [mem_tuples]
    rw [length_blockWord] at hlen
    exact ⟨hqp, by omega⟩

/-- **Linear words not starting with `Q` biject with pairs (block-length tuple, final
`P`-block).**-/
theorem sum_head_ne_true_eq (L : ℕ) (H : List Bool → ℝ) :
    ∑ l ∈ (allWords L).filter (fun l => l.head? ≠ some true), H l =
      ∑ r ∈ range (L + 1), ∑ N ∈ range (L + 1),
        if 2 * r + N ≤ L then
          ∑ t ∈ tuples r N, H (blockWord t ++ List.replicate (L - 2 * r - N) false)
        else 0 := by
  classical
  set S : Finset (Σ _ : ℕ, Σ _ : ℕ, List (ℕ × ℕ)) :=
    (range (L + 1)).sigma fun r => (range (L + 1)).sigma fun N =>
      if 2 * r + N ≤ L then tuples r N else ∅ with hS
  have hRHS : (∑ r ∈ range (L + 1), ∑ N ∈ range (L + 1),
      if 2 * r + N ≤ L then
        ∑ t ∈ tuples r N, H (blockWord t ++ List.replicate (L - 2 * r - N) false)
      else 0) =
      ∑ x ∈ S, H (blockWord x.2.2 ++ List.replicate (L - 2 * x.1 - x.2.1) false) := by
    rw [hS, Finset.sum_sigma]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.sum_sigma]
    refine Finset.sum_congr rfl fun N _ => ?_
    split_ifs <;> simp
  rw [hRHS]
  symm
  refine Finset.sum_bij (fun x _ => blockWord x.2.2 ++ List.replicate (L - 2 * x.1 - x.2.1) false)
    ?_ ?_ ?_ fun _ _ => rfl
  · rintro ⟨r, N, t⟩ hx
    simp only [hS, Finset.mem_sigma, Finset.mem_range] at hx
    obtain ⟨hr, hN, ht⟩ := hx
    dsimp only
    split_ifs at ht with hle
    · rw [mem_tuples] at ht
      rw [Finset.mem_filter, mem_allWords, List.length_append, length_blockWord,
        List.length_replicate]
      exact ⟨by omega, head?_blockWord_append t _⟩
    · simp at ht
  · rintro ⟨r, N, t⟩ hx ⟨r', N', t'⟩ hx' h
    simp only [hS, Finset.mem_sigma, Finset.mem_range] at hx hx'
    obtain ⟨_, _, ht⟩ := hx
    obtain ⟨_, _, ht'⟩ := hx'
    split_ifs at ht ht' with h1 h2
    · rw [mem_tuples] at ht ht'
      obtain ⟨rfl, _⟩ := blockWord_append_injective t t' _ _ h
      obtain ⟨rfl, rfl⟩ := ht
      obtain ⟨hr', hN'⟩ := ht'
      subst hr' hN'
      rfl
    all_goals simp at ht ht'
  · intro l hl
    rw [Finset.mem_filter, mem_allWords] at hl
    obtain ⟨hlen, hhead⟩ := hl
    obtain ⟨t, a, rfl⟩ := exists_blockWord l.length l le_rfl hhead
    rw [List.length_append, length_blockWord, List.length_replicate] at hlen
    refine ⟨⟨t.length, excess t, t⟩, ?_, ?_⟩
    · simp only [hS, Finset.mem_sigma, Finset.mem_range]
      refine ⟨by omega, by omega, ?_⟩
      rw [ite_eq_left (by omega), mem_tuples]
      exact ⟨rfl, rfl⟩
    · show blockWord t ++ List.replicate (L - 2 * t.length - excess t) false =
        blockWord t ++ List.replicate a false
      congr 2
      omega

end OddCycleBound.Excursion
