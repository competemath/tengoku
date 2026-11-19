import Tengoku.OddcyclegoodmanLean.OddCycleBound.Excursion.Words
import Tengoku.OddcyclegoodmanLean.OddCycleBound.DenseRegion.Expansion

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Block-length tuples and their weighted sums

The tuples `(α₁, β₁, …, α_r, β_r)` of nonnegative integers with `∑ (αᵢ + βᵢ) = N` are lists of
pairs (`tuples r N`). Words read as block pairs `P^{α+1} Q^{β+1}` are in bijection with them
(`sum_pq_eq_sum_tuples` for linear words from `P` to `Q`, `sum_head_ne_true_eq` for linear words
not starting with `Q`). The weighted sum `∑ q^{∑α} ∏ s(βᵢ)` over tuples is
`∑_j h_{N-j}(q^{×r}) · momentConv s r j` (`tupleSum_eq`).
-/

open Finset

namespace OddCycleBound.Excursion

open DenseRegion

/-! ### Convolution of sequences -/

/-- The convolution `(f ⋆ g)(n) = ∑_{i ≤ n} f(i) g(n - i)`.-/
def conv (f g : ℕ → ℝ) (n : ℕ) : ℝ := ∑ i ∈ range (n + 1), f i * g (n - i)

lemma conv_comm (f g : ℕ → ℝ) : conv f g = conv g f := by
  funext n
  unfold conv
  rw [← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mem_range] at hi
  rw [show n + 1 - 1 - i = n - i by omega, show n - (n - i) = i by omega, mul_comm]

lemma conv_assoc (f g h : ℕ → ℝ) : conv (conv f g) h = conv f (conv g h) := by
  funext n
  simp only [conv, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_sigma', Finset.sum_sigma']
  refine Finset.sum_nbij' (fun p => ⟨p.2, p.1 - p.2⟩) (fun p => ⟨p.1 + p.2, p.1⟩)
    ?_ ?_ ?_ ?_ ?_
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    omega
  · rintro ⟨j, k⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp ⊢
    omega
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    show (⟨j + (i - j), j⟩ : Σ _ : ℕ, ℕ) = ⟨i, j⟩
    rw [show j + (i - j) = i by omega]
  · rintro ⟨j, k⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    show (⟨j, j + k - j⟩ : Σ _ : ℕ, ℕ) = ⟨j, k⟩
    rw [show j + k - j = k by omega]
  · rintro ⟨i, j⟩ hp
    simp only [Finset.mem_sigma, Finset.mem_range] at hp
    show f j * g (i - j) * h (n - i) = f j * (g (i - j) * h (n - j - (i - j)))
    rw [show n - j - (i - j) = n - i by omega]
    ring

lemma conv_left_comm (f g h : ℕ → ℝ) : conv f (conv g h) = conv g (conv f h) := by
  rw [← conv_assoc, conv_comm f g, conv_assoc]

lemma conv_conv_conv_comm (a b c d : ℕ → ℝ) :
    conv a (conv b (conv c d)) = conv (conv a c) (conv b d) := by
  rw [conv_left_comm b c d, conv_assoc]

/-- `h_d(y, x₁, …, x_k) = ∑_i y^i h_{d-i}(x₁, …, x_k)`.-/
lemma hsym_cons_eq_conv (y : ℝ) (L : List ℝ) :
    (fun d => hsym (y :: L) d) = conv (fun i => y ^ i) (fun d => hsym L d) := by
  funext d; rw [hsym_cons]; rfl

lemma momentConv_succ_eq_conv (s : ℕ → ℝ) (r : ℕ) :
    momentConv s (r + 1) = conv s (momentConv s r) := by
  funext j; rw [momentConv_succ]; rfl

/-! ### Tuples -/

/-- Block-length tuples with `r` pairs and total excess `N`.-/
def tuples (r N : ℕ) : Finset (List (ℕ × ℕ)) :=
  (listsOf (range (N + 1) ×ˢ range (N + 1)) r).filter fun t => excess t = N

lemma le_excess_of_mem {t : List (ℕ × ℕ)} {p : ℕ × ℕ} (hp : p ∈ t) : p.1 + p.2 ≤ excess t := by
  induction t with
  | nil => simp at hp
  | cons a t ih =>
      rw [excess_cons]
      rcases List.mem_cons.mp hp with rfl | hp
      · omega
      · have := ih hp; omega

lemma mem_listsOf_filter_excess {r N M : ℕ} (hM : M ≤ N) {t : List (ℕ × ℕ)} :
    t ∈ (listsOf (range (N + 1) ×ˢ range (N + 1)) r).filter (fun t => excess t = M) ↔
      t.length = r ∧ excess t = M := by
  rw [Finset.mem_filter, mem_listsOf]
  constructor
  · rintro ⟨⟨hlen, _⟩, hex⟩; exact ⟨hlen, hex⟩
  · rintro ⟨hlen, hex⟩
    refine ⟨⟨hlen, fun p hp => ?_⟩, hex⟩
    have := le_excess_of_mem hp
    simp only [Finset.mem_product, Finset.mem_range]
    omega

lemma mem_tuples {r N : ℕ} {t : List (ℕ × ℕ)} :
    t ∈ tuples r N ↔ t.length = r ∧ excess t = N :=
  mem_listsOf_filter_excess le_rfl

lemma sum_tuples_succ (r N : ℕ) (G : List (ℕ × ℕ) → ℝ) :
    ∑ t ∈ tuples (r + 1) N, G t =
      ∑ a ∈ range (N + 1), ∑ b ∈ range (N - a + 1),
        ∑ t ∈ tuples r (N - a - b), G ((a, b) :: t) := by
  set S := range (N + 1) ×ˢ range (N + 1) with hS
  rw [tuples, Finset.sum_filter, ← hS, sum_listsOf_succ, hS, Finset.sum_product]
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Finset.mem_range] at ha
  have hsplit : ∀ b ∈ range (N + 1), (∑ t ∈ listsOf S r,
      if excess ((a, b) :: t) = N then G ((a, b) :: t) else 0) =
      if a + b ≤ N then ∑ t ∈ tuples r (N - a - b), G ((a, b) :: t) else 0 := by
    intro b _
    split_ifs with hab
    · rw [← Finset.sum_filter]
      refine Finset.sum_congr ?_ fun _ _ => rfl
      ext t
      rw [Finset.mem_filter, mem_tuples, mem_listsOf, excess_cons]
      constructor
      · rintro ⟨⟨hlen, _⟩, hex⟩; exact ⟨hlen, by simp at hex; omega⟩
      · rintro ⟨hlen, hex⟩
        refine ⟨⟨hlen, fun p hp => ?_⟩, by simp; omega⟩
        have := le_excess_of_mem hp
        simp only [hS, Finset.mem_product, Finset.mem_range]
        omega
    · refine Finset.sum_eq_zero fun t _ => ?_
      rw [ite_eq_right]
      rw [excess_cons]; simp only; omega
  rw [Finset.sum_congr rfl hsplit, ← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext b
  simp only [Finset.mem_filter, Finset.mem_range]
  omega

/-- The weight `∏ q^{αᵢ} s(βᵢ)` of a block-length tuple.-/
noncomputable def tupleWeight (q : ℝ) (s : ℕ → ℝ) (t : List (ℕ × ℕ)) : ℝ :=
  (t.map fun p => q ^ p.1 * s p.2).prod

@[simp] lemma tupleWeight_nil (q : ℝ) (s : ℕ → ℝ) : tupleWeight q s [] = 1 := rfl

@[simp] lemma tupleWeight_cons (q : ℝ) (s : ℕ → ℝ) (p : ℕ × ℕ) (t : List (ℕ × ℕ)) :
    tupleWeight q s (p :: t) = q ^ p.1 * s p.2 * tupleWeight q s t := by
  simp [tupleWeight]

/-- `∑_{tuples} q^{∑α} ∏ s(βᵢ)`.-/
noncomputable def tupleSum (q : ℝ) (s : ℕ → ℝ) (r N : ℕ) : ℝ :=
  ∑ t ∈ tuples r N, tupleWeight q s t

lemma tupleSum_zero (q : ℝ) (s : ℕ → ℝ) (N : ℕ) :
    tupleSum q s 0 N = if N = 0 then 1 else 0 := by
  unfold tupleSum
  by_cases hN : N = 0
  · subst hN
    rw [ite_eq_left rfl, Finset.sum_eq_single []]
    · exact tupleWeight_nil q s
    · intro t ht hne
      rw [mem_tuples, List.length_eq_zero_iff] at ht
      exact absurd ht.1 hne
    · intro h; exact (h (mem_tuples.mpr ⟨rfl, rfl⟩)).elim
  · rw [ite_eq_right hN]
    refine Finset.sum_eq_zero fun t ht => ?_
    rw [mem_tuples, List.length_eq_zero_iff] at ht
    obtain ⟨rfl, h⟩ := ht
    exact absurd h.symm hN

lemma tupleSum_succ (q : ℝ) (s : ℕ → ℝ) (r : ℕ) :
    tupleSum q s (r + 1) = conv (fun i => q ^ i) (conv s (tupleSum q s r)) := by
  funext N
  unfold tupleSum conv
  rw [sum_tuples_succ]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr (by rw [Nat.sub_sub]) fun t _ => ?_
  rw [tupleWeight_cons]
  ring

/-- **The tuple sum.** `∑_{(α,β) ∈ tuples r N} q^{∑α} ∏ s(βᵢ) = ∑_j h_{N-j}(q^{×r}) ·
momentConv s r j`.-/
theorem tupleSum_eq (q : ℝ) (s : ℕ → ℝ) : ∀ r : ℕ,
    tupleSum q s r = conv (fun d => hsym (List.replicate r q) d) (momentConv s r)
  | 0 => by
      funext N
      rw [tupleSum_zero]
      unfold conv
      rw [Finset.sum_eq_single 0]
      · simp only [List.replicate_zero, hsym_nil, ite_true, one_mul, Nat.sub_zero]
        cases N <;> simp
      · intro i _ hi; simp [hi]
      · intro h; simp at h
  | r + 1 => by
      rw [tupleSum_succ, tupleSum_eq q s r, conv_conv_conv_comm, List.replicate_succ,
        hsym_cons_eq_conv, momentConv_succ_eq_conv]

/-! ### The bijections between words and tuples -/

/-- Linear words from `P` to `Q` with `r` `Q`-blocks are `blockWord t` with `t ∈ tuples r N`.-/
lemma blockWord_of_pq {l : List Bool} (hl : l.head? = some false) (hl' : l.getLast? = some true) :
    ∃ t, t ≠ [] ∧ l = blockWord t := by
  obtain ⟨t, a, rfl⟩ := exists_blockWord l.length l le_rfl (by rw [hl]; simp)
  cases a with
  | zero =>
      refine ⟨t, ?_, by simp⟩
      rintro rfl; simp at hl
  | succ a =>
      exfalso
      rw [List.replicate_succ', ← List.append_assoc, List.getLast?_concat] at hl'
      simp at hl'

end OddCycleBound.Excursion
