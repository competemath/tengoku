/-
OEIS A048248: counting the valid lists.

`validSet n` is a concrete finite set containing exactly the lists `l` with `Valid n l`;
its cardinality `c n` satisfies
`c (n+6) = c (n+5) + 5 c (n+4) - 4 c (n+3) - 8 c (n+2) + 4 c (n+1) + 4 c n` for `n ≥ 1`.
-/
import Tengoku.OeisLean.OeisLean.A048248.Defs
import Tengoku.Seed.Combinatorics.Enumerative.Composition

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A048248.mem_validSet` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms A048248.c_recurrence` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms A048248.c_init` (it only prints; the queue checks the axioms of every declaration). -/

namespace A048248

namespace Count

/-! ### All compositions of `n` -/

/-- The finite set of all lists of positive integers with sum `n`.-/
def comps (n : ℕ) : Finset (List ℕ) :=
  (Finset.univ : Finset (Composition n)).image Composition.blocks

theorem mem_comps {n : ℕ} {l : List ℕ} : l ∈ comps n ↔ (∀ x ∈ l, 0 < x) ∧ l.sum = n := by
  unfold comps
  rw [Finset.mem_image]
  constructor
  · rintro ⟨c, -, rfl⟩
    exact ⟨fun x hx => c.blocks_pos hx, c.blocks_sum⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨l, fun {i} hi => h1 i hi, h2⟩, Finset.mem_univ _, rfl⟩

/-- Decomposition of the compositions of `n` by their first element.-/
theorem comps_eq (n : ℕ) :
    comps n = (if n = 0 then {[]} else ∅) ∪
      (Finset.range n).biUnion fun i => (comps (n - (i + 1))).image (fun l => (i + 1) :: l) := by
  ext l
  rw [mem_comps]
  simp only [Finset.mem_union, Finset.mem_biUnion, Finset.mem_image, Finset.mem_range, mem_comps]
  cases l with
  | nil =>
    by_cases h : n = 0
    · subst h; simp
    · simp [h, Ne.symm h]
  | cons a t =>
    constructor
    · rintro ⟨hpos, hsum⟩
      right
      have ha : 0 < a := hpos a (by simp)
      rw [List.sum_cons] at hsum
      refine ⟨a - 1, by omega, t, ⟨fun x hx => hpos x (List.mem_cons_of_mem _ hx), by omega⟩, ?_⟩
      congr 1
      omega
    · rintro (h | ⟨i, hi, l, ⟨hpos, hsum⟩, hl⟩)
      · split_ifs at h <;> simp at h
      · obtain ⟨rfl, rfl⟩ := List.cons.inj hl
        refine ⟨List.forall_mem_cons.2 ⟨by omega, hpos⟩, ?_⟩
        rw [List.sum_cons]
        omega

theorem card_filter (P : List ℕ → Bool) (n : ℕ) :
    ((comps n).filter (fun l => P l = true)).card =
      (if n = 0 ∧ P [] = true then 1 else 0) +
        ∑ i ∈ Finset.range n,
          ((comps (n - (i + 1))).filter (fun l => P ((i + 1) :: l) = true)).card := by
  conv_lhs => rw [comps_eq n]
  rw [Finset.filter_union, Finset.card_union_of_disjoint, Finset.filter_biUnion,
    Finset.card_biUnion]
  · congr 1
    · by_cases h : n = 0
      · subst h
        by_cases hp : P [] = true <;> simp [Finset.filter_singleton, hp]
      · simp [h]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.filter_image, Finset.card_image_of_injective _ (List.cons_injective)]
  · intro x _ y _ hxy
    change Disjoint _ _
    refine Finset.disjoint_filter_filter ?_
    rw [Finset.disjoint_left]
    simp only [Finset.mem_image]
    rintro l ⟨a, -, rfl⟩ ⟨b, -, h⟩
    exact hxy (by have := (List.cons.inj h).1; omega)
  · refine Finset.disjoint_filter_filter ?_
    rw [Finset.disjoint_left]
    intro l h1 h2
    split_ifs at h1
    · simp only [Finset.mem_singleton] at h1
      subst h1
      simp at h2
    · simp at h1

/-! ### The automaton -/

/-- In the last even block.-/
def acc2 : List ℕ → Bool
  | [] => true
  | x :: l => decide (x % 2 = 0) && acc2 l

/-- In the odd block.-/
def acc1 : List ℕ → Bool
  | [] => true
  | x :: l => if x % 2 = 1 then acc1 l else acc2 l

/-- In the first even block.-/
def acc0 : List ℕ → Bool
  | [] => true
  | x :: l => if x % 2 = 0 then acc0 l else acc1 l

theorem acc2_iff (l : List ℕ) : acc2 l = true ↔ ∀ x ∈ l, Even x := by
  induction l with
  | nil => simp [acc2]
  | cons x l ih => simp [acc2, ih, Nat.even_iff]

theorem acc1_iff (l : List ℕ) :
    acc1 l = true ↔ ∃ o e : List ℕ, l = o ++ e ∧ (∀ x ∈ o, Odd x) ∧ (∀ x ∈ e, Even x) := by
  induction l with
  | nil => exact ⟨fun _ => ⟨[], [], rfl, by simp, by simp⟩, fun _ => rfl⟩
  | cons x l ih =>
    change (if x % 2 = 1 then acc1 l else acc2 l) = true ↔ _
    by_cases h : x % 2 = 1
    · rw [ite_eq_left h, ih]
      constructor
      · rintro ⟨o, e, rfl, ho, he⟩
        exact ⟨x :: o, e, rfl, List.forall_mem_cons.2 ⟨Nat.odd_iff.2 h, ho⟩, he⟩
      · rintro ⟨o, e, hl, ho, he⟩
        cases o with
        | nil =>
          exfalso
          simp only [List.nil_append] at hl
          subst hl
          have := (List.forall_mem_cons.1 he).1
          rw [Nat.even_iff] at this
          omega
        | cons y o =>
          simp only [List.cons_append, List.cons.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          exact ⟨o, e, rfl, (List.forall_mem_cons.1 ho).2, he⟩
    · rw [ite_eq_right h, acc2_iff]
      constructor
      · intro hl
        exact ⟨[], x :: l, rfl, by simp,
          List.forall_mem_cons.2 ⟨Nat.even_iff.2 (by omega), hl⟩⟩
      · rintro ⟨o, e, hl, ho, he⟩
        cases o with
        | nil =>
          simp only [List.nil_append] at hl
          subst hl
          exact (List.forall_mem_cons.1 he).2
        | cons y o =>
          exfalso
          simp only [List.cons_append, List.cons.injEq] at hl
          obtain ⟨rfl, -⟩ := hl
          have := (List.forall_mem_cons.1 ho).1
          rw [Nat.odd_iff] at this
          exact h this

theorem acc0_iff (l : List ℕ) :
    acc0 l = true ↔ ∃ e₁ o e₂ : List ℕ, l = e₁ ++ o ++ e₂ ∧
      (∀ x ∈ e₁, Even x) ∧ (∀ x ∈ o, Odd x) ∧ (∀ x ∈ e₂, Even x) := by
  induction l with
  | nil => exact ⟨fun _ => ⟨[], [], [], rfl, by simp, by simp, by simp⟩, fun _ => rfl⟩
  | cons x l ih =>
    change (if x % 2 = 0 then acc0 l else acc1 l) = true ↔ _
    by_cases h : x % 2 = 0
    · rw [ite_eq_left h, ih]
      constructor
      · rintro ⟨e1, o, e2, rfl, h1, ho, h2⟩
        exact ⟨x :: e1, o, e2, rfl, List.forall_mem_cons.2 ⟨Nat.even_iff.2 h, h1⟩, ho, h2⟩
      · rintro ⟨e1, o, e2, hl, h1, ho, h2⟩
        cases e1 with
        | cons y e1 =>
          simp only [List.cons_append, List.cons.injEq] at hl
          obtain ⟨rfl, rfl⟩ := hl
          exact ⟨e1, o, e2, rfl, (List.forall_mem_cons.1 h1).2, ho, h2⟩
        | nil =>
          cases o with
          | cons y o =>
            exfalso
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at hl
            obtain ⟨rfl, -⟩ := hl
            have := (List.forall_mem_cons.1 ho).1
            rw [Nat.odd_iff] at this
            omega
          | nil =>
            simp only [List.nil_append] at hl
            subst hl
            exact ⟨l, [], [], by simp, (List.forall_mem_cons.1 h2).2, by simp, by simp⟩
    · rw [ite_eq_right h, acc1_iff]
      constructor
      · rintro ⟨o, e, rfl, ho, he⟩
        exact ⟨[], x :: o, e, rfl, by simp,
          List.forall_mem_cons.2 ⟨Nat.odd_iff.2 (by omega), ho⟩, he⟩
      · rintro ⟨e1, o, e2, hl, h1, ho, h2⟩
        cases e1 with
        | cons y e1 =>
          exfalso
          simp only [List.cons_append, List.cons.injEq] at hl
          obtain ⟨rfl, -⟩ := hl
          have := (List.forall_mem_cons.1 h1).1
          rw [Nat.even_iff] at this
          exact h this
        | nil =>
          cases o with
          | cons y o =>
            simp only [List.nil_append, List.cons_append, List.cons.injEq] at hl
            obtain ⟨rfl, rfl⟩ := hl
            exact ⟨o, e2, rfl, (List.forall_mem_cons.1 ho).2, h2⟩
          | nil =>
            exfalso
            simp only [List.nil_append] at hl
            subst hl
            have := (List.forall_mem_cons.1 h2).1
            rw [Nat.even_iff] at this
            exact h this

/-! ### Counts per automaton state -/

def N2 (n : ℕ) : ℕ := ((comps n).filter (fun l => acc2 l = true)).card
def N1 (n : ℕ) : ℕ := ((comps n).filter (fun l => acc1 l = true)).card
def N0 (n : ℕ) : ℕ := ((comps n).filter (fun l => acc0 l = true)).card

/-- Sum of `f (n - x)` over even `x` in `[1, n]` (with `x = i + 1`).-/
def Sev (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if (i + 1) % 2 = 0 then f (n - (i + 1)) else 0

/-- Sum of `f (n - x)` over odd `x` in `[1, n]` (with `x = i + 1`).-/
def Sod (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, if (i + 1) % 2 = 1 then f (n - (i + 1)) else 0

theorem Sev_shift (f : ℕ → ℕ) (n : ℕ) : Sev f (n + 2) = f n + Sev f n := by
  unfold Sev
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ i, (i + 1 + 1 + 1) % 2 = (i + 1) % 2 := by intro i; omega
  have h' : ∀ i, n + 2 - (i + 1 + 1 + 1) = n - (i + 1) := by intro i; omega
  simp only [h, h']
  simp
  omega

theorem Sod_shift (f : ℕ → ℕ) (n : ℕ) : Sod f (n + 2) = f (n + 1) + Sod f n := by
  unfold Sod
  rw [Finset.sum_range_succ', Finset.sum_range_succ']
  have h : ∀ i, (i + 1 + 1 + 1) % 2 = (i + 1) % 2 := by intro i; omega
  have h' : ∀ i, n + 2 - (i + 1 + 1 + 1) = n - (i + 1) := by intro i; omega
  simp only [h, h']
  simp
  omega

theorem N2_eq (n : ℕ) : N2 n = (if n = 0 then 1 else 0) + Sev N2 n := by
  rw [N2, card_filter]
  congr 1
  · simp [acc2]
  · unfold Sev
    refine Finset.sum_congr rfl fun i _ => ?_
    generalize i + 1 = x
    by_cases h : x % 2 = 0 <;> simp [acc2, h, N2]

theorem N1_eq (n : ℕ) : N1 n = (if n = 0 then 1 else 0) + Sod N1 n + Sev N2 n := by
  rw [N1, card_filter, add_assoc]
  congr 1
  · simp [acc1]
  · unfold Sod Sev
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    generalize i + 1 = x
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [acc1, h, N1, N2]

theorem N0_eq (n : ℕ) : N0 n = (if n = 0 then 1 else 0) + Sev N0 n + Sod N1 n := by
  rw [N0, card_filter, add_assoc]
  congr 1
  · simp [acc0]
  · unfold Sod Sev
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    generalize i + 1 = x
    rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [acc0, h, N0, N1]

theorem N2_step (n : ℕ) : N2 (n + 2) + (if n = 0 then 1 else 0) = 2 * N2 n := by
  have h1 := N2_eq (n + 2)
  have h2 := N2_eq n
  rw [Sev_shift, ite_eq_right (by omega)] at h1
  omega

theorem N1_step (n : ℕ) :
    N1 (n + 2) + (if n = 0 then 1 else 0) = N1 (n + 1) + N1 n + N2 n := by
  have h1 := N1_eq (n + 2)
  have h2 := N1_eq n
  rw [Sev_shift, Sod_shift, ite_eq_right (by omega)] at h1
  omega

theorem N0_step (n : ℕ) :
    N0 (n + 2) + (if n = 0 then 1 else 0) = 2 * N0 n + N1 (n + 1) := by
  have h1 := N0_eq (n + 2)
  have h2 := N0_eq n
  rw [Sev_shift, Sod_shift, ite_eq_right (by omega)] at h1
  omega

theorem N2_zero : N2 0 = 1 := by have := N2_eq 0; simpa [Sev] using this
theorem N1_zero : N1 0 = 1 := by have := N1_eq 0; simpa [Sev, Sod] using this
theorem N0_zero : N0 0 = 1 := by have := N0_eq 0; simpa [Sev, Sod] using this
theorem N2_one : N2 1 = 0 := by have := N2_eq 1; simpa [Sev] using this
theorem N1_one : N1 1 = 1 := by
  have := N1_eq 1
  unfold Sev Sod at this
  rw [Finset.sum_range_one, Finset.sum_range_one] at this
  simpa [N1_zero] using this
theorem N0_one : N0 1 = 1 := by
  have := N0_eq 1
  unfold Sev Sod at this
  rw [Finset.sum_range_one, Finset.sum_range_one] at this
  simpa [N1_zero] using this

theorem N2_step' (n : ℕ) (hn : 1 ≤ n) : N2 (n + 2) = 2 * N2 n := by
  have := N2_step n
  rw [ite_eq_right (by omega)] at this
  omega

theorem N1_step' (n : ℕ) (hn : 1 ≤ n) : N1 (n + 2) = N1 (n + 1) + N1 n + N2 n := by
  have := N1_step n
  rw [ite_eq_right (by omega)] at this
  omega

theorem N0_step' (n : ℕ) (hn : 1 ≤ n) : N0 (n + 2) = 2 * N0 n + N1 (n + 1) := by
  have := N0_step n
  rw [ite_eq_right (by omega)] at this
  omega

end Count

open Count

/-- A concrete finite set containing exactly the valid lists.-/
def validSet (n : ℕ) : Finset (List ℕ) := (comps n).filter (fun l => acc0 l = true)

theorem mem_validSet (n : ℕ) (l : List ℕ) : l ∈ validSet n ↔ Valid n l := by
  rw [validSet, Finset.mem_filter, mem_comps, acc0_iff]
  exact ⟨fun ⟨⟨hp, hs⟩, h⟩ => ⟨hs, hp, h⟩, fun ⟨hs, hp, h⟩ => ⟨⟨hp, hs⟩, h⟩⟩

def c (n : ℕ) : ℕ := (validSet n).card

theorem c_eq_N0 (n : ℕ) : c n = N0 n := rfl

theorem c_recurrence (n : ℕ) (hn : 1 ≤ n) :
    c (n + 6) + 4 * c (n + 3) + 8 * c (n + 2) =
      c (n + 5) + 5 * c (n + 4) + 4 * c (n + 1) + 4 * c n := by
  simp only [c_eq_N0]
  have a0 : N0 (n + 2) = 2 * N0 n + N1 (n + 1) := N0_step' n hn
  have a1 : N0 (n + 3) = 2 * N0 (n + 1) + N1 (n + 2) := N0_step' (n + 1) (by omega)
  have a2 : N0 (n + 4) = 2 * N0 (n + 2) + N1 (n + 3) := N0_step' (n + 2) (by omega)
  have a3 : N0 (n + 5) = 2 * N0 (n + 3) + N1 (n + 4) := N0_step' (n + 3) (by omega)
  have a4 : N0 (n + 6) = 2 * N0 (n + 4) + N1 (n + 5) := N0_step' (n + 4) (by omega)
  have b1 : N1 (n + 3) = N1 (n + 2) + N1 (n + 1) + N2 (n + 1) := N1_step' (n + 1) (by omega)
  have b2 : N1 (n + 4) = N1 (n + 3) + N1 (n + 2) + N2 (n + 2) := N1_step' (n + 2) (by omega)
  have b3 : N1 (n + 5) = N1 (n + 4) + N1 (n + 3) + N2 (n + 3) := N1_step' (n + 3) (by omega)
  have c1 : N2 (n + 3) = 2 * N2 (n + 1) := N2_step' (n + 1) (by omega)
  omega

theorem c_init : c 1 = 1 ∧ c 2 = 2 ∧ c 3 = 4 ∧ c 4 = 7 ∧ c 5 = 14 ∧ c 6 = 23 ∧ c 7 = 45 := by
  simp only [c_eq_N0]
  have z0 := N0_zero
  have z1 := N1_zero
  have z2 := N2_zero
  have o0 := N0_one
  have o1 := N1_one
  have o2 := N2_one
  have c2 : N2 2 + 1 = 2 * N2 0 := N2_step 0
  have c3 : N2 3 = 2 * N2 1 := N2_step' 1 (by omega)
  have c4 : N2 4 = 2 * N2 2 := N2_step' 2 (by omega)
  have b2 : N1 2 + 1 = N1 1 + N1 0 + N2 0 := N1_step 0
  have b3 : N1 3 = N1 2 + N1 1 + N2 1 := N1_step' 1 (by omega)
  have b4 : N1 4 = N1 3 + N1 2 + N2 2 := N1_step' 2 (by omega)
  have b5 : N1 5 = N1 4 + N1 3 + N2 3 := N1_step' 3 (by omega)
  have b6 : N1 6 = N1 5 + N1 4 + N2 4 := N1_step' 4 (by omega)
  have a2 : N0 2 + 1 = 2 * N0 0 + N1 1 := N0_step 0
  have a3 : N0 3 = 2 * N0 1 + N1 2 := N0_step' 1 (by omega)
  have a4 : N0 4 = 2 * N0 2 + N1 3 := N0_step' 2 (by omega)
  have a5 : N0 5 = 2 * N0 3 + N1 4 := N0_step' 3 (by omega)
  have a6 : N0 6 = 2 * N0 4 + N1 5 := N0_step' 4 (by omega)
  have a7 : N0 7 = 2 * N0 5 + N1 6 := N0_step' 5 (by omega)
  omega

end A048248

