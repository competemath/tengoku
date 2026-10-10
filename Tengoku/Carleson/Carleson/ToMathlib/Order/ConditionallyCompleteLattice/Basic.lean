module

public import Tengoku

public section

-- Upstreaming status: ready

/--
@isnad1 id=le.2h5v.s6.1f0fcee70b61 from=translated src=- shape=5a2da1cb vocab=457fa91f
-/
theorem ciSup_le_ciSup {α : Type*} {ι ι' : Sort*} [Nonempty ι] [ConditionallyCompleteLattice α]
  {f : ι → α} {g : ι' → α} (h₀ : ∀ i, ∃ j, f i ≤ g j) (hg : BddAbove (Set.range g)) :
    ⨆ i, f i ≤ ⨆ j, g j := by
  apply ciSup_le
  intro i
  rcases h₀ i with ⟨j, hj⟩
  apply le_ciSup_of_le hg _ hj

--currently unused
/--
@isnad1 id=eq.2h5v.s6.9bce3b198fad from=translated src=- shape=9886736f vocab=7ff99aae
-/
theorem ciSup_eq_ciSup {α : Type*} {ι ι' : Sort*} [ConditionallyCompleteLinearOrder α]
  {f : ι → α} {g : ι' → α} (h₀ : ∀ i, ∃ j, f i ≤ g j) (h₁ : ∀ j, ∃ i, g j ≤ f i) :
    ⨆ i, f i = ⨆ j, g j := by
  by_cases hι : Nonempty ι
  · by_cases hι' : Nonempty ι'
    · by_cases hf : BddAbove (Set.range f)
      · by_cases hg : BddAbove (Set.range g)
        · apply le_antisymm
          · apply ciSup_le_ciSup h₀ hg
          · apply ciSup_le_ciSup h₁ hf
        exfalso
        rw [bddAbove_def] at hf
        rcases hf with ⟨y, hy⟩
        rw [not_bddAbove_iff] at hg
        rcases hg y with ⟨x, hx⟩
        rcases hx.1 with ⟨j, hj⟩
        rcases h₁ j with ⟨i, hi⟩
        have := hy (f i) (by simp)
        rw [hj] at hi
        exact lt_irrefl _ ((hx.2.trans_le hi).trans_le this)
      have hg : ¬BddAbove (Set.range g) := by
        intro hg
        rw [bddAbove_def] at hg
        rcases hg with ⟨x, hx⟩
        rw [not_bddAbove_iff] at hf
        rcases hf x with ⟨y, hy⟩
        rcases hy.1 with ⟨i, hi⟩
        rcases h₀ i with ⟨j, hj⟩
        have := hx (g j) (by simp)
        rw [hi] at hj
        exact lt_irrefl _ ((hy.2.trans_le hj).trans_le this)
      rw [ciSup_of_not_bddAbove hf, ciSup_of_not_bddAbove hg]
    exfalso
    rcases hι with ⟨i⟩
    rcases h₀ i with ⟨j, _⟩
    exact hι' ⟨j⟩
  have hι' : ¬ Nonempty ι' := by
    intro ⟨j⟩
    rcases h₁ j with ⟨i, _⟩
    exact hι ⟨i⟩
  push Not at hι hι'
  rw [iSup_of_empty', iSup_of_empty']

/--
@isnad1 id=eq.0h1v.s6.faa8d29f5adb from=translated src=- shape=a2893651 vocab=b8e6ed2f
-/
@[simp]
theorem WithTop.iSup_coe_eq_top' {α : Type*} [ConditionallyCompleteLinearOrderBot α] [NoTopOrder α] :
  ⨆ (i : α), ↑i = (⊤ : WithTop α) := by
  rw [WithTop.iSup_coe_eq_top]
  simp
