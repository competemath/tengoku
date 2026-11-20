/-
OEIS A307917: the recurrence `B_succ` for the counting function `B`, proved by an explicit
bijection (insert two equal neighbouring entries at positions `c`, `c + 1`).
-/
import Tengoku.OeisLean.OeisLean.A307917.Defs
import Tengoku.Seed.Data.Fin.SuccPred
import Tengoku.Seed.Data.Finset.Prod
import Tengoku.Seed.Data.Fintype.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A307917.B_succ` (it only prints; the queue checks the axioms of every declaration). -/

namespace A307917.Step

variable {n L : ℕ}

/-- Embed `Fin L` into `Fin (L + 2)`, skipping the positions `c` and `c + 1`.-/
def skip (c : ℕ) (i : Fin L) : Fin (L + 2) :=
  if i.val < c then ⟨i.val, by omega⟩ else ⟨i.val + 2, by omega⟩

theorem skip_val (c : ℕ) (i : Fin L) :
    ((skip c i).val = i.val ∧ i.val < c) ∨ ((skip c i).val = i.val + 2 ∧ c ≤ i.val) := by
  unfold skip
  split_ifs with h
  · left; exact ⟨rfl, h⟩
  · right; exact ⟨rfl, by omega⟩

/-- Insert the value `v` at positions `c`, `c + 1` and push all other values off `v`.-/
def Ψ (c : ℕ) (hc : c ≤ L) (v : Fin (n + 1)) (z' : Fin L → Fin n) (i : Fin (L + 2)) :
    Fin (n + 1) :=
  if h : i.val < c then v.succAbove (z' ⟨i.val, by omega⟩)
  else if h2 : c + 1 < i.val then v.succAbove (z' ⟨i.val - 2, by omega⟩) else v

theorem Ψ_mid (c : ℕ) (hc : c ≤ L) (v : Fin (n + 1)) (z' : Fin L → Fin n) (i : Fin (L + 2))
    (h : i.val = c ∨ i.val = c + 1) : Ψ c hc v z' i = v := by
  unfold Ψ
  rw [dite_eq_right (show ¬ i.val < c by omega), dite_eq_right (show ¬ c + 1 < i.val by omega)]

theorem cover (c : ℕ) (hc : c ≤ L) (i : Fin (L + 2)) (h : ¬ (i.val = c ∨ i.val = c + 1)) :
    ∃ j : Fin L, skip c j = i := by
  by_cases h1 : i.val < c
  · refine ⟨⟨i.val, by omega⟩, ?_⟩
    unfold skip
    rw [ite_eq_left h1]
  · have h2 : ¬ (i.val - 2 < c) := by omega
    refine ⟨⟨i.val - 2, by omega⟩, ?_⟩
    unfold skip
    rw [ite_eq_right h2]
    exact Fin.ext (by dsimp only; omega)

theorem Ψ_skip (c : ℕ) (hc : c ≤ L) (v : Fin (n + 1)) (z' : Fin L → Fin n) (i : Fin L) :
    Ψ c hc v z' (skip c i) = v.succAbove (z' i) := by
  unfold Ψ skip
  by_cases h : i.val < c
  · simp [h]
  · have h3 : ¬ i.val + 2 < c := by omega
    have h4 : c + 1 < i.val + 2 := by omega
    simp [h, h3, h4]

theorem Ψ_sp (c : ℕ) (hc : c ≤ L) (v : Fin (n + 1)) (z' : Fin L → Fin n) (hz : Sp z') :
    Sp (Ψ c hc v z') := by
  unfold Sp
  intro i j hij hpar
  have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
  unfold Ψ
  split_ifs <;> first
    | (exfalso; omega)
    | exact Fin.succAbove_ne _ _
    | exact (Fin.succAbove_ne _ _).symm
    | exact fun h => hz _ _ (Fin.ne_of_val_ne (by dsimp only; omega)) (by dsimp only; omega)
        (Fin.succAbove_right_injective h)

theorem Ψ_pairs (c : ℕ) (hc : c ≤ L) (v : Fin (n + 1)) (z' : Fin L → Fin n)
    (hz : ∀ i j : Fin L, i.val + 1 = j.val → i.val < c - 1 → z' i ≠ z' j) :
    ∀ i j : Fin (L + 2), i.val + 1 = j.val → i.val < c → Ψ c hc v z' i ≠ Ψ c hc v z' j := by
  intro i j hij hi
  unfold Ψ
  split_ifs <;> first
    | (exfalso; omega)
    | exact Fin.succAbove_ne _ _
    | exact (Fin.succAbove_ne _ _).symm
    | exact fun h => hz _ _ (by dsimp only; omega) (by dsimp only; omega)
        (Fin.succAbove_right_injective h)

theorem Ψ_inj (c : ℕ) (hc : c ≤ L) (v w : Fin (n + 1)) (z' y' : Fin L → Fin n)
    (h : Ψ c hc v z' = Ψ c hc w y') : v = w ∧ z' = y' := by
  have hv : v = w := by
    have := congrFun h ⟨c, by omega⟩
    have a := Ψ_mid c hc v z' ⟨c, by omega⟩ (Or.inl rfl)
    have b := Ψ_mid c hc w y' ⟨c, by omega⟩ (Or.inl rfl)
    exact a.symm.trans (this.trans b)
  subst hv
  refine ⟨rfl, funext fun i => ?_⟩
  have := congrFun h (skip c i)
  rw [Ψ_skip, Ψ_skip] at this
  exact Fin.succAbove_right_injective this

theorem Ψ_surj (c : ℕ) (hc : c ≤ L) (z : Fin (L + 2) → Fin (n + 1)) (hs : Sp z)
    (hp : ∀ i j : Fin (L + 2), i.val + 1 = j.val → i.val < c → z i ≠ z j)
    (he : z ⟨c, by omega⟩ = z ⟨c + 1, by omega⟩) :
    ∃ (v : Fin (n + 1)) (z' : Fin L → Fin n), Sp z' ∧
      (∀ i j : Fin L, i.val + 1 = j.val → i.val < c - 1 → z' i ≠ z' j) ∧ Ψ c hc v z' = z := by
  obtain ⟨v, hv⟩ : ∃ v, v = z ⟨c, by omega⟩ := ⟨_, rfl⟩
  have hne : ∀ i : Fin L, z (skip c i) ≠ v := by
    intro i
    have hi := skip_val c i
    rw [hv]
    by_cases hpar : (skip c i).val % 2 = c % 2
    · exact hs _ _ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega) hpar
    · rw [he]
      exact hs _ _ (fun h => by have := congrArg Fin.val h; dsimp only at this; omega)
        (by dsimp only; omega)
  have key : ∀ i : Fin L, ∃ y, v.succAbove y = z (skip c i) :=
    fun i => Fin.exists_succAbove_eq (hne i)
  choose z' hz' using key
  refine ⟨v, z', ?_, ?_, ?_⟩
  · intro i j hij hpar heq
    have hij' : i.val ≠ j.val := fun h => hij (Fin.ext h)
    have hi := skip_val c i
    have hj := skip_val c j
    refine hs (skip c i) (skip c j) (fun h => ?_) (by omega) (by rw [← hz' i, ← hz' j, heq])
    have := congrArg Fin.val h
    omega
  · intro i j hij hi heq
    have hi' := skip_val c i
    have hj' := skip_val c j
    exact hp (skip c i) (skip c j) (by omega) (by omega) (by rw [← hz' i, ← hz' j, heq])
  · funext i
    by_cases hm : i.val = c ∨ i.val = c + 1
    · rw [Ψ_mid c hc v z' i hm]
      rcases hm with h | h
      · have : i = ⟨c, by omega⟩ := Fin.ext h
        rw [this, hv]
      · have : i = ⟨c + 1, by omega⟩ := Fin.ext h
        rw [this, hv, he]
    · obtain ⟨j, rfl⟩ := cover c hc i hm
      rw [Ψ_skip]
      exact hz' j

theorem bad_card (c : ℕ) (hc : c ≤ L) (S : Finset (Fin (L + 2) → Fin (n + 1)))
    (T : Finset (Fin L → Fin n))
    (hS : ∀ z, z ∈ S ↔ (Sp z ∧ ∀ i j : Fin (L + 2), i.val + 1 = j.val → i.val < c → z i ≠ z j) ∧
      z ⟨c, by omega⟩ = z ⟨c + 1, by omega⟩)
    (hT : ∀ z', z' ∈ T ↔
      Sp z' ∧ ∀ i j : Fin L, i.val + 1 = j.val → i.val < c - 1 → z' i ≠ z' j) :
    (n + 1) * T.card = S.card := by
  have h : ((Finset.univ : Finset (Fin (n + 1))) ×ˢ T).card = S.card := by
    refine Finset.card_bij (fun p _ => Ψ c hc p.1 p.2) ?_ ?_ ?_
    · intro p hp
      rw [Finset.mem_product] at hp
      rw [hS]
      have := (hT _).1 hp.2
      exact ⟨⟨Ψ_sp c hc _ _ this.1, Ψ_pairs c hc _ _ this.2⟩,
        (Ψ_mid c hc _ _ ⟨c, by omega⟩ (Or.inl rfl)).trans
          (Ψ_mid c hc _ _ ⟨c + 1, by omega⟩ (Or.inr rfl)).symm⟩
    · intro p _ q _ h
      obtain ⟨h1, h2⟩ := Ψ_inj c hc _ _ _ _ h
      exact Prod.ext h1 h2
    · intro z hz
      rw [hS] at hz
      obtain ⟨v, z', h1, h2, h3⟩ := Ψ_surj c hc z hz.1.1 hz.1.2 hz.2
      exact ⟨(v, z'), Finset.mem_product.2 ⟨Finset.mem_univ _, (hT _).2 ⟨h1, h2⟩⟩, h3⟩
  rw [← h, Finset.card_product, Finset.card_univ, Fintype.card_fin]

end A307917.Step

namespace A307917

theorem B_succ (n L c : ℕ) (hc : c ≤ L) :
    B (n + 1) (L + 2) (c + 1) + (n + 1) * B n L (c - 1) = B (n + 1) (L + 2) c := by
  unfold B
  refine Eq.trans ?_ (Finset.card_filter_add_card_filter_not
    (fun z : Fin (L + 2) → Fin (n + 1) => z ⟨c, by omega⟩ ≠ z ⟨c + 1, by omega⟩))
  congr 1
  · refine congrArg Finset.card (Finset.ext fun z => ?_)
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hs, hp⟩
      refine ⟨⟨hs, fun i j hij hi => hp i j hij (by omega)⟩, hp _ _ rfl (by dsimp only; omega)⟩
    · rintro ⟨⟨hs, hp⟩, hne⟩
      refine ⟨hs, fun i j hij hi => ?_⟩
      by_cases h : i.val < c
      · exact hp i j hij h
      · have e1 : z i = z ⟨c, by omega⟩ := congrArg z (Fin.ext (by dsimp only; omega))
        have e2 : z j = z ⟨c + 1, by omega⟩ := congrArg z (Fin.ext (by dsimp only; omega))
        rw [e1, e2]
        exact hne
  · refine Step.bad_card c hc _ _ (fun z => ?_) (fun z' => ?_)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, ne_eq, not_not]
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]

end A307917

