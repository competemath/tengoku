/-
OEIS A307917: the base case `B n L 0` of the counting function `B`, obtained by appending one
position at a time (`Fin.snoc`) and counting the admissible values of the new entry.
-/
import Tengoku.OeisLean.OeisLean.A307917.Defs
import Tengoku.Seed.Data.Fin.Tuple.Basic
import Tengoku.Seed.Data.Fintype.Card
import Tengoku.Seed.Data.Fintype.BigOperators
import Tengoku.Seed.Algebra.BigOperators.Group.Finset.Sigma
import Tengoku.Seed.Tactic.Ring

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A307917.B_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms A307917.B_zero_left` (it only prints; the queue checks the axioms of every declaration). -/

namespace A307917.Base

variable {n L : ℕ}

/-- The functions satisfying `Sp`.-/
def S (n L : ℕ) : Finset (Fin L → Fin n) :=
  Finset.univ.filter fun z : Fin L → Fin n => Sp z

/-- The values that may be appended to `z'` without breaking `Sp`.-/
def allowed (z' : Fin L → Fin n) : Finset (Fin n) :=
  Finset.univ.filter fun v : Fin n => ∀ i : Fin L, i.val % 2 = L % 2 → z' i ≠ v

/-- There are `L / 2` positions below `L` with the parity of `L`.-/
theorem par_card (L : ℕ) :
    ((Finset.univ : Finset (Fin L)).filter fun i => i.val % 2 = L % 2).card = L / 2 := by
  have h : ((Finset.univ : Finset (Fin L)).filter fun i => i.val % 2 = L % 2) =
      (Finset.univ : Finset (Fin (L / 2))).image
        (fun k => (⟨L % 2 + 2 * k.val, by omega⟩ : Fin L)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      exact ⟨⟨i.val / 2, by omega⟩, Fin.ext (by simp only; omega)⟩
    · rintro ⟨k, rfl⟩
      simp only
      omega
  rw [h, Finset.card_image_of_injective, Finset.card_univ, Fintype.card_fin]
  intro a b hab
  have := congrArg Fin.val hab
  simp only at this
  exact Fin.ext (by omega)

theorem Sp_snoc (z' : Fin L → Fin n) (v : Fin n) :
    Sp (Fin.snoc z' v : Fin (L + 1) → Fin n) ↔
      Sp z' ∧ ∀ i : Fin L, i.val % 2 = L % 2 → z' i ≠ v := by
  constructor
  · intro h
    refine ⟨fun i j hij hpar => ?_, fun i hpar => ?_⟩
    · have := h i.castSucc j.castSucc (fun e => hij (Fin.castSucc_injective _ e))
        (by simpa using hpar)
      simpa only [Fin.snoc_castSucc] using this
    · have := h i.castSucc (Fin.last L) (Fin.castSucc_lt_last i).ne (by simpa using hpar)
      simpa only [Fin.snoc_castSucc, Fin.snoc_last] using this
  · rintro ⟨h1, h2⟩ i j hij hpar
    induction i using Fin.lastCases with
    | last =>
      induction j using Fin.lastCases with
      | last => exact absurd rfl hij
      | cast j =>
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact (h2 j (by simpa using hpar.symm)).symm
    | cast i =>
      induction j using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_castSucc, Fin.snoc_last]
        exact h2 i (by simpa using hpar)
      | cast j =>
        simp only [Fin.snoc_castSucc]
        exact h1 i j (fun e => hij (by rw [e])) (by simpa using hpar)

theorem allowed_card (z' : Fin L → Fin n) (h : Sp z') : (allowed z').card = n - L / 2 := by
  have e : allowed z' =
      (((Finset.univ : Finset (Fin L)).filter fun i => i.val % 2 = L % 2).image z')ᶜ := by
    ext v
    simp only [allowed, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl,
      Finset.mem_image, not_exists, not_and, ne_eq]
  rw [e, Finset.card_compl, Fintype.card_fin, Finset.card_image_of_injOn, par_card]
  intro i hi j hj hij
  by_contra hne
  simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
  exact h i j hne (hi.trans hj.symm) hij

theorem S_succ (n L : ℕ) : (S n (L + 1)).card = (S n L).card * (n - L / 2) := by
  have h : ((S n L).sigma fun z' => allowed z').card = (S n (L + 1)).card := by
    apply Finset.card_bij (fun p _ => (Fin.snoc p.1 p.2 : Fin (L + 1) → Fin n))
    · rintro ⟨z', v⟩ hp
      simp only [Finset.mem_sigma, S, allowed, Finset.mem_filter, Finset.mem_univ,
        true_and] at hp ⊢
      exact (Sp_snoc z' v).2 hp
    · rintro ⟨z1, v1⟩ _ ⟨z2, v2⟩ _ h
      obtain ⟨rfl, rfl⟩ := Fin.snoc_injective2 h
      rfl
    · intro z hz
      refine ⟨⟨Fin.init z, z (Fin.last L)⟩, ?_, Fin.snoc_init_self z⟩
      simp only [Finset.mem_sigma, S, allowed, Finset.mem_filter, Finset.mem_univ,
        true_and] at hz ⊢
      apply (Sp_snoc _ _).1
      rw [Fin.snoc_init_self]
      exact hz
  rw [← h, Finset.card_sigma,
    Finset.sum_const_nat fun z hz => allowed_card z (by simpa [S] using hz)]

theorem S_card (n L : ℕ) :
    (S n L).card = n.descFactorial ((L + 1) / 2) * n.descFactorial (L / 2) := by
  induction L with
  | zero =>
    have h : S n 0 = Finset.univ := by
      ext z
      simp only [S, Finset.mem_filter, Finset.mem_univ, true_and, iff_true]
      intro i
      exact i.elim0
    rw [h]
    simp
  | succ L ih =>
    rw [S_succ, ih]
    rcases Nat.even_or_odd' L with ⟨m, rfl | rfl⟩
    · have h1 : (2 * m + 1) / 2 = m := by omega
      have h2 : 2 * m / 2 = m := by omega
      have h3 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      rw [h1, h2, h3, Nat.descFactorial_succ]
      ring
    · have h1 : (2 * m + 1 + 1) / 2 = m + 1 := by omega
      have h2 : (2 * m + 1) / 2 = m := by omega
      have h3 : (2 * m + 1 + 1 + 1) / 2 = m + 1 := by omega
      rw [h1, h2, h3, Nat.descFactorial_succ]
      ring

end A307917.Base

namespace A307917

open Base in
theorem B_zero (n L : ℕ) :
    B n L 0 = n.descFactorial ((L + 1) / 2) * n.descFactorial (L / 2) := by
  rw [← S_card]
  unfold B S
  congr 1
  ext z
  simp

theorem B_zero_left (L c : ℕ) (hL : 1 ≤ L) : B 0 L c = 0 := by
  unfold B
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro z _
  exact (z ⟨0, hL⟩).elim0

end A307917

