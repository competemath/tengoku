/-
OEIS A347722, step D: the recurrence `D n (c + 1) + c * D (n - 2) (c - 1) = D n c`.

The maps counted by `D n c` split according to whether the point `c` is bad. Those in which it
is not are counted by `D n (c + 1)`. Those in which it is bad consist of a fixed point `c` whose
only other preimage is some `u < c` (`c` choices). Deleting the two points `u` and `c` and
relabelling the remaining `n - 2` points increasingly (`emb`, with inverse `inv`) is a bijection
onto the maps counted by `D (n - 2) (c - 1)`: the relabelling preserves the order, and exactly
`c - 1` of the surviving points lie below `c`. `Phi` is the inverse direction of this bijection
(it reinserts `u` and `c`), `Psi` the deletion.
-/
import Tengoku.OeisLean.OeisLean.A347722.Defs
import Tengoku.Seed.Data.Finset.Prod
import Tengoku.Seed.Data.Fintype.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A347722.D_succ` (it only prints; the queue checks the axioms of every declaration). -/

namespace A347722.StepD

/-! ### The relabelling on natural numbers -/

/-- The increasing map `ℕ → ℕ` whose range is the complement of `{a, b}` (for `a < b`).-/
def emb (a b i : ℕ) : ℕ := if i < a then i else if i + 1 < b then i + 1 else i + 2

/-- Left inverse of `emb a b`.-/
def inv (a b w : ℕ) : ℕ := if w < a then w else if w < b then w - 1 else w - 2

theorem emb_lt (a b i m : ℕ) (hi : i < m) : emb a b i < m + 2 := by
  simp only [emb]; split_ifs <;> omega

theorem emb_ne_a (a b i : ℕ) (_h : a < b) : emb a b i ≠ a := by
  simp only [emb]; split_ifs <;> omega

theorem emb_ne_b (a b i : ℕ) (h : a < b) : emb a b i ≠ b := by
  simp only [emb]; split_ifs <;> omega

theorem inv_emb (a b i : ℕ) (_h : a < b) : inv a b (emb a b i) = i := by
  simp only [emb, inv]; split_ifs <;> omega

theorem emb_inv (a b w : ℕ) (h : a < b) (h1 : w ≠ a) (h2 : w ≠ b) : emb a b (inv a b w) = w := by
  simp only [emb, inv]; split_ifs <;> omega

theorem inv_lt (a b w m : ℕ) (h : a < b) (hb : b < m + 2) (hw : w < m + 2) (h1 : w ≠ a)
    (h2 : w ≠ b) : inv a b w < m := by
  simp only [inv]; split_ifs <;> omega

theorem emb_lt_emb (a b i j : ℕ) : emb a b i < emb a b j ↔ i < j := by
  simp only [emb]; split_ifs <;> omega

theorem emb_lt_b (a b i : ℕ) (h : a < b) : emb a b i < b ↔ i < b - 1 := by
  simp only [emb]; split_ifs <;> omega

/-! ### The relabelling on `Fin` -/

variable {m : ℕ} {u cc : Fin (m + 2)}

/-- The increasing embedding `Fin m → Fin (m + 2)` missing `u` and `cc`.-/
def E (u cc : Fin (m + 2)) (i : Fin m) : Fin (m + 2) := ⟨emb u cc i, emb_lt _ _ _ _ i.isLt⟩

/-- The inverse of `E` on the complement of `{u, cc}`.-/
def R (u cc : Fin (m + 2)) (h : u < cc) (w : Fin (m + 2)) (hw : ¬(w = u ∨ w = cc)) : Fin m :=
  ⟨inv u cc w, inv_lt _ _ _ _ (Fin.lt_def.mp h) cc.isLt w.isLt
    (fun e => hw (Or.inl (Fin.ext e))) (fun e => hw (Or.inr (Fin.ext e)))⟩

theorem E_ne_u (h : u < cc) (i : Fin m) : E u cc i ≠ u := fun H =>
  emb_ne_a _ _ _ (Fin.lt_def.mp h) (congrArg Fin.val H)

theorem E_ne_cc (h : u < cc) (i : Fin m) : E u cc i ≠ cc := fun H =>
  emb_ne_b _ _ _ (Fin.lt_def.mp h) (congrArg Fin.val H)

theorem E_inj (h : u < cc) {i j : Fin m} (H : E u cc i = E u cc j) : i = j := by
  have h1 : emb u cc i = emb u cc j := congrArg Fin.val H
  have h2 := inv_emb u cc i (Fin.lt_def.mp h)
  rw [h1, inv_emb u cc j (Fin.lt_def.mp h)] at h2
  exact Fin.ext h2.symm

theorem E_R (h : u < cc) (w : Fin (m + 2)) (hw : ¬(w = u ∨ w = cc)) :
    E u cc (R u cc h w hw) = w :=
  Fin.ext (emb_inv _ _ _ (Fin.lt_def.mp h)
    (fun e => hw (Or.inl (Fin.ext e))) (fun e => hw (Or.inr (Fin.ext e))))

theorem R_E (h : u < cc) (i : Fin m) (hw : ¬(E u cc i = u ∨ E u cc i = cc)) :
    R u cc h (E u cc i) hw = i :=
  Fin.ext (inv_emb _ _ _ (Fin.lt_def.mp h))

theorem cases (h : u < cc) (w : Fin (m + 2)) : w = u ∨ w = cc ∨ ∃ i, w = E u cc i := by
  by_cases hw : w = u ∨ w = cc
  · rcases hw with e | e
    · exact Or.inl e
    · exact Or.inr (Or.inl e)
  · exact Or.inr (Or.inr ⟨R u cc h w hw, (E_R h w hw).symm⟩)

theorem E_lt_iff (_h : u < cc) {i j : Fin m} : E u cc i < E u cc j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def]; exact emb_lt_emb _ _ _ _

theorem E_val_lt (h : u < cc) (i : Fin m) : (E u cc i).val < cc.val ↔ i.val < cc.val - 1 :=
  emb_lt_b _ _ _ (Fin.lt_def.mp h)

/-! ### The bijection -/

/-- Reinsert the edge `u → cc`: `cc` becomes a fixed point with the single leaf `u`.-/
def Phi (u cc : Fin (m + 2)) (h : u < cc) (g' : Fin m → Fin m) (w : Fin (m + 2)) : Fin (m + 2) :=
  if hw : w = u ∨ w = cc then cc else E u cc (g' (R u cc h w hw))

/-- Delete the points `u` and `cc` (the value is irrelevant where `g` leaves the range of `E`).-/
def Psi (u cc : Fin (m + 2)) (h : u < cc) (g : Fin (m + 2) → Fin (m + 2)) (i : Fin m) : Fin m :=
  if hw : g (E u cc i) = u ∨ g (E u cc i) = cc then i else R u cc h (g (E u cc i)) hw

theorem Phi_u (h : u < cc) (g' : Fin m → Fin m) : Phi u cc h g' u = cc := by
  simp [Phi]

theorem Phi_cc (h : u < cc) (g' : Fin m → Fin m) : Phi u cc h g' cc = cc := by
  simp [Phi]

theorem Phi_E (h : u < cc) (g' : Fin m → Fin m) (i : Fin m) :
    Phi u cc h g' (E u cc i) = E u cc (g' i) := by
  have hw : ¬(E u cc i = u ∨ E u cc i = cc) := not_or.mpr ⟨E_ne_u h i, E_ne_cc h i⟩
  unfold Phi
  rw [dite_eq_right hw, R_E]

theorem E_Psi (h : u < cc) (g : Fin (m + 2) → Fin (m + 2)) (i : Fin m)
    (hw : ¬(g (E u cc i) = u ∨ g (E u cc i) = cc)) : E u cc (Psi u cc h g i) = g (E u cc i) := by
  unfold Psi
  rw [dite_eq_right hw, E_R]

theorem Phi_eq_cc (h : u < cc) (g' : Fin m → Fin m) {w : Fin (m + 2)}
    (hw : Phi u cc h g' w = cc) : w = u ∨ w = cc := by
  rcases cases h w with e | e | ⟨i, e⟩
  · exact Or.inl e
  · exact Or.inr e
  · rw [e, Phi_E] at hw
    exact absurd hw (E_ne_cc h _)

theorem badAt_Phi_E (h : u < cc) (g' : Fin m → Fin m) (i : Fin m) :
    BadAt (Phi u cc h g') (E u cc i) ↔ BadAt g' i := by
  constructor
  · rintro ⟨hfix, x, hx, hgx, huniq⟩
    rw [Phi_E] at hfix
    rcases cases h x with e | e | ⟨j, e⟩
    · rw [e, Phi_u] at hgx
      exact absurd hgx.symm (E_ne_cc h i)
    · rw [e, Phi_cc] at hgx
      exact absurd hgx.symm (E_ne_cc h i)
    · rw [e, Phi_E] at hgx
      rw [e] at hx
      refine ⟨E_inj h hfix, j, (E_lt_iff h).mp hx, E_inj h hgx, fun w hw => ?_⟩
      have hw' : Phi u cc h g' (E u cc w) = E u cc i := by rw [Phi_E, hw]
      rcases huniq (E u cc w) hw' with e' | e'
      · left; rw [e] at e'; exact E_inj h e'
      · right; exact E_inj h e'
  · rintro ⟨hfix, j, hj, hgj, huniq⟩
    refine ⟨by rw [Phi_E, hfix], E u cc j, (E_lt_iff h).mpr hj, by rw [Phi_E, hgj],
      fun w hw => ?_⟩
    rcases cases h w with e | e | ⟨k, e⟩
    · rw [e, Phi_u] at hw
      exact absurd hw.symm (E_ne_cc h i)
    · rw [e, Phi_cc] at hw
      exact absurd hw.symm (E_ne_cc h i)
    · rw [e, Phi_E] at hw
      rcases huniq k (E_inj h hw) with e' | e'
      · left; rw [e, e']
      · right; rw [e, e']

theorem Phi_mem (h : u < cc) (g' : Fin m → Fin m) (hI : Idem g')
    (hB : ∀ v : Fin m, v.val < cc.val - 1 → ¬BadAt g' v) :
    Idem (Phi u cc h g') ∧ (∀ v : Fin (m + 2), v.val < cc.val → ¬BadAt (Phi u cc h g') v) ∧
      BadAt (Phi u cc h g') cc := by
  refine ⟨?_, ?_, ?_⟩
  · intro w
    rcases cases h w with e | e | ⟨i, e⟩
    · rw [e, Phi_u, Phi_cc]
    · rw [e, Phi_cc, Phi_cc]
    · rw [e, Phi_E, Phi_E, hI i]
  · intro v hv hbad
    rcases cases h v with e | e | ⟨i, e⟩
    · rw [e] at hbad
      have h1 := hbad.1
      rw [Phi_u] at h1
      exact absurd h1.symm (ne_of_lt h)
    · rw [e] at hv
      exact lt_irrefl _ hv
    · rw [e] at hv hbad
      exact hB i ((E_val_lt h i).mp hv) ((badAt_Phi_E h g' i).mp hbad)
  · exact ⟨Phi_cc h g', u, h, Phi_u h g', fun w hw => Phi_eq_cc h g' hw⟩

theorem Psi_spec (h : u < cc) (g : Fin (m + 2) → Fin (m + 2)) (hI : Idem g)
    (hB : ∀ v : Fin (m + 2), v.val < cc.val → ¬BadAt g v) (hbad : BadAt g cc) (hu : g u = cc) :
    (Idem (Psi u cc h g) ∧ ∀ v : Fin m, v.val < cc.val - 1 → ¬BadAt (Psi u cc h g) v) ∧
      Phi u cc h (Psi u cc h g) = g := by
  obtain ⟨hfix, u0, -, -, huniq⟩ := hbad
  have hne : u ≠ cc := ne_of_lt h
  have key : ∀ w, g w = cc → w = u ∨ w = cc := by
    intro w hw
    rcases huniq u hu with e | e
    · rw [e]; exact huniq w hw
    · exact absurd e hne
  have nou : ∀ w, g w ≠ u := by
    intro w hw
    have h1 := hI w
    rw [hw, hu] at h1
    exact hne h1.symm
  have hE : ∀ i, E u cc (Psi u cc h g i) = g (E u cc i) := by
    intro i
    apply E_Psi
    rintro (e | e)
    · exact nou _ e
    · rcases key _ e with e' | e'
      · exact E_ne_u h i e'
      · exact E_ne_cc h i e'
  have hPhi : Phi u cc h (Psi u cc h g) = g := by
    funext w
    rcases cases h w with e | e | ⟨i, e⟩
    · rw [e, Phi_u, hu]
    · rw [e, Phi_cc, hfix]
    · rw [e, Phi_E, hE]
  refine ⟨⟨?_, ?_⟩, hPhi⟩
  · intro i
    apply E_inj h
    calc E u cc (Psi u cc h g (Psi u cc h g i)) = g (E u cc (Psi u cc h g i)) := hE _
      _ = g (g (E u cc i)) := by rw [hE i]
      _ = g (E u cc i) := hI _
      _ = E u cc (Psi u cc h g i) := (hE i).symm
  · intro v hv hb
    have hb' := (badAt_Phi_E h (Psi u cc h g) v).mpr hb
    rw [hPhi] at hb'
    exact hB _ ((E_val_lt h v).mpr hv) hb'

/-- The `j`-th point below `c`, as a point of `Fin (m + 2)`.-/
def U {m c : ℕ} (hc : c < m + 2) (j : Fin c) : Fin (m + 2) := ⟨j.val, lt_trans j.isLt hc⟩

theorem U_lt {m c : ℕ} (hc : c < m + 2) (j : Fin c) : U hc j < ⟨c, hc⟩ :=
  Fin.lt_def.mpr j.isLt

/-- The maps counted by `D (m + 2) c` in which `c` is bad: `c` choices of the leaf `u`, then a
map counted by `D m (c - 1)`.-/
theorem card_V (m c : ℕ) (hc : c < m + 2) :
    (Finset.univ.filter fun g : Fin (m + 2) → Fin (m + 2) =>
      Idem g ∧ (∀ v : Fin (m + 2), v.val < c → ¬BadAt g v) ∧ BadAt g ⟨c, hc⟩).card
      = c * D m (c - 1) := by
  have hprod : c * D m (c - 1) = ((Finset.univ : Finset (Fin c)) ×ˢ
      (Finset.univ.filter fun g : Fin m → Fin m =>
        Idem g ∧ ∀ v : Fin m, v.val < c - 1 → ¬BadAt g v)).card := by
    rw [Finset.card_product, Finset.card_univ, Fintype.card_fin]; rfl
  rw [hprod]
  symm
  refine Finset.card_bij (fun p _ => Phi (U hc p.1) ⟨c, hc⟩ (U_lt hc p.1) p.2) ?_ ?_ ?_
  · intro p hp
    have h2 := (Finset.mem_filter.mp (Finset.mem_product.mp hp).2).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, Phi_mem (U_lt hc p.1) p.2 h2.1 h2.2⟩
  · rintro ⟨j, g1⟩ - ⟨k, g2⟩ - heq
    have heq' : Phi (U hc j) ⟨c, hc⟩ (U_lt hc j) g1 = Phi (U hc k) ⟨c, hc⟩ (U_lt hc k) g2 := heq
    have hjk : j = k := by
      have h1 := congrFun heq' (U hc j)
      rw [Phi_u] at h1
      rcases Phi_eq_cc (U_lt hc k) g2 h1.symm with e | e
      · have e' : (U hc j).val = (U hc k).val := congrArg Fin.val e
        exact Fin.ext e'
      · exact absurd e (ne_of_lt (U_lt hc j))
    subst hjk
    have hg : g1 = g2 := by
      funext i
      have e1 := congrFun heq' (E (U hc j) ⟨c, hc⟩ i)
      rw [Phi_E, Phi_E] at e1
      exact E_inj (U_lt hc j) e1
    rw [hg]
  · intro g hg
    obtain ⟨hI, hB, hbad⟩ := (Finset.mem_filter.mp hg).2
    obtain ⟨u0, hu0, hgu0, -⟩ := hbad.2
    have hval : u0.val < c := Fin.lt_def.mp hu0
    have hU : U hc ⟨u0.val, hval⟩ = u0 := Fin.ext rfl
    have spec := Psi_spec (U_lt hc ⟨u0.val, hval⟩) g hI hB hbad (by rw [hU]; exact hgu0)
    exact ⟨(⟨u0.val, hval⟩, Psi (U hc ⟨u0.val, hval⟩) ⟨c, hc⟩ (U_lt hc _) g),
      Finset.mem_product.mpr ⟨Finset.mem_univ _,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _, spec.1⟩⟩, spec.2⟩

/-- Splitting the maps counted by `D n c` according to whether `c` is bad.-/
theorem D_split (n c : ℕ) (hc : c < n) :
    D n c = D n (c + 1) + (Finset.univ.filter fun g : Fin n → Fin n =>
      Idem g ∧ (∀ v : Fin n, v.val < c → ¬BadAt g v) ∧ BadAt g ⟨c, hc⟩).card := by
  have key := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun g : Fin n → Fin n => Idem g ∧ ∀ v : Fin n, v.val < c → ¬BadAt g v)
    (fun g => BadAt g ⟨c, hc⟩)
  rw [Finset.filter_filter, Finset.filter_filter] at key
  have e1 : (Finset.univ.filter fun g : Fin n → Fin n =>
      Idem g ∧ ∀ v : Fin n, v.val < c + 1 → ¬BadAt g v)
      = (Finset.univ.filter fun g : Fin n → Fin n =>
        (Idem g ∧ ∀ v : Fin n, v.val < c → ¬BadAt g v) ∧ ¬BadAt g ⟨c, hc⟩) := by
    apply Finset.filter_congr
    intro g _
    constructor
    · rintro ⟨hI, hB⟩
      exact ⟨⟨hI, fun v hv => hB v (Nat.lt_succ_of_lt hv)⟩, hB ⟨c, hc⟩ (Nat.lt_succ_self c)⟩
    · rintro ⟨⟨hI, hB⟩, hc'⟩
      refine ⟨hI, fun v hv => ?_⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hv with h1 | h1
      · exact hB v h1
      · have hv' : v = ⟨c, hc⟩ := Fin.ext h1
        rw [hv']; exact hc'
  have e2 : (Finset.univ.filter fun g : Fin n → Fin n =>
      Idem g ∧ (∀ v : Fin n, v.val < c → ¬BadAt g v) ∧ BadAt g ⟨c, hc⟩)
      = (Finset.univ.filter fun g : Fin n → Fin n =>
        (Idem g ∧ ∀ v : Fin n, v.val < c → ¬BadAt g v) ∧ BadAt g ⟨c, hc⟩) := by
    apply Finset.filter_congr
    intro g _
    exact and_assoc.symm
  unfold D
  rw [e1, e2, add_comm]
  exact key.symm

end A347722.StepD

namespace A347722

open StepD in
/-- The recurrence for `D`: a map counted by `D n c` either has `c` not bad (`D n (c + 1)`), or
has `c` as a fixed point with a single leaf `u < c`; removing `u` and `c` leaves a map counted
by `D (n - 2) (c - 1)`, and there are `c` choices for `u`.-/
theorem D_succ (n c : ℕ) (hc : c < n) : D n (c + 1) + c * D (n - 2) (c - 1) = D n c := by
  rw [D_split n c hc]
  congr 1
  rcases Nat.eq_zero_or_pos c with rfl | hpos
  · rw [zero_mul]
    symm
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    rintro g - ⟨-, -, -, u, hu, -⟩
    exact absurd (Fin.lt_def.mp hu) (Nat.not_lt_zero _)
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [Nat.add_sub_cancel]
    exact (card_V m c hc).symm

end A347722

