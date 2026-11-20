/-
OEIS A347722, step F: the recurrence `F (n+1) (d+1) + F n d = F (n+1) d` and `F n 0 = D n n`.

`F n d` counts the good maps on `n` points in which none of the first `d` points is isolated.
Splitting the maps counted by `F (n+1) d` on whether the point `dd = d` is isolated gives
`F (n+1) (d+1)` plus the number of maps in which `dd` is isolated. The latter are in bijection
with the maps counted by `F n d`, by deleting the point `dd`:

* `emb d : Fin n → Fin (n+1)` is the increasing map whose range is the complement of `{dd}`;
* `Phi g' (emb i) = emb (g' i)` and `Phi g' dd = dd`.

`Phi` preserves and reflects `Idem`, `BadAt` and `IsoAt` at the points `emb i`; `dd` is isolated
for `Phi g'` and is never bad. `Phi` is injective, and its range is the set of maps for which
`dd` is isolated.
-/
import Tengoku.OeisLean.OeisLean.A347722.Defs

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms A347722.F_zero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms A347722.F_succ` (it only prints; the queue checks the axioms of every declaration). -/

namespace A347722.StepF

variable {n : ℕ}

/-- The increasing embedding `Fin n → Fin (n+1)` that skips the value `d`.-/
def emb (d : ℕ) (i : Fin n) : Fin (n + 1) :=
  ⟨if i.val < d then i.val else i.val + 1, by have := i.isLt; split <;> omega⟩

/-- The inverse of `emb d` on the points different from `d`.-/
def ret (d : ℕ) (hd : d ≤ n) (w : Fin (n + 1)) (h : w.val ≠ d) : Fin n :=
  ⟨if w.val < d then w.val else w.val - 1, by have := w.isLt; split <;> omega⟩

/-- The deleted point.-/
def dd (d : ℕ) (hd : d ≤ n) : Fin (n + 1) := ⟨d, by omega⟩

theorem dd_val (d : ℕ) (hd : d ≤ n) : (dd d hd).val = d := rfl

theorem emb_val (d : ℕ) (i : Fin n) :
    (emb d i).val = if i.val < d then i.val else i.val + 1 := rfl

theorem emb_val_ne (d : ℕ) (i : Fin n) : (emb d i).val ≠ d := by
  rw [emb_val]; split <;> omega

theorem emb_ne_dd (d : ℕ) (hd : d ≤ n) (i : Fin n) : emb d i ≠ dd d hd :=
  fun h => emb_val_ne d i (congrArg Fin.val h)

theorem dd_ne_emb (d : ℕ) (hd : d ≤ n) (i : Fin n) : dd d hd ≠ emb d i :=
  fun h => emb_ne_dd d hd i h.symm

theorem emb_inj {d : ℕ} {i j : Fin n} : emb d i = emb d j ↔ i = j := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [emb_val, emb_val] at this
    apply Fin.ext
    split at this <;> split at this <;> omega
  · rintro rfl; rfl

theorem emb_lt {d : ℕ} {i j : Fin n} : emb d i < emb d j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def, emb_val, emb_val]; split <;> split <;> omega

theorem emb_val_lt {d : ℕ} {i : Fin n} : (emb d i).val < d ↔ i.val < d := by
  rw [emb_val]; split <;> omega

theorem emb_ret (d : ℕ) (hd : d ≤ n) (w : Fin (n + 1)) (h : w.val ≠ d) :
    emb d (ret d hd w h) = w := by
  apply Fin.ext
  have := w.isLt
  by_cases h1 : w.val < d
  · simp [emb, ret, h1]
  · have h2 : ¬ (w.val - 1 < d) := by omega
    simp only [emb, ret, ite_eq_right h1, ite_eq_right h2]
    omega

theorem forall_split (d : ℕ) (hd : d ≤ n) {P : Fin (n + 1) → Prop} :
    (∀ w, P w) ↔ P (dd d hd) ∧ ∀ i, P (emb d i) := by
  constructor
  · intro h; exact ⟨h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ w
    by_cases h : w.val = d
    · have hw : w = dd d hd := Fin.ext h
      rw [hw]; exact h1
    · rw [← emb_ret d hd w h]; exact h2 _

theorem exists_split (d : ℕ) (hd : d ≤ n) {P : Fin (n + 1) → Prop} :
    (∃ w, P w) ↔ P (dd d hd) ∨ ∃ i, P (emb d i) := by
  constructor
  · rintro ⟨w, hw⟩
    by_cases h : w.val = d
    · have hw' : w = dd d hd := Fin.ext h
      left; rw [← hw']; exact hw
    · right; exact ⟨ret d hd w h, by rw [emb_ret]; exact hw⟩
  · rintro (h | ⟨i, h⟩)
    · exact ⟨_, h⟩
    · exact ⟨_, h⟩

/-- Extend a map on `n` points to `n+1` points by inserting the isolated fixed point `dd`.-/
def Phi (d : ℕ) (hd : d ≤ n) (g' : Fin n → Fin n) (w : Fin (n + 1)) : Fin (n + 1) :=
  if h : w.val = d then w else emb d (g' (ret d hd w h))

variable {d : ℕ} {hd : d ≤ n} {g' : Fin n → Fin n}

theorem Phi_emb (i : Fin n) : Phi d hd g' (emb d i) = emb d (g' i) := by
  unfold Phi
  rw [dite_eq_right (emb_val_ne d i), emb_inj.1 (emb_ret d hd (emb d i) (emb_val_ne d i))]

theorem Phi_dd : Phi d hd g' (dd d hd) = dd d hd := by
  unfold Phi
  rw [dite_eq_left (dd_val d hd)]

theorem idem_Phi : Idem (Phi d hd g') ↔ Idem g' := by
  unfold Idem
  rw [forall_split d hd]
  simp [Phi_dd, Phi_emb, emb_inj]

theorem isoAt_Phi_emb {i : Fin n} : IsoAt (Phi d hd g') (emb d i) ↔ IsoAt g' i := by
  unfold IsoAt
  rw [forall_split d hd]
  simp [Phi_dd, Phi_emb, emb_inj, dd_ne_emb]

theorem isoAt_Phi_dd : IsoAt (Phi d hd g') (dd d hd) := by
  unfold IsoAt
  rw [forall_split d hd]
  simp [Phi_dd, Phi_emb, emb_ne_dd]

theorem badAt_Phi_emb {i : Fin n} : BadAt (Phi d hd g') (emb d i) ↔ BadAt g' i := by
  unfold BadAt
  rw [Phi_emb, emb_inj, exists_split d hd]
  have key : ∀ j, (∀ w, Phi d hd g' w = emb d i → w = emb d j ∨ w = emb d i) ↔
      (∀ w, g' w = i → w = j ∨ w = i) := by
    intro j
    rw [forall_split d hd]
    simp [Phi_dd, Phi_emb, emb_inj, dd_ne_emb]
  simp [Phi_dd, Phi_emb, emb_inj, emb_lt, dd_ne_emb, key]

theorem not_badAt_Phi_dd : ¬ BadAt (Phi d hd g') (dd d hd) := by
  have h : ∀ u, u < dd d hd → Phi d hd g' u ≠ dd d hd := by
    rw [forall_split d hd]
    refine ⟨fun h => absurd h (lt_irrefl _), fun j _ h => ?_⟩
    rw [Phi_emb] at h
    exact emb_ne_dd _ _ _ h
  rintro ⟨_, u, hu, hgu, _⟩
  exact h u hu hgu

theorem good_Phi : Good (Phi d hd g') ↔ Good g' := by
  unfold Good
  rw [idem_Phi, forall_split d hd]
  simp [badAt_Phi_emb, not_badAt_Phi_dd]

theorem noiso_Phi :
    (∀ v : Fin (n + 1), v.val < d → ¬ IsoAt (Phi d hd g') v) ↔
      ∀ v : Fin n, v.val < d → ¬ IsoAt g' v := by
  rw [forall_split d hd]
  simp [isoAt_Phi_emb, emb_val_lt, dd_val]

theorem Phi_inj {g₁ g₂ : Fin n → Fin n} (h : Phi d hd g₁ = Phi d hd g₂) : g₁ = g₂ := by
  funext i
  have := congrFun h (emb d i)
  rwa [Phi_emb, Phi_emb, emb_inj] at this

theorem Phi_surj (d : ℕ) (hd : d ≤ n) (g : Fin (n + 1) → Fin (n + 1))
    (hg : IsoAt g (dd d hd)) : ∃ g', Phi d hd g' = g := by
  have hne : ∀ i, (g (emb d i)).val ≠ d :=
    fun i h => emb_ne_dd d hd i ((hg _).1 (Fin.ext h))
  refine ⟨fun i => ret d hd (g (emb d i)) (hne i), ?_⟩
  funext w
  revert w
  rw [forall_split d hd]
  refine ⟨?_, fun i => ?_⟩
  · rw [Phi_dd]; exact ((hg _).2 rfl).symm
  · rw [Phi_emb, emb_ret]

end A347722.StepF

namespace A347722

open StepF

/-- With no isolation constraint, `F` counts the good maps, as does `D n n`.-/
theorem F_zero (n : ℕ) : F n 0 = D n n := by
  unfold F D
  congr 1
  apply Finset.filter_congr
  intro g _
  simp [Good]

/-- Splitting on whether the point `d` is isolated, and deleting it when it is.-/
theorem F_succ (n d : ℕ) (hd : d ≤ n) : F (n + 1) (d + 1) + F n d = F (n + 1) d := by
  have hV : F n d = (Finset.univ.filter fun g : Fin (n + 1) → Fin (n + 1) =>
      (Good g ∧ ∀ v : Fin (n + 1), v.val < d → ¬ IsoAt g v) ∧ IsoAt g (dd d hd)).card := by
    unfold F
    apply Finset.card_bij (fun g' _ => Phi d hd g')
    · intro g' hg'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg' ⊢
      exact ⟨⟨good_Phi.2 hg'.1, noiso_Phi.2 hg'.2⟩, isoAt_Phi_dd⟩
    · intro a _ b _ h
      exact Phi_inj h
    · intro g hg
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hg
      obtain ⟨g', rfl⟩ := Phi_surj d hd g hg.2
      refine ⟨g', ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨good_Phi.1 hg.1.1, noiso_Phi.1 hg.1.2⟩
  have hS : F (n + 1) (d + 1) = (Finset.univ.filter fun g : Fin (n + 1) → Fin (n + 1) =>
      (Good g ∧ ∀ v : Fin (n + 1), v.val < d → ¬ IsoAt g v) ∧ ¬ IsoAt g (dd d hd)).card := by
    unfold F
    congr 1
    apply Finset.filter_congr
    intro g _
    have key : (∀ v : Fin (n + 1), v.val < d + 1 → ¬ IsoAt g v) ↔
        (∀ v : Fin (n + 1), v.val < d → ¬ IsoAt g v) ∧ ¬ IsoAt g (dd d hd) := by
      constructor
      · intro h
        exact ⟨fun v hv => h v (by omega), h _ (by rw [dd_val]; omega)⟩
      · rintro ⟨h1, h2⟩ v hv
        by_cases h : v.val = d
        · have hv' : v = dd d hd := Fin.ext h
          rw [hv']; exact h2
        · exact h1 v (by omega)
    rw [key, and_assoc]
  have hsplit := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter fun g : Fin (n + 1) → Fin (n + 1) =>
      Good g ∧ ∀ v : Fin (n + 1), v.val < d → ¬ IsoAt g v)
    (fun g => IsoAt g (dd d hd))
  rw [Finset.filter_filter, Finset.filter_filter] at hsplit
  rw [hV, hS, add_comm]
  exact hsplit

end A347722

