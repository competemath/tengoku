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

/--
@isnad1 id=eq.1h2v.s4.bf0a0772cfb6 from=translated src=- shape=847639ae vocab=f6e89b7a
-/
theorem dd_val (d : ℕ) (hd : d ≤ n) : (dd d hd).val = d := rfl

/--
@isnad1 id=eq.0h3v.s5.b8618ee5cec1 from=translated src=- shape=a64a0060 vocab=10f7a5ef
-/
theorem emb_val (d : ℕ) (i : Fin n) :
    (emb d i).val = if i.val < d then i.val else i.val + 1 := rfl

/--
@isnad1 id=ne.0h3v.s4.c7f75be0567c from=translated src=- shape=4270e95a vocab=f3c6b27d
-/
theorem emb_val_ne (d : ℕ) (i : Fin n) : (emb d i).val ≠ d := by
  rw [emb_val]; split <;> omega

/--
@isnad1 id=ne.1h3v.s5.935de815d63c from=translated src=- shape=08984727 vocab=877527ab
-/
theorem emb_ne_dd (d : ℕ) (hd : d ≤ n) (i : Fin n) : emb d i ≠ dd d hd :=
  fun h => emb_val_ne d i (congrArg Fin.val h)

/--
@isnad1 id=ne.1h3v.s5.0d51c8747b3b from=translated src=- shape=00877bbd vocab=877527ab
-/
theorem dd_ne_emb (d : ℕ) (hd : d ≤ n) (i : Fin n) : dd d hd ≠ emb d i :=
  fun h => emb_ne_dd d hd i h.symm

/--
@isnad1 id=iff.0h4v.s5.1c1f82665bd7 from=translated src=- shape=0766af9a vocab=4cef2e0f
-/
theorem emb_inj {d : ℕ} {i j : Fin n} : emb d i = emb d j ↔ i = j := by
  constructor
  · intro h
    have := congrArg Fin.val h
    rw [emb_val, emb_val] at this
    apply Fin.ext
    split at this <;> split at this <;> omega
  · rintro rfl; rfl

/--
@isnad1 id=iff.0h4v.s5.b79c8db3ca3c from=translated src=- shape=0766af9a vocab=2443594b
-/
theorem emb_lt {d : ℕ} {i j : Fin n} : emb d i < emb d j ↔ i < j := by
  rw [Fin.lt_def, Fin.lt_def, emb_val, emb_val]; split <;> split <;> omega

/--
@isnad1 id=iff.0h3v.s5.66e0edc163c4 from=translated src=- shape=965cf025 vocab=c9826da3
-/
theorem emb_val_lt {d : ℕ} {i : Fin n} : (emb d i).val < d ↔ i.val < d := by
  rw [emb_val]; split <;> omega

/--
@isnad1 id=eq.2h3v.s6.085f699024f4 from=translated src=- shape=6583de06 vocab=e599f586
-/
theorem emb_ret (d : ℕ) (hd : d ≤ n) (w : Fin (n + 1)) (h : w.val ≠ d) :
    emb d (ret d hd w h) = w := by
  apply Fin.ext
  have := w.isLt
  by_cases h1 : w.val < d
  · simp [emb, ret, h1]
  · have h2 : ¬ (w.val - 1 < d) := by omega
    simp only [emb, ret, ite_eq_right h1, ite_eq_right h2]
    omega

/--
@isnad1 id=iff.1h3v.s5.bce96a660ffc from=translated src=- shape=d2d1a89d vocab=877527ab
-/
theorem forall_split (d : ℕ) (hd : d ≤ n) {P : Fin (n + 1) → Prop} :
    (∀ w, P w) ↔ P (dd d hd) ∧ ∀ i, P (emb d i) := by
  constructor
  · intro h; exact ⟨h _, fun i => h _⟩
  · rintro ⟨h1, h2⟩ w
    by_cases h : w.val = d
    · have hw : w = dd d hd := Fin.ext h
      rw [hw]; exact h1
    · rw [← emb_ret d hd w h]; exact h2 _

/--
@isnad1 id=iff.1h3v.s6.55d44d891d78 from=translated src=- shape=fe603a16 vocab=877527ab
-/
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

/--
@isnad1 id=eq.1h4v.s5.ab8791ddb1ff from=translated src=- shape=b7b2edc8 vocab=10b4bc66
-/
theorem Phi_emb (i : Fin n) : Phi d hd g' (emb d i) = emb d (g' i) := by
  unfold Phi
  rw [dite_eq_right (emb_val_ne d i), emb_inj.1 (emb_ret d hd (emb d i) (emb_val_ne d i))]

/--
@isnad1 id=eq.1h3v.s5.dcd79da06ddf from=translated src=- shape=6cc47115 vocab=dce386a3
-/
theorem Phi_dd : Phi d hd g' (dd d hd) = dd d hd := by
  unfold Phi
  rw [dite_eq_left (dd_val d hd)]

/--
@isnad1 id=iff.1h3v.s5.53909e77d445 from=translated src=- shape=b5cf3e7e vocab=225536fb
-/
theorem idem_Phi : Idem (Phi d hd g') ↔ Idem g' := by
  unfold Idem
  rw [forall_split d hd]
  simp [Phi_dd, Phi_emb, emb_inj]

/--
@isnad1 id=iff.1h4v.s5.cac689e87c2e from=translated src=- shape=0913165f vocab=9e296315
-/
theorem isoAt_Phi_emb {i : Fin n} : IsoAt (Phi d hd g') (emb d i) ↔ IsoAt g' i := by
  unfold IsoAt
  rw [forall_split d hd]
  simp [Phi_dd, Phi_emb, emb_inj, dd_ne_emb]

/--
@isnad1 id=isoat.1h3v.s5.3145329cac24 from=translated src=- shape=cc78241b vocab=728e1b9a
-/
theorem isoAt_Phi_dd : IsoAt (Phi d hd g') (dd d hd) := by
  unfold IsoAt
  rw [forall_split d hd]
  simp [Phi_dd, Phi_emb, emb_ne_dd]

/--
@isnad1 id=iff.1h4v.s5.bc38e5ed4e8f from=translated src=- shape=0913165f vocab=2118a84a
-/
theorem badAt_Phi_emb {i : Fin n} : BadAt (Phi d hd g') (emb d i) ↔ BadAt g' i := by
  unfold BadAt
  rw [Phi_emb, emb_inj, exists_split d hd]
  have key : ∀ j, (∀ w, Phi d hd g' w = emb d i → w = emb d j ∨ w = emb d i) ↔
      (∀ w, g' w = i → w = j ∨ w = i) := by
    intro j
    rw [forall_split d hd]
    simp [Phi_dd, Phi_emb, emb_inj, dd_ne_emb]
  simp [Phi_dd, Phi_emb, emb_inj, emb_lt, dd_ne_emb, key]

/--
@isnad1 id=not.1h3v.s5.156114b39416 from=translated src=- shape=c734f595 vocab=a42f0af1
-/
theorem not_badAt_Phi_dd : ¬ BadAt (Phi d hd g') (dd d hd) := by
  have h : ∀ u, u < dd d hd → Phi d hd g' u ≠ dd d hd := by
    rw [forall_split d hd]
    refine ⟨fun h => absurd h (lt_irrefl _), fun j _ h => ?_⟩
    rw [Phi_emb] at h
    exact emb_ne_dd _ _ _ h
  rintro ⟨_, u, hu, hgu, _⟩
  exact h u hu hgu

/--
@isnad1 id=iff.1h3v.s5.a09fe4c4ffa6 from=translated src=- shape=b5cf3e7e vocab=f0f42c66
-/
theorem good_Phi : Good (Phi d hd g') ↔ Good g' := by
  unfold Good
  rw [idem_Phi, forall_split d hd]
  simp [badAt_Phi_emb, not_badAt_Phi_dd]

/--
@isnad1 id=iff.1h3v.s6.b63d06ce176e from=translated src=- shape=b2bec0f9 vocab=350c0b61
-/
theorem noiso_Phi :
    (∀ v : Fin (n + 1), v.val < d → ¬ IsoAt (Phi d hd g') v) ↔
      ∀ v : Fin n, v.val < d → ¬ IsoAt g' v := by
  rw [forall_split d hd]
  simp [isoAt_Phi_emb, emb_val_lt, dd_val]

/--
@isnad1 id=eq.2h4v.s6.ec1e47c73cad from=translated src=- shape=9259a9d2 vocab=384197e2
-/
theorem Phi_inj {g₁ g₂ : Fin n → Fin n} (h : Phi d hd g₁ = Phi d hd g₂) : g₁ = g₂ := by
  funext i
  have := congrFun h (emb d i)
  rwa [Phi_emb, Phi_emb, emb_inj] at this

/--
@isnad1 id=ex.2h3v.s6.0e84f0f44b43 from=translated src=- shape=1ec72710 vocab=728e1b9a
-/
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

/-- With no isolation constraint, `F` counts the good maps, as does `D n n`.
@isnad1 id=eq.0h1v.s3.67bd247f1310 from=translated src=- shape=5efd7bb9 vocab=6002aadd
-/
theorem F_zero (n : ℕ) : F n 0 = D n n := by
  unfold F D
  congr 1
  apply Finset.filter_congr
  intro g _
  simp [Good]

/-- Splitting on whether the point `d` is isolated, and deleting it when it is.
@isnad1 id=eq.1h2v.s6.437840f0ae2c from=translated src=- shape=1af7c526 vocab=8528a6d7
-/
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

