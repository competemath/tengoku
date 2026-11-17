import Tengoku.StringDiagramsLean.StringDiagrams.Chord.NormalForm

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Letters of chord diagrams and realisation of pairings

* `canon_eq_of_iso`: the canonical diagram `canon s` depends only on the letters and the pairing
  of `s` (not on the arc ids).
* `Equiv.fits_letters`: equivalent diagrams fit on the same states and produce the same letters
  (`lstep` is the effect of a move on the list of letters).
* `run_canon`: `canon s` fits on the empty state and realises the letters and the pairing of `s`,
  when the letters at the two ends of each arc are `a` (left end) and `d a` (right end)
  (`Lettered`).
-/

namespace StringDiagrams.Chord

/-! ## Relabelling ids, letters, and the canonical diagram realises its pairing -/

section Iso

variable {α : Type*}

/-- Two states with the same letters and the same pairing (they differ by a relabelling of the
arc ids).-/
def Iso (s s' : List (ℕ × α)) : Prop :=
  s.map Prod.snd = s'.map Prod.snd ∧ ∀ i j, Same s i j ↔ Same s' i j

/--
@isnad1 id=eq.1h3v.s4.53f64c07c815 from=translated src=- shape=7c21a244 vocab=61b2e7e9
-/
theorem Iso.length_eq {s s' : List (ℕ × α)} (h : Iso s s') : s.length = s'.length := by
  simpa using congrArg List.length h.1

/--
@isnad1 id=iso.1h3v.s4.2a73998a5256 from=translated src=- shape=64dff98b vocab=d5599d94
-/
theorem Iso.symm {s s' : List (ℕ × α)} (h : Iso s s') : Iso s' s :=
  ⟨h.1.symm, fun i j => (h.2 i j).symm⟩

/--
@isnad1 id=valid.2h3v.s4.06a0fce764ba from=translated src=- shape=3534f547 vocab=8429b854
-/
theorem Iso.valid {s s' : List (ℕ × α)} (h : Iso s s') (hv : Valid s) : Valid s' := by
  intro i hi
  obtain ⟨j, hj, hu⟩ := hv i (by rw [h.length_eq]; exact hi)
  exact ⟨j, (h.2 i j).1 hj, fun k hk => hu k ((h.2 i k).2 hk)⟩

/--
@isnad1 id=eq.3h4v.s6.52e65e38e3c0 from=translated src=- shape=6087b218 vocab=0d3174e8
-/
theorem Iso.snd_getElem {s s' : List (ℕ × α)} (h : Iso s s') {i : ℕ} (hi : i < s.length)
    (hi' : i < s'.length) : (s[i]).2 = (s'[i]).2 := by
  have := congrArg (fun l => l[i]?) h.1
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi'] at this
  simpa using this

/--
@isnad1 id=iso.1h4v.s5.297280b704dd from=translated src=- shape=9051a317 vocab=89255491
-/
theorem Iso.swapAt {s s' : List (ℕ × α)} (h : Iso s s') (p : ℕ) :
    Iso (Chord.swapAt s p) (Chord.swapAt s' p) := by
  by_cases hp : p + 1 < s.length
  · have hp' : p + 1 < s'.length := h.length_eq ▸ hp
    refine ⟨?_, fun i j => by rw [same_swapAt hp, same_swapAt hp', h.2]⟩
    apply List.ext_getElem?; intro i
    have := congrArg (fun l => l[tau p i]?) h.1
    simp only [List.getElem?_map] at this ⊢
    rw [getElem?_swapAt s hp, getElem?_swapAt s' hp']; exact this
  · rw [swapAt_of_le s hp, swapAt_of_le s' (h.length_eq ▸ hp)]; exact h

/--
@isnad1 id=iso.2h4v.s5.a522c94488a7 from=translated src=- shape=24c0f1e9 vocab=98866eae
-/
theorem Iso.rmAt {s s' : List (ℕ × α)} (h : Iso s s') {r : ℕ} (hr : r + 2 ≤ s.length) :
    Iso (Chord.rmAt s r) (Chord.rmAt s' r) := by
  have hr' : r + 2 ≤ s'.length := h.length_eq ▸ hr
  refine ⟨?_, fun i j => by rw [same_rmAt hr, same_rmAt hr', h.2]⟩
  apply List.ext_getElem?; intro i
  have := congrArg (fun l => l[rmIdx r i]?) h.1
  simp only [List.getElem?_map] at this ⊢
  rw [getElem?_rmAt s hr, getElem?_rmAt s' hr']; exact this

/--
@isnad1 id=iff.1h4v.s4.20366490625f from=translated src=- shape=b4444cda vocab=7e1e61f6
-/
theorem opn_iff {s s' : List (ℕ × α)} (h : Iso s s') (q : ℕ) : Opn s q ↔ Opn s' q := by
  simp only [Opn, h.2]

/--
@isnad1 id=iff.1h4v.s4.2fb373532c82 from=translated src=- shape=b4444cda vocab=e9237954
-/
theorem cls_iff {s s' : List (ℕ × α)} (h : Iso s s') (q : ℕ) : Cls s q ↔ Cls s' q := by
  simp only [Cls, h.2]

/--
@isnad1 id=le.1h3v.s4.99777dfc66d1 from=translated src=- shape=148ed7ae vocab=a2c6a4fe
-/
theorem cr_le_of_iso {s s' : List (ℕ × α)} (h : Iso s s') : cr s ≤ cr s' := by
  unfold cr
  refine Finset.card_le_card fun x hx => ?_
  rw [mem_crSet] at hx ⊢
  obtain ⟨h1, h2, h3, h4, h5⟩ := hx
  exact ⟨h1, h2, h3, (h.2 _ _).1 h4, (h.2 _ _).1 h5⟩

/-- The canonical diagram depends only on the letters and the pairing.
@isnad1 id=eq.2h4v.s5.7e751ccbc318 from=translated src=- shape=526b8719 vocab=141eb23d
-/
theorem canon_congr : ∀ (n : ℕ) {s s' : List (ℕ × α)}, s.length + cr s < n → Iso s s' →
    canon s = canon s' := by
  intro n
  induction n with
  | zero => intro s s' h; omega
  | succ n ih =>
    intro s s' hn h
    by_cases hv : Valid s
    swap
    · have hv' : ¬ Valid s' := fun hv' => hv (h.symm.valid hv')
      rw [canon, dite_eq_right hv, canon, dite_eq_right hv']
    have hv' := h.valid hv
    by_cases hadj : ∃ r, Same s r (r + 1)
    · classical
      obtain ⟨r, hr, hmin⟩ : ∃ r, Same s r (r + 1) ∧ ∀ r' < r, ¬ Same s r' (r' + 1) :=
        ⟨Nat.find hadj, Nat.find_spec hadj, fun _ => Nat.find_min hadj⟩
      have hr' : Same s' r (r + 1) := (h.2 _ _).1 hr
      have hmin' : ∀ r' < r, ¬ Same s' r' (r' + 1) := fun r' hr'' hs => hmin r' hr'' ((h.2 _ _).2 hs)
      rw [canon_adj hv hr hmin, canon_adj hv' hr' hmin', h.snd_getElem hr.lt_left hr'.lt_left]
      have hl : r + 2 ≤ s.length := hr.lt_right
      rw [ih (by rw [length_rmAt s hl]; have := cr_rmAt_le hl; omega) (h.rmAt hl)]
    · have hno : ∀ r, ¬ Same s r (r + 1) := fun r hr => hadj ⟨r, hr⟩
      have hno' : ∀ r, ¬ Same s' r (r + 1) := fun r hr => hno r ((h.2 _ _).2 hr)
      by_cases hne : s = []
      · have hne' : s' = [] := List.eq_nil_of_length_eq_zero (by rw [← h.length_eq, hne]; rfl)
        rw [hne, hne']
      have hne' : s' ≠ [] := fun e => hne (List.eq_nil_of_length_eq_zero
        (by rw [h.length_eq, e]; rfl))
      obtain ⟨q, ho, hc, hq, hmin⟩ := canon_cross hv hno hne
      obtain ⟨q', ho', hc', hq', hmin'⟩ := canon_cross hv' hno' hne'
      have e : q = q' := by
        rcases lt_trichotomy q q' with l | l | l
        · exact (hmin' q l ⟨(opn_iff h q).1 ho, (cls_iff h _).1 hc⟩).elim
        · exact l
        · exact (hmin q' l ⟨(opn_iff h q').2 ho', (cls_iff h _).2 hc'⟩).elim
      subst e
      have hilv := ilv_of_opn_cls hv (hno q) ho hc
      rw [hq, hq', ih (by rw [length_swapAt]; have := cr_swapAt_lt hv hilv; omega) (h.swapAt q)]

/-- The canonical diagram depends only on the letters and the pairing.
@isnad1 id=eq.1h3v.s4.ff0ef31570e8 from=translated src=- shape=43aa0626 vocab=147f046d
-/
theorem canon_eq_of_iso {s s' : List (ℕ × α)} (h : Iso s s') : canon s = canon s' :=
  canon_congr _ (Nat.lt_succ_self _) h

end Iso

section Letters

variable {α : Type*} {d : α → α}

/-- The effect of a move on the list of letters.-/
def lstep (d : α → α) (l : List α) : Move α → List α
  | .cup g a => insAt l g a (d a)
  | .cross p => swapAt l p

/--
@isnad1 id=eq.0h7v.s5.d85d1c13a0d2 from=translated src=- shape=f0d88cf1 vocab=3d462c92
-/
theorem map_insAt {β γ : Type*} (f : β → γ) (s : List β) (g : ℕ) (x y : β) :
    (insAt s g x y).map f = insAt (s.map f) g (f x) (f y) := by
  simp [insAt, List.map_take, List.map_drop]

/--
@isnad1 id=eq.0h5v.s5.22c7f4f6b0e8 from=translated src=- shape=62ad656d vocab=d56f67f1
-/
theorem map_swapAt {β γ : Type*} (f : β → γ) (s : List β) (p : ℕ) :
    (swapAt s p).map f = swapAt (s.map f) p := by
  by_cases hp : p + 1 < s.length
  · apply List.ext_getElem?; intro i
    rw [List.getElem?_map, getElem?_swapAt s hp, getElem?_swapAt _ (by simpa using hp),
      List.getElem?_map]
  · rw [swapAt_of_le s hp, swapAt_of_le _ (by simpa using hp)]

/--
@isnad1 id=eq.0h5v.s5.edd2e79b8438 from=translated src=- shape=62ad656d vocab=5bc96e9c
-/
theorem map_rmAt {β γ : Type*} (f : β → γ) (s : List β) (r : ℕ) :
    (rmAt s r).map f = rmAt (s.map f) r := by
  simp [rmAt, List.map_take, List.map_drop]

/--
@isnad1 id=eq.0h4v.s5.db554c4e73d9 from=translated src=- shape=0de14490 vocab=f47bed9b
-/
theorem snd_step (s : List (ℕ × α)) (m : Move α) :
    (step d s m).map Prod.snd = lstep d (s.map Prod.snd) m := by
  cases m with
  | cup g a => simp only [step, lstep, map_insAt]
  | cross p => simp only [step, lstep, map_swapAt]

/--
@isnad1 id=eq.0h4v.s5.c1e68b08ab70 from=translated src=- shape=d81bbdf2 vocab=8827f757
-/
theorem snd_foldl_step : ∀ (s : List (ℕ × α)) (D : List (Move α)),
    (D.foldl (step d) s).map Prod.snd = D.foldl (lstep d) (s.map Prod.snd)
  | s, [] => rfl
  | s, m :: D => by simp only [List.foldl_cons, snd_foldl_step _ D, snd_step]

/-- The letters of the final state of a diagram.
@isnad1 id=eq.0h3v.s5.ae3ba0c966fd from=translated src=- shape=d5ff5ae5 vocab=d035b79f
-/
theorem snd_run (D : List (Move α)) : (run d D).map Prod.snd = D.foldl (lstep d) [] := by
  rw [run, snd_foldl_step]; rfl

/--
@isnad1 id=eq.0h4v.s4.5dc95a662ec9 from=translated src=- shape=c3e68f6e vocab=8c06c0cf
-/
theorem length_lstep (l : List α) (m : Move α) : (lstep d l m).length = m.len l.length := by
  cases m with
  | cup g a => simp [lstep, Move.len, insAt]; omega
  | cross p => simp [lstep, Move.len]

/--
@isnad1 id=eq.2h8v.s6.6356ddd6440e from=translated src=- shape=52ed7341 vocab=0f993640
-/
theorem insAt_insAt {β : Type*} (l : List β) {g g' : ℕ} (h : g' ≤ g) (hg : g ≤ l.length)
    (x y u v : β) : insAt (insAt l g x y) g' u v = insAt (insAt l g' u v) (g + 2) x y := by
  apply List.ext_getElem?; intro i
  have h1 : g' ≤ (insAt l g x y).length := by rw [length_insAt l hg]; omega
  have h2 : g + 2 ≤ (insAt l g' u v).length := by rw [length_insAt l (by omega)]; omega
  simp only [getElem?_insAt _ h1, getElem?_insAt _ h2, getElem?_insAt l hg,
    getElem?_insAt l (show g' ≤ l.length by omega)]
  rcases (show i < g' ∨ i = g' ∨ i = g' + 1 ∨ (g' + 1 < i ∧ i < g + 2) ∨ i = g + 2 ∨ i = g + 3 ∨
    g + 3 < i by omega) with hi | hi | hi | hi | hi | hi | hi <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right]

/--
@isnad1 id=eq.2h6v.s5.aa25f129fce6 from=translated src=- shape=1e1766d1 vocab=91910def
-/
theorem insAt_swapAt_lt {β : Type*} (l : List β) {p g : ℕ} (h : p + 2 ≤ g) (hg : g ≤ l.length)
    (x y : β) : insAt (swapAt l p) g x y = swapAt (insAt l g x y) p := by
  have hp : p + 1 < l.length := by omega
  have hg' : g ≤ (swapAt l p).length := by simpa using hg
  have hp' : p + 1 < (insAt l g x y).length := by rw [length_insAt l hg]; omega
  apply List.ext_getElem?; intro i
  simp only [getElem?_insAt _ hg', getElem?_swapAt _ hp', getElem?_insAt l hg,
    getElem?_swapAt l hp]
  rcases (show i < p ∨ i = p ∨ i = p + 1 ∨ (p + 1 < i ∧ i < g) ∨ i = g ∨ i = g + 1 ∨ g + 1 < i
    by omega) with hi | rfl | rfl | hi | rfl | rfl | hi <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, tau_left, tau_right, tau_of_ne, ↓reduceIte]

/--
@isnad1 id=eq.2h6v.s6.ec15b75cd6b1 from=translated src=- shape=70f1f251 vocab=4e1f2ce9
-/
theorem insAt_swapAt_ge {β : Type*} (l : List β) {p g : ℕ} (h : g ≤ p) (hp : p + 1 < l.length)
    (x y : β) : insAt (swapAt l p) g x y = swapAt (insAt l g x y) (p + 2) := by
  have hg : g ≤ l.length := by omega
  have hg' : g ≤ (swapAt l p).length := by simpa using hg
  have hp' : p + 2 + 1 < (insAt l g x y).length := by rw [length_insAt l hg]; omega
  apply List.ext_getElem?; intro i
  simp only [getElem?_insAt _ hg', getElem?_swapAt _ hp', getElem?_insAt l hg,
    getElem?_swapAt l hp]
  rcases (show i < g ∨ i = g ∨ i = g + 1 ∨ (g + 1 < i ∧ i < p + 2) ∨ i = p + 2 ∨ i = p + 2 + 1 ∨
    p + 2 + 1 < i by omega) with hi | rfl | rfl | hi | rfl | rfl | hi <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, tau_left, tau_right, tau_of_ne, ↓reduceIte]
    try (congr 1; unfold tau; split_ifs <;> omega)

/--
@isnad1 id=eq.1h5v.s6.322b2c4a0cca from=translated src=- shape=b77151b2 vocab=016590a9
-/
theorem insAt_pitch {β : Type*} (l : List β) {g : ℕ} (hg : g < l.length) (x y : β) :
    swapAt (insAt l g x y) (g + 1) = swapAt (insAt l (g + 1) x y) g := by
  have h1 : g + 1 + 1 < (insAt l g x y).length := by rw [length_insAt l (by omega)]; omega
  have h2 : g + 1 < (insAt l (g + 1) x y).length := by rw [length_insAt l (by omega)]; omega
  apply List.ext_getElem?; intro i
  simp only [getElem?_swapAt _ h1, getElem?_swapAt _ h2, getElem?_insAt l (show g ≤ l.length by omega),
    getElem?_insAt l (show g + 1 ≤ l.length by omega)]
  rcases (show i < g ∨ i = g ∨ i = g + 1 ∨ i = g + 1 + 1 ∨ g + 1 + 1 < i by omega) with
    hi | rfl | rfl | rfl | hi <;>
  · simp (disch := omega) only [ite_eq_left, ite_eq_right, tau_left, tau_right, tau_of_ne, ↓reduceIte,
      show ∀ n : ℕ, n + 1 + 1 - 2 = n from fun n => by omega]

/-- Each generating move preserves whether a diagram fits and the letters it produces.
@isnad1 id=and.1h5v.s6.d5116b10a25a from=translated src=- shape=25ccf8bf vocab=ce2f5dfc
-/
theorem Step.fits_letters {L R : List (Move α)} (h : Step L R) (l : List α) :
    (Fits l.length L ↔ Fits l.length R) ∧
      (Fits l.length L → L.foldl (lstep d) l = R.foldl (lstep d) l) := by
  cases h with
  | xx h =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    exact swapAt_comm l h (by omega)
  | xuL a h =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    rw [insAt_swapAt_lt l h (by simpa using hf.2.1)]
  | xuR a h =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    rw [insAt_swapAt_ge l h hf.1]
  | uu a b h =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    exact insAt_insAt l h hf.1 _ _ _ _
  | braid p =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    exact swapAt_braid l (by omega)
  | pitch g a =>
    refine ⟨by simp only [Fits, Move.Ok, Move.len, and_true]; constructor <;> intro <;> omega,
      fun hf => ?_⟩
    simp only [Fits, Move.Ok, Move.len] at hf
    simp only [List.foldl_cons, List.foldl_nil, lstep]
    exact insAt_pitch l (by omega) _ _

/--
@isnad1 id=eq.0h4v.s5.c0571fdef6d4 from=translated src=- shape=3d8385ad vocab=97fa1c64
-/
theorem foldl_lstep_len : ∀ (l : List α) (D : List (Move α)),
    (D.foldl (lstep d) l).length = D.foldl Move.len l.length
  | l, [] => rfl
  | l, m :: D => by simp only [List.foldl_cons, foldl_lstep_len _ D, length_lstep]

/-- A move in context preserves whether a diagram fits and the letters it produces.
@isnad1 id=and.1h5v.s6.9c9766c266d5 from=translated src=- shape=25ccf8bf vocab=a83b5db1
-/
theorem Rw.fits_letters {X Y : List (Move α)} (h : Rw X Y) (l : List α) :
    (Fits l.length X ↔ Fits l.length Y) ∧
      (Fits l.length X → X.foldl (lstep d) l = Y.foldl (lstep d) l) := by
  obtain ⟨A, B, L, R, hs, rfl, rfl⟩ := h
  have hA := foldl_lstep_len (d := d) l A
  obtain ⟨h1, h2⟩ := hs.fits_letters (d := d) (A.foldl (lstep d) l)
  rw [hA] at h1 h2
  have hLR : ∀ hf : Fits (A.foldl Move.len l.length) L, L.foldl Move.len (A.foldl Move.len l.length) =
      R.foldl Move.len (A.foldl Move.len l.length) := fun hf => by
    rw [← hA, ← foldl_lstep_len (d := d), ← foldl_lstep_len (d := d), h2 (hA ▸ hf)]
  simp only [fits_append, List.foldl_append]
  constructor
  · constructor
    · rintro ⟨⟨hA', hL⟩, hB⟩
      exact ⟨⟨hA', h1.1 hL⟩, by rwa [← hLR hL]⟩
    · rintro ⟨⟨hA', hR⟩, hB⟩
      exact ⟨⟨hA', h1.2 hR⟩, by rwa [hLR (h1.2 hR)]⟩
  · rintro ⟨⟨-, hL⟩, -⟩
    rw [h2 (hA ▸ hL)]

/-- Equivalent diagrams fit on the same number of strands and produce the same letters.
@isnad1 id=and.1h5v.s6.77b80fd27ce0 from=translated src=- shape=25ccf8bf vocab=527048a1
-/
theorem Equiv.fits_letters {X Y : List (Move α)} (h : Equiv X Y) (l : List α) :
    (Fits l.length X ↔ Fits l.length Y) ∧
      (Fits l.length X → X.foldl (lstep d) l = Y.foldl (lstep d) l) := by
  induction h with
  | rel X Y h => exact h.fits_letters l
  | refl => exact ⟨Iff.rfl, fun _ => rfl⟩
  | symm X Y _ ih => exact ⟨ih.1.symm, fun hf => (ih.2 (ih.1.2 hf)).symm⟩
  | trans X Y Z _ _ ih ih' =>
    exact ⟨ih.1.trans ih'.1, fun hf => (ih.2 hf).trans (ih'.2 (ih.1.1 hf))⟩

end Letters

section RunCanon

variable {α : Type*} {d : α → α}

/-- The letters at the two ends of each arc are `a` (at one end) and `d a` (at the other).-/
def Lettered (d : α → α) (s : List (ℕ × α)) : Prop :=
  ∀ i j, Same s i j → i < j → (s[j]?).map Prod.snd = (s[i]?).map (d ∘ Prod.snd)

/--
@isnad1 id=lettered.3h4v.s6.25e3c7cc103e from=translated src=- shape=1e2c5238 vocab=c93df5b7
-/
theorem Lettered.swapAt {s : List (ℕ × α)} (h : Lettered d s) {p : ℕ}
    (hp : p + 1 < s.length) (hn : ¬ Same s p (p + 1)) : Lettered d (Chord.swapAt s p) := by
  intro i j hij hlt
  rw [same_swapAt hp] at hij
  rw [getElem?_swapAt s hp, getElem?_swapAt s hp]
  have : tau p i < tau p j := by
    rw [tau_lt_iff p]
    · exact hlt
    · rintro ⟨rfl, rfl⟩; exact hn (by simpa [tau] using hij.symm)
    · rintro ⟨rfl, rfl⟩; omega
  exact h _ _ hij this

/--
@isnad1 id=lettered.2h4v.s5.c7d0137e1f94 from=translated src=- shape=df346bc7 vocab=4f2d5d1f
-/
theorem Lettered.rmAt {s : List (ℕ × α)} (h : Lettered d s) {r : ℕ} (hr : r + 2 ≤ s.length) :
    Lettered d (Chord.rmAt s r) := by
  intro i j hij hlt
  rw [same_rmAt hr] at hij
  rw [getElem?_rmAt s hr, getElem?_rmAt s hr]
  exact h _ _ hij ((rmIdx_lt_iff r).2 hlt)

/--
@isnad1 id=iso.4h8v.s6.0f905bd7d231 from=translated src=- shape=5ed8e0a2 vocab=7d81a932
-/
theorem Iso.insAt {u t : List (ℕ × α)} (h : Iso u t) {g : ℕ} (hg : g ≤ u.length) {k k' : ℕ}
    (hk : ∀ x ∈ u, x.1 ≠ k) (hk' : ∀ x ∈ t, x.1 ≠ k') (a b : α) :
    Iso (Chord.insAt u g (k, a) (k, b)) (Chord.insAt t g (k', a) (k', b)) := by
  have hg' : g ≤ t.length := h.length_eq ▸ hg
  refine ⟨by rw [map_insAt, map_insAt, h.1], fun i j => ?_⟩
  rw [same_insAt_iff hg hk, same_insAt_iff hg' hk', h.2]

/--
@isnad1 id=ne.3h4v.s6.ac774d237a07 from=translated src=- shape=e87138f5 vocab=f5990cc1
-/
theorem ne_id_of_mem_rmAt {s : List (ℕ × α)} (hv : Valid s) {r : ℕ} (hr : Same s r (r + 1))
    {x : ℕ × α} (hx : x ∈ Chord.rmAt s r) : x.1 ≠ (s[r]'hr.lt_left).1 := by
  have hl : r + 2 ≤ s.length := hr.lt_right
  rw [List.mem_iff_getElem?] at hx
  obtain ⟨i, hi⟩ := hx
  rw [getElem?_rmAt s hl] at hi
  intro e
  have hs : Same s (rmIdx r i) r := by
    refine ⟨by unfold rmIdx; split_ifs <;> omega, by simp [idAt, hi], ?_⟩
    simp [idAt, hi, List.getElem?_eq_getElem hr.lt_left, e]
  have := hv.unique hs.symm hr
  unfold rmIdx at this; split_ifs at this <;> omega

/-- **The canonical diagram realises its pairing**: it fits, and its final state has the letters
and the pairing of `s`.
@isnad1 id=and.3h4v.s5.ed7f82dd7838 from=translated src=- shape=9e79851c vocab=86b077d3
-/
theorem run_canon : ∀ (n : ℕ) {s : List (ℕ × α)}, s.length + cr s < n → Valid s →
    Lettered d s → Fits 0 (canon s) ∧ Iso (run d (canon s)) s := by
  intro n
  induction n with
  | zero => intro s h; omega
  | succ n ih =>
    intro s hn hv hl
    by_cases hadj : ∃ r, Same s r (r + 1)
    · classical
      obtain ⟨r, hr, hmin⟩ : ∃ r, Same s r (r + 1) ∧ ∀ r' < r, ¬ Same s r' (r' + 1) :=
        ⟨Nat.find hadj, Nat.find_spec hadj, fun _ => Nat.find_min hadj⟩
      have hl2 : r + 2 ≤ s.length := hr.lt_right
      obtain ⟨hf, hiso⟩ := ih (s := rmAt s r)
        (by rw [length_rmAt s hl2]; have := cr_rmAt_le hl2; omega) (hv.rmAt hr) (hl.rmAt hl2)
      have hinv := inv_run (d := d) hf
      have hlen : (run d (canon (rmAt s r))).length = s.length - 2 := by
        rw [hiso.length_eq, length_rmAt s hl2]
      rw [canon_adj hv hr hmin]
      refine ⟨(fits_snoc (d := d)).2 ⟨hf, by simp only [Move.Ok]; omega⟩, ?_⟩
      rw [run_append, List.foldl_cons, List.foldl_nil]
      have e1 := insAt_rmAt s (show r + 1 < s.length by omega)
      have eid : (s[r + 1]'(by omega)).1 = (s[r]'(by omega)).1 := by
        have := hr.2.2
        simp only [idAt, List.getElem?_eq_getElem (show r < s.length by omega),
          List.getElem?_eq_getElem (show r + 1 < s.length by omega)] at this
        simpa using this.symm
      have elt : (s[r + 1]'(by omega)).2 = d (s[r]'(by omega)).2 := by
        have := hl r (r + 1) hr (by omega)
        simp only [List.getElem?_eq_getElem (show r < s.length by omega),
          List.getElem?_eq_getElem (show r + 1 < s.length by omega)] at this
        simpa using this
      have e2 : s[r + 1]'(by omega) = ((s[r]'(by omega)).1, d (s[r]'(by omega)).2) :=
        Prod.ext eid elt
      conv_rhs => rw [← e1, e2]
      exact hiso.insAt (by omega) (fun x hx => (hinv.2 x hx).ne)
        (fun x hx => ne_id_of_mem_rmAt hv hr hx) _ _
    · have hno : ∀ r, ¬ Same s r (r + 1) := fun r hr => hadj ⟨r, hr⟩
      by_cases hne : s = []
      · subst hne
        rw [canon_nil]
        exact ⟨trivial, ⟨rfl, fun i j => Iff.rfl⟩⟩
      obtain ⟨q, ho, hc, hq, -⟩ := canon_cross hv hno hne
      have hilv := ilv_of_opn_cls hv (hno q) ho hc
      have hql := hilv.lt
      obtain ⟨hf, hiso⟩ := ih (s := swapAt s q)
        (by rw [length_swapAt]; have := cr_swapAt_lt hv hilv; omega) (hv.swapAt hql)
        (hl.swapAt hql (hno q))
      rw [hq]
      refine ⟨(fits_snoc (d := d)).2 ⟨hf, by simp only [Move.Ok]; rw [hiso.length_eq]; simpa⟩, ?_⟩
      rw [run_append, List.foldl_cons, List.foldl_nil]
      have := hiso.swapAt q
      rwa [swapAt_swapAt] at this

end RunCanon

end StringDiagrams.Chord
