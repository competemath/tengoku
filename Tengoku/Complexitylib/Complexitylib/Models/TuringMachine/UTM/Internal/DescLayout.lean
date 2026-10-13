/-
Copyright (c) 2025 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.UTM.Internal.VTape
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.UTM.Internal.Desc
public import Tengoku.Complexitylib.Complexitylib.Models.TuringMachine.UTM.Internal.HaltTest

/-!
# Description-tape layout

Positional facts about a tape holding a description string
`l = qsF □ qhF □ R` (the `takeField` split): where the two header fields
end, and what the cells of the entry region are. Everything is derived
from a single normalization: the `getElem?`-with-blank-default view of `l`
agrees with its *canonical* three-part layout even when trailing separators
are missing (`takeField` treats end-of-list like `□` — by design, matching
the tape's blank fill).

These feed the seek phase (two `scanRight_loop` instances land the desc
head at the entry region) and the match loop (entry-region cells).
-/

public section

namespace Complexity

namespace TM.UTMBody

/-- `getElem?`-with-blank-default is insensitive to a trailing blank.
@isnad1 id=eq.0h2v.s6.bf359acdac92 from=translated src=- shape=ce3850fd vocab=a68a656f
-/
theorem getD_append_blank (l : List Γw) (i : ℕ) :
    (((l ++ [Γw.blank])[i]?).getD Γw.blank) = ((l[i]?).getD Γw.blank) := by
  rcases Nat.lt_trichotomy i l.length with hi | hi | hi
  · rw [List.getElem?_append_left hi]
  · subst hi
    rw [List.getElem?_append_right (Nat.le_refl _),
      List.getElem?_eq_none (by omega : l.length ≤ l.length)]
    simp
  · rw [List.getElem?_eq_none (by simp; omega),
      List.getElem?_eq_none (by omega)]

/-- The canonical three-part layout of a description string. -/
def canonical (l : List Γw) : List Γw :=
  (takeField l).1 ++ Γw.blank ::
    ((takeField (takeField l).2).1 ++ Γw.blank :: (takeField (takeField l).2).2)

/-- Blank-default cell access agrees with the canonical layout, whether or
    not the trailing separators are present in `l`.
@isnad1 id=eq.0h2v.s5.0fb166c3d1e1 from=translated src=- shape=017be6f4 vocab=72ae4b81
-/
theorem getD_canonical (l : List Γw) (i : ℕ) :
    ((l[i]?).getD Γw.blank) = ((canonical l)[i]?).getD Γw.blank := by
  rcases takeField_structure l with h1 | ⟨h1, h1'⟩
  · rcases takeField_structure (takeField l).2 with h2 | ⟨h2, h2'⟩
    · have hcan : canonical l = (takeField l).1 ++ Γw.blank :: (takeField l).2 := by
        unfold canonical
        rw [← h2]
      rw [hcan, ← h1]
    · have hcan : canonical l
          = ((takeField l).1 ++ Γw.blank :: (takeField l).2) ++ [Γw.blank] := by
        unfold canonical
        rw [h2, h2']
        simp
      rw [hcan, ← h1, getD_append_blank]
  · have hcan : canonical l = (l ++ [Γw.blank]) ++ [Γw.blank] := by
      unfold canonical
      rw [h1, h1']
      simp [takeField]
    rw [hcan, getD_append_blank, getD_append_blank]

/-- Cell contents of a `HoldsExact` tape, in blank-default form.
@isnad1 id=eq.1h3v.s5.3fd925efd0fc from=translated src=- shape=48f3b14f vocab=17418c23
-/
theorem holdsExact_cells_getD {t : Tape} {l : List Γw} (h : t.HoldsExact l)
    (i : ℕ) : t.cells (i + 1) = ((l[i]?).getD Γw.blank).toΓ := by
  rw [h.2 i]
  split
  · next hi => rw [List.getElem?_eq_getElem hi]; rfl
  · next hi => rw [List.getElem?_eq_none (by omega)]; rfl

-- ════════════════════════════════════════════════════════════════════════
-- The four seek facts and the entry region
-- ════════════════════════════════════════════════════════════════════════

/-- Field-1 cells are non-blank.
@isnad1 id=ne.2h3v.s5.88983a7c67bd from=translated src=- shape=55519669 vocab=748b6c58
-/
theorem descLayout_field1 {t : Tape} {l : List Γw} (h : t.HoldsExact l) :
    ∀ j, j < (takeField l).1.length → t.cells (1 + j) ≠ Γ.blank := by
  intro j hj
  rw [show 1 + j = j + 1 by omega, holdsExact_cells_getD h, getD_canonical]
  unfold canonical
  rw [List.getElem?_append_left (by omega), List.getElem?_eq_getElem hj,
    Option.getD_some]
  have := takeField_fst_ne_blank l _ (List.getElem_mem hj)
  cases hne : (takeField l).1[j] <;> simp_all [Γw.toΓ]

/-- The separator after field 1.
@isnad1 id=eq.1h2v.s5.8883fb7c1d9e from=translated src=- shape=03af164d vocab=b7777e2b
-/
theorem descLayout_sep1 {t : Tape} {l : List Γw} (h : t.HoldsExact l) :
    t.cells (1 + (takeField l).1.length) = Γ.blank := by
  rw [show 1 + (takeField l).1.length = (takeField l).1.length + 1 by omega,
    holdsExact_cells_getD h, getD_canonical]
  unfold canonical
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- Field-2 cells are non-blank.
@isnad1 id=ne.2h3v.s6.15cc2032333c from=translated src=- shape=5e245bd8 vocab=a72ed69b
-/
theorem descLayout_field2 {t : Tape} {l : List Γw} (h : t.HoldsExact l) :
    ∀ j, j < (takeField (takeField l).2).1.length →
      t.cells ((takeField l).1.length + 2 + j) ≠ Γ.blank := by
  intro j hj
  rw [show (takeField l).1.length + 2 + j = ((takeField l).1.length + 1 + j) + 1
      by omega,
    holdsExact_cells_getD h, getD_canonical]
  unfold canonical
  rw [List.getElem?_append_right (by omega),
    show (takeField l).1.length + 1 + j - (takeField l).1.length = j + 1 by omega]
  rw [show ((Γw.blank :: ((takeField (takeField l).2).1 ++ Γw.blank ::
      (takeField (takeField l).2).2))[j + 1]?)
      = (((takeField (takeField l).2).1 ++ Γw.blank ::
        (takeField (takeField l).2).2)[j]?) from rfl]
  rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, Option.getD_some]
  have := takeField_fst_ne_blank (takeField l).2 _ (List.getElem_mem hj)
  cases hne : (takeField (takeField l).2).1[j] <;> simp_all [Γw.toΓ]

/-- The separator after field 2.
@isnad1 id=eq.1h2v.s5.26f349f98d18 from=translated src=- shape=ec5d436f vocab=a6a97ece
-/
theorem descLayout_sep2 {t : Tape} {l : List Γw} (h : t.HoldsExact l) :
    t.cells ((takeField l).1.length + 2 + (takeField (takeField l).2).1.length)
      = Γ.blank := by
  rw [show (takeField l).1.length + 2 + (takeField (takeField l).2).1.length
      = ((takeField l).1.length + 1 + (takeField (takeField l).2).1.length) + 1
      by omega,
    holdsExact_cells_getD h, getD_canonical]
  unfold canonical
  rw [List.getElem?_append_right (by omega),
    show (takeField l).1.length + 1 + (takeField (takeField l).2).1.length
      - (takeField l).1.length = (takeField (takeField l).2).1.length + 1 by omega]
  rw [show ((Γw.blank :: ((takeField (takeField l).2).1 ++ Γw.blank ::
      (takeField (takeField l).2).2))[(takeField (takeField l).2).1.length + 1]?)
      = (((takeField (takeField l).2).1 ++ Γw.blank ::
        (takeField (takeField l).2).2)[(takeField (takeField l).2).1.length]?)
      from rfl]
  rw [List.getElem?_append_right (Nat.le_refl _)]
  simp

/-- Entry-region cells: cell `|F1| + |F2| + 3 + j` holds the `j`-th symbol
    of the entry region `R := (takeField (takeField l).2).2` (blank beyond).
@isnad1 id=eq.1h3v.s6.410188373bfa from=translated src=- shape=81a28b67 vocab=0965b3c3
-/
theorem descLayout_entries {t : Tape} {l : List Γw} (h : t.HoldsExact l)
    (j : ℕ) :
    t.cells ((takeField l).1.length + (takeField (takeField l).2).1.length + 3 + j)
      = (((takeField (takeField l).2).2[j]?).getD Γw.blank).toΓ := by
  rw [show (takeField l).1.length + (takeField (takeField l).2).1.length + 3 + j
      = ((takeField l).1.length + (takeField (takeField l).2).1.length + 2 + j) + 1
      by omega,
    holdsExact_cells_getD h, getD_canonical]
  unfold canonical
  rw [List.getElem?_append_right (by omega),
    show (takeField l).1.length + (takeField (takeField l).2).1.length + 2 + j
      - (takeField l).1.length
      = ((takeField (takeField l).2).1.length + 1 + j) + 1 by omega]
  rw [show ((Γw.blank :: ((takeField (takeField l).2).1 ++ Γw.blank ::
      (takeField (takeField l).2).2))[((takeField (takeField l).2).1.length + 1 + j) + 1]?)
      = (((takeField (takeField l).2).1 ++ Γw.blank ::
        (takeField (takeField l).2).2)[(takeField (takeField l).2).1.length + 1 + j]?)
      from rfl]
  rw [List.getElem?_append_right (by omega),
    show (takeField (takeField l).2).1.length + 1 + j
      - (takeField (takeField l).2).1.length = j + 1 by omega]
  rfl

/-- Field-1 cell values.
@isnad1 id=eq.2h3v.s6.b04a738bee1d from=translated src=- shape=e4f955d4 vocab=cb97bc7c
-/
theorem descLayout_field1_val {t : Tape} {l : List Γw} (h : t.HoldsExact l) :
    ∀ j, (hj : j < (takeField l).1.length) →
      t.cells (1 + j) = ((takeField l).1[j]).toΓ := by
  intro j hj
  rw [show 1 + j = j + 1 by omega, holdsExact_cells_getD h, getD_canonical]
  unfold canonical
  rw [List.getElem?_append_left (by omega), List.getElem?_eq_getElem hj,
    Option.getD_some]

/-- Field-2 cell values.
@isnad1 id=eq.2h3v.s6.2d29049612ee from=translated src=- shape=4a4b5a10 vocab=e5ebf331
-/
theorem descLayout_field2_val {t : Tape} {l : List Γw} (h : t.HoldsExact l) :
    ∀ j, (hj : j < (takeField (takeField l).2).1.length) →
      t.cells ((takeField l).1.length + 2 + j)
        = ((takeField (takeField l).2).1[j]).toΓ := by
  intro j hj
  rw [show (takeField l).1.length + 2 + j = ((takeField l).1.length + 1 + j) + 1
      by omega,
    holdsExact_cells_getD h, getD_canonical]
  unfold canonical
  rw [List.getElem?_append_right (by omega),
    show (takeField l).1.length + 1 + j - (takeField l).1.length = j + 1 by omega]
  rw [show ((Γw.blank :: ((takeField (takeField l).2).1 ++ Γw.blank ::
      (takeField (takeField l).2).2))[j + 1]?)
      = (((takeField (takeField l).2).1 ++ Γw.blank ::
        (takeField (takeField l).2).2)[j]?) from rfl]
  rw [List.getElem?_append_left hj, List.getElem?_eq_getElem hj, Option.getD_some]

/-- Field-2 cell values, blank-default form (covers positions beyond the
    field: the separator/beyond reads `□`).
@isnad1 id=eq.2h3v.s6.28dc80349338 from=translated src=- shape=57c700a4 vocab=91ee437c
-/
theorem descLayout_field2_getD {t : Tape} {l : List Γw} (h : t.HoldsExact l)
    (j : ℕ) (hj : j ≤ (takeField (takeField l).2).1.length) :
    t.cells ((takeField l).1.length + 2 + j)
      = (((takeField (takeField l).2).1[j]?).getD Γw.blank).toΓ := by
  rcases Nat.lt_or_ge j (takeField (takeField l).2).1.length with hlt | hge
  · rw [descLayout_field2_val h j hlt, List.getElem?_eq_getElem hlt,
      Option.getD_some]
  · have hj' : j = (takeField (takeField l).2).1.length := by omega
    subst hj'
    rw [descLayout_sep2 h, List.getElem?_eq_none (Nat.le_refl _)]
    rfl

/-- **First mismatch extraction**: two different blank-free lists, viewed as
    blank-padded infinite sequences, have a least disagreement index; below
    it they agree on non-blank symbols, and at it the `hc1`-style mismatch
    conditions hold.
@isnad1 id=ex.3h2v.s7.c569c16501eb from=translated src=- shape=7daad595 vocab=c9f92750
-/
theorem exists_first_mismatch {A B : List Γw}
    (hA : ∀ s ∈ A, s ≠ Γw.blank) (hB : ∀ s ∈ B, s ≠ Γw.blank)
    (hne : A ≠ B) :
    ∃ n, n ≤ A.length ∧ n ≤ B.length ∧
      (∀ j, j < n → ((A[j]?).getD Γw.blank) = ((B[j]?).getD Γw.blank) ∧
        ((A[j]?).getD Γw.blank) ≠ Γw.blank) ∧
      ((A[n]?).getD Γw.blank) ≠ ((B[n]?).getD Γw.blank) := by
  induction A generalizing B with
  | nil =>
    cases B with
    | nil => exact absurd rfl hne
    | cons b bs =>
      refine ⟨0, by omega, by omega, fun j hj => by omega, ?_⟩
      have hb : b ≠ Γw.blank := hB b (List.mem_cons_self ..)
      simpa using fun hcon => hb hcon.symm
  | cons a as ih =>
    cases B with
    | nil =>
      refine ⟨0, by omega, by omega, fun j hj => by omega, ?_⟩
      have ha : a ≠ Γw.blank := hA a (List.mem_cons_self ..)
      simpa using ha
    | cons b bs =>
      by_cases hab : a = b
      · subst hab
        have hne' : as ≠ bs := fun hcon => hne (by rw [hcon])
        obtain ⟨n, hnA, hnB, hagree, hmm⟩ :=
          ih (fun s hs => hA s (List.mem_cons_of_mem _ hs))
            (fun s hs => hB s (List.mem_cons_of_mem _ hs)) hne'
        refine ⟨n + 1, by simpa using hnA, by simpa using hnB, ?_, ?_⟩
        · intro j hj
          cases j with
          | zero =>
            refine ⟨rfl, ?_⟩
            simpa using hA a (List.mem_cons_self ..)
          | succ j' =>
            have := hagree j' (by omega)
            simpa using this
        · simpa using hmm
      · refine ⟨0, by omega, by omega, fun j hj => by omega, ?_⟩
        simpa using hab

end TM.UTMBody

end Complexity
