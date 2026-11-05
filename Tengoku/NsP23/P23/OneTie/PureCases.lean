import Tengoku.NsP23.P23.OneTie.PrincipalBorder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 1: dominant pure border count

This file contains only the P1 dominant three-socle geometry reproduced in
the Run-03 command.  In particular, it does not contain the later pure trace
or fibre-product arguments.
-/

namespace P23.OneTie

variable {a b r u v : ℕ} [NeZero a]

/-- The dominant pure three-socle configuration below the last x-layer.-/
def pureDominantSoclesBelow (r u v : ℕ) (hr : r < a - 1) :
    Finset (Normal a b 0) :=
  {pureCore r u v (by omega), pureH r u (by omega), pureZ v}

/-- The exceptional live-tie dominant pure configuration.-/
def pureDominantSoclesLast (v : ℕ) : Finset (Normal a b 0) :=
  {pureCore (a - 1) (b - 1) v (by
      have := Nat.pos_of_ne_zero (NeZero.ne a)
      omega),
    pureH (a - 1) (b - 1) (by
      have := Nat.pos_of_ne_zero (NeZero.ne a)
      omega),
    pureZ v}

/-- Normal form of `xH` below the last x-layer, including the wrapped
`r=a-2` endpoint.-/
def pureBelowXH (r u : ℕ) (hr : r < a - 1) : Normal a b 0 :=
  if hh : r + 1 < a - 1 then
    ⟨r + 2, u + 1 - b, 0, by omega⟩
  else
    ⟨0, u + 1, 0, Nat.pos_of_ne_zero (NeZero.ne a)⟩

def pureBelowYH (r u : ℕ) (hr : r < a - 1) : Normal a b 0 :=
  ⟨r + 1, u + 2 - b, 0, by omega⟩

def pureBelowZH (r u : ℕ) (hr : r < a - 1) : Normal a b 0 :=
  ⟨r + 1, u + 1 - b, 1, by omega⟩

def pureZX (ha : 2 ≤ a) (v : ℕ) : Normal a b 0 := ⟨1, 0, v + 1, by omega⟩
def pureZY (v : ℕ) : Normal a b 0 :=
  ⟨0, 1, v + 1, Nat.pos_of_ne_zero (NeZero.ne a)⟩
def pureZZ (v : ℕ) : Normal a b 0 :=
  ⟨0, 0, v + 2, Nat.pos_of_ne_zero (NeZero.ne a)⟩

/-- The five permanent multiples and the sixth `zH` multiple when `v>0`.-/
def pureDominantExpectedBorderBelow (ha : 2 ≤ a) (r u v : ℕ)
    (hr : r < a - 1) : Finset (Normal a b 0) :=
  {pureBelowXH r u hr, pureBelowYH r u hr, pureZX ha v, pureZY v, pureZZ v} ∪
    (if 0 < v then {pureBelowZH r u hr} else ∅)

def pureBelowStandardNat (a b r u v x y z : ℕ) : Prop :=
  (y ≤ u ∧ z ≤ v ∧ (x ≤ r ∨ (y + b ≤ u ∧ z ≤ v))) ∨
  (y ≤ u + 1 - b ∧ z = 0 ∧
    (x ≤ r + 1 ∨ (y + b ≤ u + 1 - b ∧ z = 0))) ∨
  (y = 0 ∧ z ≤ v + 1 ∧
    (x = 0 ∨ (y + b ≤ 0 ∧ z ≤ v + 1)))

def pureBelowBorderNat (a b r u v x y z : ℕ) : Prop :=
  ((r + 1 < a - 1 ∧ x = r + 2 ∧ y = u + 1 - b ∧ z = 0) ∨
    (¬r + 1 < a - 1 ∧ x = 0 ∧ y = u + 1 ∧ z = 0)) ∨
  (x = r + 1 ∧ y = u + 2 - b ∧ z = 0) ∨
  (x = 1 ∧ y = 0 ∧ z = v + 1) ∨
  (x = 0 ∧ y = 1 ∧ z = v + 1) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 2) ∨
  (0 < v ∧ x = r + 1 ∧ y = u + 1 - b ∧ z = 1)

theorem mem_pureDominantExpectedBorderBelow_iff
    (ha : 2 ≤ a) (r u v : ℕ) (hr : r < a - 1) (m : Normal a b 0) :
    m ∈ pureDominantExpectedBorderBelow (a := a) (b := b) ha r u v hr ↔
      pureBelowBorderNat a b r u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hh : r + 1 < a - 1
  · by_cases hv : 0 < v <;>
      simp [pureDominantExpectedBorderBelow, pureBelowXH, pureBelowYH,
        pureBelowZH, pureZX, pureZY, pureZZ, pureBelowBorderNat, hh, hv]
  · by_cases hv : 0 < v <;>
      simp [pureDominantExpectedBorderBelow, pureBelowXH, pureBelowYH,
        pureBelowZH, pureZX, pureZY, pureZZ, pureBelowBorderNat, hh, hv]

set_option maxHeartbeats 6400000 in
theorem pureBelow_border_arithmetic
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) (hr : r < a - 1)
    (x y z : ℕ) (hxlt : x < a) :
    (¬pureBelowStandardNat a b r u v x y z ∧
      (if 0 < x then pureBelowStandardNat a b r u v (x - 1) y z
       else if b ≤ y then pureBelowStandardNat a b r u v (a - 1) (y - b) z
       else True) ∧
      (0 < y → pureBelowStandardNat a b r u v x (y - 1) z) ∧
      (0 < z → pureBelowStandardNat a b r u v x y (z - 1))) ↔
      pureBelowBorderNat a b r u v x y z := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y <;> by_cases hz : 0 < z <;>
      by_cases hh : r + 1 < a - 1
    all_goals simp [hx, hy, hz, hh, pureBelowStandardNat,
      pureBelowBorderNat] <;> grind (splits := 64)
  · have hx0 : x = 0 := by omega
    by_cases hby : b ≤ y
    · by_cases hy : 0 < y <;> by_cases hz : 0 < z <;>
        by_cases hh : r + 1 < a - 1
      all_goals simp [hx, hx0, hby, hy, hz, hh, pureBelowStandardNat,
        pureBelowBorderNat] <;> grind (splits := 64)
    · by_cases hy : 0 < y <;> by_cases hz : 0 < z <;>
        by_cases hh : r + 1 < a - 1
      all_goals simp [hx, hx0, hby, hy, hz, hh, pureBelowStandardNat,
        pureBelowBorderNat] <;> grind (splits := 64)

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
theorem pureDominantBorder_below_exact
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) (hr : r < a - 1) :
    borderFinset (pureDominantSoclesBelow (a := a) (b := b) r u v hr) =
      pureDominantExpectedBorderBelow (a := a) (b := b) ha r u v hr := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp [pureDominantSoclesBelow])]
  rw [mem_pureDominantExpectedBorderBelow_iff ha r u v hr]
  rcases m with ⟨mx, my, mz, hmx⟩
  have harith := pureBelow_border_arithmetic (v := v) ha hb hu hr mx my mz hmx
  by_cases hx : 0 < mx
  · simp [IsMinimalBorder, ApplicablePredecessorsSurvive,
      standardSet, pureDominantSoclesBelow, Normal.exact_divides_iff,
      Normal.DividesCriterion, pureBelowStandardNat, Normal.predecessor,
      Normal.xPredecessor, Normal.yPredecessor, Normal.zPredecessor,
      pureCore, pureH, pureZ, hx, hr] at harith ⊢
    grind
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive,
        standardSet, pureDominantSoclesBelow, Normal.exact_divides_iff,
        Normal.DividesCriterion, pureBelowStandardNat, Normal.predecessor,
        Normal.wrappedXPredecessor, Normal.yPredecessor,
        Normal.zPredecessor, pureCore, pureH, pureZ, hx, hx0, hby, hr]
        at harith ⊢
      grind
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive,
        standardSet, pureDominantSoclesBelow, Normal.exact_divides_iff,
        Normal.DividesCriterion, pureBelowStandardNat, Normal.predecessor,
        Normal.yPredecessor, Normal.zPredecessor, pureCore, pureH, pureZ,
        hx, hx0, hby, hr] at harith ⊢
      grind

theorem pureDominantBorder_below_card
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) (hr : r < a - 1) :
    (borderFinset (pureDominantSoclesBelow (a := a) (b := b) r u v hr)).card =
      if 0 < v then 6 else 5 := by
  rw [pureDominantBorder_below_exact ha hb hu hr]
  let A := pureBelowXH (a := a) (b := b) r u hr
  let B := pureBelowYH (a := a) (b := b) r u hr
  let C := pureZX (a := a) (b := b) ha v
  let D := pureZY (a := a) (b := b) v
  let E := pureZZ (a := a) (b := b) v
  let F := pureBelowZH (a := a) (b := b) r u hr
  let s : Finset (Normal a b 0) := {A, B, C, D, E}
  by_cases hh : r + 1 < a - 1
  · have hA : A ∉ ({B, C, D, E} : Finset (Normal a b 0)) := by
      simp [A, B, C, D, E, pureBelowXH, pureBelowYH, pureZX, pureZY,
        pureZZ, hh]
    have hB : B ∉ ({C, D, E} : Finset (Normal a b 0)) := by
      simp [B, C, D, E, pureBelowYH, pureZX, pureZY, pureZZ]
    have hC : C ∉ ({D, E} : Finset (Normal a b 0)) := by
      simp [C, D, E, pureZX, pureZY, pureZZ]
    have hD : D ∉ ({E} : Finset (Normal a b 0)) := by
      simp [D, E, pureZY, pureZZ]
    have hs : s.card = 5 := by
      dsimp [s]
      rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB,
        Finset.card_insert_of_notMem hC, Finset.card_insert_of_notMem hD]
      simp
    by_cases hv : 0 < v
    · have hF : F ∉ s := by
        simp [F, s, A, B, C, D, E, pureBelowZH, pureBelowXH,
          pureBelowYH, pureZX, pureZY, pureZZ, hh]
        omega
      rw [ite_eq_left hv]
      simp only [pureDominantExpectedBorderBelow, ite_eq_left hv]
      change (s ∪ {F}).card = 6
      simp [Finset.card_insert_of_notMem hF, hs]
    · simpa [pureDominantExpectedBorderBelow, hv, s, A, B, C, D, E]
        using hs
  · have hA : A ∉ ({B, C, D, E} : Finset (Normal a b 0)) := by
      simp [A, B, C, D, E, pureBelowXH, pureBelowYH, pureZX, pureZY,
        pureZZ, hh]
    have hB : B ∉ ({C, D, E} : Finset (Normal a b 0)) := by
      simp [B, C, D, E, pureBelowYH, pureZX, pureZY, pureZZ]
    have hC : C ∉ ({D, E} : Finset (Normal a b 0)) := by
      simp [C, D, E, pureZX, pureZY, pureZZ]
    have hD : D ∉ ({E} : Finset (Normal a b 0)) := by
      simp [D, E, pureZY, pureZZ]
    have hs : s.card = 5 := by
      dsimp [s]
      rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB,
        Finset.card_insert_of_notMem hC, Finset.card_insert_of_notMem hD]
      simp
    by_cases hv : 0 < v
    · have hF : F ∉ s := by
        simp [F, s, A, B, C, D, E, pureBelowZH, pureBelowXH,
          pureBelowYH, pureZX, pureZY, pureZZ, hh]
        omega
      rw [ite_eq_left hv]
      simp only [pureDominantExpectedBorderBelow, ite_eq_left hv]
      change (s ∪ {F}).card = 6
      simp [Finset.card_insert_of_notMem hF, hs]
    · simpa [pureDominantExpectedBorderBelow, hv, s, A, B, C, D, E]
        using hs

/-! ### Exceptional live-tie branch `r=a-1`, `u=b-1` -/

def pureLastXH (ha : 2 ≤ a) : Normal a b 0 := ⟨1, b, 0, by omega⟩
def pureLastYH : Normal a b 0 :=
  ⟨0, b + 1, 0, Nat.pos_of_ne_zero (NeZero.ne a)⟩
def pureLastZH : Normal a b 0 :=
  ⟨0, b, 1, Nat.pos_of_ne_zero (NeZero.ne a)⟩

def pureDominantExpectedBorderLast (ha : 2 ≤ a) (v : ℕ) :
    Finset (Normal a b 0) :=
  {pureLastXH ha, pureLastYH, pureZX ha v, pureZY v, pureZZ v} ∪
    (if 0 < v then {pureLastZH} else ∅)

def pureLastStandardNat (a b v x y z : ℕ) : Prop :=
  (y ≤ b - 1 ∧ z ≤ v) ∨
  (z = 0 ∧ ((x = 0 ∧ y ≤ b) ∨ y = 0)) ∨
  (x = 0 ∧ y = 0 ∧ z ≤ v + 1)

def pureLastBorderNat (b v x y z : ℕ) : Prop :=
  (x = 1 ∧ y = b ∧ z = 0) ∨
  (x = 0 ∧ y = b + 1 ∧ z = 0) ∨
  (x = 1 ∧ y = 0 ∧ z = v + 1) ∨
  (x = 0 ∧ y = 1 ∧ z = v + 1) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 2) ∨
  (0 < v ∧ x = 0 ∧ y = b ∧ z = 1)

theorem mem_pureDominantExpectedBorderLast_iff
    (ha : 2 ≤ a) (v : ℕ) (m : Normal a b 0) :
    m ∈ pureDominantExpectedBorderLast (a := a) (b := b) ha v ↔
      pureLastBorderNat b v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hv : 0 < v <;>
    simp [pureDominantExpectedBorderLast, pureLastXH, pureLastYH,
      pureLastZH, pureZX, pureZY, pureZZ, pureLastBorderNat, hv]

set_option maxHeartbeats 6400000 in
theorem pureLast_border_arithmetic
    (ha : 2 ≤ a) (hb : 2 ≤ b) (x y z : ℕ) (hxlt : x < a) :
    (¬pureLastStandardNat a b v x y z ∧
      (if 0 < x then pureLastStandardNat a b v (x - 1) y z
       else if b ≤ y then pureLastStandardNat a b v (a - 1) (y - b) z
       else True) ∧
      (0 < y → pureLastStandardNat a b v x (y - 1) z) ∧
      (0 < z → pureLastStandardNat a b v x y (z - 1))) ↔
      pureLastBorderNat b v x y z := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y <;> by_cases hz : 0 < z <;>
      by_cases hx1 : x = 1 <;> by_cases hy0 : y = 0 <;>
      by_cases hyb : y = b <;> by_cases hz0 : z = 0 <;>
      by_cases hzv : z = v + 1
    all_goals simp_all [pureLastStandardNat, pureLastBorderNat] <;> omega
  · have hx0 : x = 0 := by omega
    by_cases hby : b ≤ y
    · by_cases hy : 0 < y <;> by_cases hz : 0 < z <;>
        by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;>
        by_cases hyb : y = b <;> by_cases hybp : y = b + 1 <;>
        by_cases hz0 : z = 0 <;> by_cases hz1 : z = 1 <;>
        by_cases hzv : z = v + 1 <;> by_cases hzv2 : z = v + 2
      all_goals simp_all [pureLastStandardNat, pureLastBorderNat] <;> omega
    · by_cases hy : 0 < y <;> by_cases hz : 0 < z <;>
        by_cases hy0 : y = 0 <;> by_cases hy1 : y = 1 <;>
        by_cases hyb : y = b <;> by_cases hybp : y = b + 1 <;>
        by_cases hz0 : z = 0 <;> by_cases hz1 : z = 1 <;>
        by_cases hzv : z = v + 1 <;> by_cases hzv2 : z = v + 2
      all_goals simp_all [pureLastStandardNat, pureLastBorderNat] <;> omega

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
theorem pureDominantBorder_last_exact
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    borderFinset (pureDominantSoclesLast (a := a) (b := b) v) =
      pureDominantExpectedBorderLast (a := a) (b := b) ha v := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp [pureDominantSoclesLast])]
  rw [mem_pureDominantExpectedBorderLast_iff ha v]
  rcases m with ⟨mx, my, mz, hmx⟩
  have harith := pureLast_border_arithmetic (v := v) ha hb mx my mz hmx
  have hlast : ¬a - 1 < a - 1 := by omega
  by_cases hx : 0 < mx
  · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
      pureDominantSoclesLast, Normal.exact_divides_iff,
      Normal.DividesCriterion, pureLastStandardNat, Normal.predecessor,
      Normal.xPredecessor, Normal.yPredecessor, Normal.zPredecessor,
      pureCore, pureH, pureZ, hx, hlast] at harith ⊢
    grind
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
        pureDominantSoclesLast, Normal.exact_divides_iff,
        Normal.DividesCriterion, pureLastStandardNat, Normal.predecessor,
        Normal.wrappedXPredecessor, Normal.yPredecessor,
        Normal.zPredecessor, pureCore, pureH, pureZ, hx, hx0, hby, hlast]
        at harith ⊢
      grind
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
        pureDominantSoclesLast, Normal.exact_divides_iff,
        Normal.DividesCriterion, pureLastStandardNat, Normal.predecessor,
        Normal.yPredecessor, Normal.zPredecessor, pureCore, pureH, pureZ,
        hx, hx0, hby, hlast] at harith ⊢
      grind

theorem pureDominantBorder_last_card
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (borderFinset (pureDominantSoclesLast (a := a) (b := b) v)).card =
      if 0 < v then 6 else 5 := by
  rw [pureDominantBorder_last_exact ha hb]
  let A := pureLastXH (a := a) (b := b) ha
  let B := pureLastYH (a := a) (b := b)
  let C := pureZX (a := a) (b := b) ha v
  let D := pureZY (a := a) (b := b) v
  let E := pureZZ (a := a) (b := b) v
  let F := pureLastZH (a := a) (b := b)
  let s : Finset (Normal a b 0) := {A, B, C, D, E}
  have hA : A ∉ ({B, C, D, E} : Finset (Normal a b 0)) := by
    simp [A, B, C, D, E, pureLastXH, pureLastYH, pureZX, pureZY,
      pureZZ]
  have hB : B ∉ ({C, D, E} : Finset (Normal a b 0)) := by
    simp [B, C, D, E, pureLastYH, pureZX, pureZY, pureZZ]
  have hC : C ∉ ({D, E} : Finset (Normal a b 0)) := by
    simp [C, D, E, pureZX, pureZY, pureZZ]
  have hD : D ∉ ({E} : Finset (Normal a b 0)) := by
    simp [D, E, pureZY, pureZZ]
  have hs : s.card = 5 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB,
      Finset.card_insert_of_notMem hC, Finset.card_insert_of_notMem hD]
    simp
  by_cases hv : 0 < v
  · have hF : F ∉ s := by
      simp [F, s, A, B, C, D, E, pureLastZH, pureLastXH,
        pureLastYH, pureZX, pureZY, pureZZ]
      omega
    rw [ite_eq_left hv]
    simp only [pureDominantExpectedBorderLast, ite_eq_left hv]
    change (s ∪ {F}).card = 6
    simp [Finset.card_insert_of_notMem hF, hs]
  · simpa [pureDominantExpectedBorderLast, hv, s, A, B, C, D, E]
      using hs

/-- Both command-authorized live-tie branches have six final border points
when `v≥1`.-/
theorem pureDominant_card_of_pos
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    (∀ (hr : r < a - 1), b ≤ u →
      (borderFinset (pureDominantSoclesBelow (a := a) (b := b)
        r u v hr)).card = 6) ∧
    (borderFinset (pureDominantSoclesLast (a := a) (b := b) v)).card = 6 := by
  constructor
  · intro hr hu
    have hv' : 0 < v := by omega
    simpa [hv'] using
      (pureDominantBorder_below_card (v := v) ha hb hu hr)
  · have hv' : 0 < v := by omega
    simpa [hv'] using pureDominantBorder_last_card (v := v) ha hb

/-- Both command-authorized live-tie branches have five final border points
when `v=0`.-/
theorem pureDominant_card_of_zero
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (∀ (hr : r < a - 1), b ≤ u →
      (borderFinset (pureDominantSoclesBelow (a := a) (b := b)
        r u 0 hr)).card = 5) ∧
    (borderFinset (pureDominantSoclesLast (a := a) (b := b) 0)).card = 5 := by
  constructor
  · intro hr hu
    simpa using pureDominantBorder_below_card (v := 0) ha hb hu hr
  · simpa using pureDominantBorder_last_card (v := 0) ha hb

/-- Neither command-authorized dominant pure branch can have cardinality
four.-/
theorem pureDominant_card_ne_four
    (ha : 2 ≤ a) (hb : 2 ≤ b) :
    (∀ (hr : r < a - 1), b ≤ u →
      (borderFinset (pureDominantSoclesBelow (a := a) (b := b)
        r u v hr)).card ≠ 4) ∧
    (borderFinset (pureDominantSoclesLast (a := a) (b := b) v)).card ≠ 4 := by
  constructor
  · intro hr hu
    rw [pureDominantBorder_below_card ha hb hu hr]
    split <;> decide
  · rw [pureDominantBorder_last_card (v := v) ha hb]
    split <;> decide

end P23.OneTie
