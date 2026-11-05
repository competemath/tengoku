import Tengoku.NsP23.P23.OneTie.NonDominantRows
import Tengoku.NsP23.P23.OneTie.MixedCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact last-layer dominant geometry

This module adds the two last-x-layer families missing from the frozen Run-03
library.  It does not change the meaning of any earlier scoped declaration.
-/

namespace P23.OneTie

variable {a b c u v : ℕ} [NeZero a]

private theorem last_a_pos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)

/-! ## Mixed last layer -/

def mixedDominantSoclesLast (u v : ℕ) : Finset (Normal a b c) :=
  {mixedCore (a - 1) u v (by
      have := last_a_pos (a := a)
      omega), mixedY u, mixedZ v}

def mixedDominantExpectedBorderLast (ha : 2 ≤ a) (u v : ℕ) :
    Finset (Normal a b c) :=
  {mixedYTimesX ha u, mixedYTimesY u, mixedYTimesZ u,
    mixedZTimesX ha v, mixedZTimesY v, mixedZTimesZ v}

def dominantLastStandardNat (u v x y z : ℕ) : Prop :=
  (y ≤ u ∧ z ≤ v) ∨
  (x = 0 ∧ z = 0 ∧ y ≤ u + 1) ∨
  (x = 0 ∧ y = 0 ∧ z ≤ v + 1)

def mixedDominantLastBorderNat (u v x y z : ℕ) : Prop :=
  (x = 1 ∧ y = u + 1 ∧ z = 0) ∨
  (x = 0 ∧ y = u + 2 ∧ z = 0) ∨
  (x = 0 ∧ y = u + 1 ∧ z = 1) ∨
  (x = 1 ∧ y = 0 ∧ z = v + 1) ∨
  (x = 0 ∧ y = 1 ∧ z = v + 1) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 2)

theorem mem_standardSet_mixedDominantSoclesLast_iff
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (p : Normal a b c) :
    p ∈ standardSet (mixedDominantSoclesLast (a := a) (b := b) (c := c) u v) ↔
      dominantLastStandardNat u v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, mixedDominantSoclesLast, mixedCore, mixedY, mixedZ,
    Normal.exact_divides_iff, Normal.DividesCriterion,
    dominantLastStandardNat]
  omega

theorem mem_mixedDominantExpectedBorderLast_iff
    (ha : 2 ≤ a) (m : Normal a b c) :
    m ∈ mixedDominantExpectedBorderLast (a := a) (b := b) (c := c) ha u v ↔
      mixedDominantLastBorderNat u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  simp [mixedDominantExpectedBorderLast, mixedDominantLastBorderNat,
    mixedYTimesX, mixedYTimesY, mixedYTimesZ, mixedZTimesX,
    mixedZTimesY, mixedZTimesZ, Normal.ext_iff]

set_option maxHeartbeats 6400000 in
theorem mixedDominantLast_border_arithmetic
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (x y z : ℕ) (hxlt : x < a) :
    ((¬dominantLastStandardNat u v x y z ∧
      (if 0 < x then dominantLastStandardNat u v (x - 1) y z
       else if b ≤ y ∧ c ≤ z then
         dominantLastStandardNat u v (a - 1) (y - b) (z - c)
       else True) ∧
      (0 < y → dominantLastStandardNat u v x (y - 1) z) ∧
      (0 < z → dominantLastStandardNat u v x y (z - 1))) ↔
      mixedDominantLastBorderNat u v x y z) := by
  by_cases hx : 0 < x <;> by_cases hby : b ≤ y <;> by_cases hcz : c ≤ z
  all_goals
    simp [hx, hby, hcz, dominantLastStandardNat,
      mixedDominantLastBorderNat] <;> grind (splits := 32)

theorem mixedDominantLast_border_exact
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) :
    borderFinset (mixedDominantSoclesLast (a := a) (b := b) (c := c) u v) =
      mixedDominantExpectedBorderLast (a := a) (b := b) (c := c) ha u v := by
  apply borderFinset_eq_expected_of_nat _ _
    (dominantLastStandardNat u v) (mixedDominantLastBorderNat u v)
  · simp [mixedDominantSoclesLast]
  · intro p
    exact mem_standardSet_mixedDominantSoclesLast_iff ha hb hc p
  · intro m
    exact mem_mixedDominantExpectedBorderLast_iff ha m
  · exact mixedDominantLast_border_arithmetic ha hb hc hu hv

theorem mixedDominantLast_border_card
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) :
    (borderFinset
      (mixedDominantSoclesLast (a := a) (b := b) (c := c) u v)).card = 6 := by
  rw [mixedDominantLast_border_exact ha hb hc hu hv]
  let A := mixedYTimesX (a := a) (b := b) (c := c) ha u
  let B := mixedYTimesY (a := a) (b := b) (c := c) u
  let C := mixedYTimesZ (a := a) (b := b) (c := c) u
  let D := mixedZTimesX (a := a) (b := b) (c := c) ha v
  let E := mixedZTimesY (a := a) (b := b) (c := c) v
  let F := mixedZTimesZ (a := a) (b := b) (c := c) v
  have hA : A ∉ ({B, C, D, E, F} : Finset (Normal a b c)) := by
    simp [A, B, C, D, E, F, mixedYTimesX, mixedYTimesY,
      mixedYTimesZ, mixedZTimesX, mixedZTimesY, mixedZTimesZ]
  have hB : B ∉ ({C, D, E, F} : Finset (Normal a b c)) := by
    simp [B, C, D, E, F, mixedYTimesY, mixedYTimesZ,
      mixedZTimesX, mixedZTimesY, mixedZTimesZ]
  have hC : C ∉ ({D, E, F} : Finset (Normal a b c)) := by
    simp [C, D, E, F, mixedYTimesZ, mixedZTimesX,
      mixedZTimesY, mixedZTimesZ]
    omega
  have hD : D ∉ ({E, F} : Finset (Normal a b c)) := by
    simp [D, E, F, mixedZTimesX, mixedZTimesY, mixedZTimesZ]
  have hE : E ∉ ({F} : Finset (Normal a b c)) := by
    simp [E, F, mixedZTimesY, mixedZTimesZ]
  change ({A, B, C, D, E, F} : Finset (Normal a b c)).card = 6
  rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB,
    Finset.card_insert_of_notMem hC, Finset.card_insert_of_notMem hD,
    Finset.card_insert_of_notMem hE]
  simp

/-! ## Pure last layer with the tie in the principal core -/

def pureDominantSoclesLastCore (u v : ℕ) : Finset (Normal a b 0) :=
  {pureCore (a - 1) u v (by
      have := last_a_pos (a := a)
      omega),
    pureH (a - 1) u (by
      have := last_a_pos (a := a)
      omega), pureZ v}

def pureLastCoreXH (ha : 2 ≤ a) (u : ℕ) : Normal a b 0 :=
  ⟨1, u + 1, 0, by omega⟩
def pureLastCoreYH (u : ℕ) : Normal a b 0 :=
  ⟨0, u + 2, 0, last_a_pos⟩
def pureLastCoreZH (u : ℕ) : Normal a b 0 :=
  ⟨0, u + 1, 1, last_a_pos⟩
def pureLastCoreXZ (ha : 2 ≤ a) (v : ℕ) : Normal a b 0 :=
  ⟨1, 0, v + 1, by omega⟩
def pureLastCoreYZ (v : ℕ) : Normal a b 0 :=
  ⟨0, 1, v + 1, last_a_pos⟩
def pureLastCoreZZ (v : ℕ) : Normal a b 0 :=
  ⟨0, 0, v + 2, last_a_pos⟩

def pureDominantExpectedBorderLastCore (ha : 2 ≤ a) (u v : ℕ) :
    Finset (Normal a b 0) :=
  {pureLastCoreXH ha u, pureLastCoreYH u,
    pureLastCoreXZ ha v, pureLastCoreYZ v, pureLastCoreZZ v} ∪
    (if 0 < v then {pureLastCoreZH u} else ∅)

def pureDominantLastCoreBorderNat (u v x y z : ℕ) : Prop :=
  (x = 1 ∧ y = u + 1 ∧ z = 0) ∨
  (x = 0 ∧ y = u + 2 ∧ z = 0) ∨
  (x = 1 ∧ y = 0 ∧ z = v + 1) ∨
  (x = 0 ∧ y = 1 ∧ z = v + 1) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 2) ∨
  (0 < v ∧ x = 0 ∧ y = u + 1 ∧ z = 1)

theorem mem_standardSet_pureDominantSoclesLastCore_iff
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) (p : Normal a b 0) :
    p ∈ standardSet (pureDominantSoclesLastCore (a := a) (b := b) u v) ↔
      dominantLastStandardNat u v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, pureDominantSoclesLastCore, pureCore, pureH, pureZ,
    Normal.exact_divides_iff, Normal.DividesCriterion,
    dominantLastStandardNat]
  omega

theorem mem_pureDominantExpectedBorderLastCore_iff
    (ha : 2 ≤ a) (m : Normal a b 0) :
    m ∈ pureDominantExpectedBorderLastCore (a := a) (b := b) ha u v ↔
      pureDominantLastCoreBorderNat u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hv : 0 < v <;>
    simp [pureDominantExpectedBorderLastCore, pureDominantLastCoreBorderNat,
      pureLastCoreXH, pureLastCoreYH, pureLastCoreZH, pureLastCoreXZ,
      pureLastCoreYZ, pureLastCoreZZ, hv, Normal.ext_iff]

set_option maxHeartbeats 6400000 in
theorem pureDominantLastCore_border_arithmetic
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u)
    (x y z : ℕ) (hxlt : x < a) :
    ((¬dominantLastStandardNat u v x y z ∧
      (if 0 < x then dominantLastStandardNat u v (x - 1) y z
       else if b ≤ y ∧ 0 ≤ z then
         dominantLastStandardNat u v (a - 1) (y - b) (z - 0)
       else True) ∧
      (0 < y → dominantLastStandardNat u v x (y - 1) z) ∧
      (0 < z → dominantLastStandardNat u v x y (z - 1))) ↔
      pureDominantLastCoreBorderNat u v x y z) := by
  by_cases hx : 0 < x <;> by_cases hby : b ≤ y <;> by_cases hv0 : 0 < v
  all_goals
    simp [hx, hby, hv0, dominantLastStandardNat,
      pureDominantLastCoreBorderNat] <;> grind (splits := 32)

theorem pureDominantBorder_lastCore_exact
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) :
    borderFinset (pureDominantSoclesLastCore (a := a) (b := b) u v) =
      pureDominantExpectedBorderLastCore (a := a) (b := b) ha u v := by
  apply borderFinset_eq_expected_of_nat _ _
    (dominantLastStandardNat u v) (pureDominantLastCoreBorderNat u v)
  · simp [pureDominantSoclesLastCore]
  · intro p
    exact mem_standardSet_pureDominantSoclesLastCore_iff ha hb hu p
  · intro m
    exact mem_pureDominantExpectedBorderLastCore_iff ha m
  · exact pureDominantLastCore_border_arithmetic ha hb hu

theorem pureDominantBorder_lastCore_card
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) :
    (borderFinset
      (pureDominantSoclesLastCore (a := a) (b := b) u v)).card =
      if 0 < v then 6 else 5 := by
  rw [pureDominantBorder_lastCore_exact ha hb hu]
  let A := pureLastCoreXH (a := a) (b := b) ha u
  let B := pureLastCoreYH (a := a) (b := b) u
  let C := pureLastCoreXZ (a := a) (b := b) ha v
  let D := pureLastCoreYZ (a := a) (b := b) v
  let E := pureLastCoreZZ (a := a) (b := b) v
  let F := pureLastCoreZH (a := a) (b := b) u
  let s : Finset (Normal a b 0) := {A, B, C, D, E}
  have hA : A ∉ ({B, C, D, E} : Finset (Normal a b 0)) := by
    simp [A, B, C, D, E, pureLastCoreXH, pureLastCoreYH,
      pureLastCoreXZ, pureLastCoreYZ, pureLastCoreZZ]
  have hB : B ∉ ({C, D, E} : Finset (Normal a b 0)) := by
    simp [B, C, D, E, pureLastCoreYH, pureLastCoreXZ,
      pureLastCoreYZ, pureLastCoreZZ]
  have hC : C ∉ ({D, E} : Finset (Normal a b 0)) := by
    simp [C, D, E, pureLastCoreXZ, pureLastCoreYZ, pureLastCoreZZ]
  have hD : D ∉ ({E} : Finset (Normal a b 0)) := by
    simp [D, E, pureLastCoreYZ, pureLastCoreZZ]
  have hs : s.card = 5 := by
    dsimp [s]
    rw [Finset.card_insert_of_notMem hA, Finset.card_insert_of_notMem hB,
      Finset.card_insert_of_notMem hC, Finset.card_insert_of_notMem hD]
    simp
  by_cases hv : 0 < v
  · have hF : F ∉ s := by
      simp [F, s, A, B, C, D, E, pureLastCoreZH, pureLastCoreXH,
        pureLastCoreYH, pureLastCoreXZ, pureLastCoreYZ, pureLastCoreZZ]
      omega
    rw [ite_eq_left hv]
    simp only [pureDominantExpectedBorderLastCore, ite_eq_left hv]
    change (s ∪ {F}).card = 6
    simp [Finset.card_insert_of_notMem hF, hs]
  · simpa [pureDominantExpectedBorderLastCore, hv, s, A, B, C, D, E]
      using hs

theorem pureDominantBorder_lastCore_card_ne_four
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) :
    (borderFinset
      (pureDominantSoclesLastCore (a := a) (b := b) u v)).card ≠ 4 := by
  rw [pureDominantBorder_lastCore_card ha hb hu]
  split <;> omega

end P23.OneTie
