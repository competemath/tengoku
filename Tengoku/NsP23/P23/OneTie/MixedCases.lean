import Tengoku.NsP23.P23.OneTie.DirectionalCentre
import Tengoku.NsP23.P23.OneTie.PrincipalBorder

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 1: dominant mixed border counts

Only the dominant four-border geometry reproduced in the Run-03 command is
formalized here. No non-dominant classification or trace argument appears.
-/

namespace P23.OneTie

variable {a b c r u v : ℕ} [NeZero a]

/-- The six unordered choices of two principal-border points to adjoin.-/
inductive MixedAddedPair where
  | YZ | YP | YQ | ZP | ZQ | PQ
deriving DecidableEq, Repr

/-- A singleton included exactly when `condition` holds.-/
def singletonIf (condition : Prop) [Decidable condition]
    (m : Normal a b c) : Finset (Normal a b c) :=
  if condition then {m} else ∅

omit [NeZero a] in
/--
@isnad1 id=iff.0h6v.s6.a2ff8dc524d7 from=translated src=- shape=37ffe2a8 vocab=a5119c07
-/
theorem mem_singletonIf_iff (condition : Prop) [Decidable condition]
    (m n : Normal a b c) :
    m ∈ singletonIf condition n ↔ condition ∧ m = n := by
  by_cases h : condition <;> simp [singletonIf, h]

def singletonProofIf (condition : Prop) [Decidable condition]
    (m : condition → Normal a b c) : Finset (Normal a b c) :=
  if h : condition then {m h} else ∅

/-- Indicator arithmetic used in the displayed Run-03 count formulas.-/
def indicator (condition : Prop) [Decidable condition] : ℕ :=
  if condition then 1 else 0

omit [NeZero a] in
/--
@isnad1 id=eq.1h6v.s6.78c4ef795e48 from=translated src=- shape=6e181f4b vocab=db21b791
-/
theorem card_union_singletonProofIf (s : Finset (Normal a b c))
    (condition : Prop) [Decidable condition] (m : condition → Normal a b c)
    (hnot : ∀ h, m h ∉ s) :
    (s ∪ singletonProofIf condition m).card = s.card + indicator condition := by
  by_cases h : condition
  · simp [singletonProofIf, indicator, h, Finset.card_insert_of_notMem (hnot h)]
  · simp [singletonProofIf, indicator, h]

/-! Explicit normalized variable multiples used in the six tables. -/

def mixedYTimesY (u : ℕ) : Normal a b c :=
  ⟨0, u + 2, 0, Nat.pos_of_ne_zero (NeZero.ne a)⟩

def mixedZTimesZ (v : ℕ) : Normal a b c :=
  ⟨0, 0, v + 2, Nat.pos_of_ne_zero (NeZero.ne a)⟩

def mixedYTimesX (ha : 2 ≤ a) (u : ℕ) : Normal a b c :=
  ⟨1, u + 1, 0, by omega⟩

def mixedZTimesX (ha : 2 ≤ a) (v : ℕ) : Normal a b c :=
  ⟨1, 0, v + 1, by omega⟩

def mixedYTimesZ (u : ℕ) : Normal a b c :=
  ⟨0, u + 1, 1, Nat.pos_of_ne_zero (NeZero.ne a)⟩

def mixedZTimesY (v : ℕ) : Normal a b c :=
  ⟨0, 1, v + 1, Nat.pos_of_ne_zero (NeZero.ne a)⟩

def mixedPTimesY (r u : ℕ) (hr : r < a - 1) : Normal a b c :=
  ⟨r + 1, u + 2 - b, 0, by omega⟩

def mixedPTimesZ (r u : ℕ) (hr : r < a - 1) : Normal a b c :=
  ⟨r + 1, u + 1 - b, 1, by omega⟩

def mixedQTimesY (r v : ℕ) (hr : r < a - 1) : Normal a b c :=
  ⟨r + 1, 1, v + 1 - c, by omega⟩

def mixedQTimesZ (r v : ℕ) (hr : r < a - 1) : Normal a b c :=
  ⟨r + 1, 0, v + 2 - c, by omega⟩

def mixedPTimesX (r u : ℕ) (hh : r + 1 < a - 1) : Normal a b c :=
  ⟨r + 2, u + 1 - b, 0, by omega⟩

def mixedQTimesX (r v : ℕ) (hh : r + 1 < a - 1) : Normal a b c :=
  ⟨r + 2, 0, v + 1 - c, by omega⟩

def mixedWrappedZY (u : ℕ) : Normal a b 1 :=
  ⟨a - 1, u + 1 - b, 0, by
    have ha0 := Nat.pos_of_ne_zero (NeZero.ne a)
    omega⟩

/-- At `c = 1`, the x-predecessor of `zY` is the wrapped endpoint
`(a-1,u+1-b,0)`. This is the load-bearing endpoint in the `Y,P` table.
@isnad1 id=eq.2h3v.s6.0c7ad0f05cee from=translated src=- shape=25fdf27b vocab=16b7ed0d
-/
theorem wrappedPredecessor_zY_c_eq_one
    (hb : 1 ≤ b) (hu : b ≤ u) :
    Normal.predecessor .x (mixedYTimesZ (a := a) (b := b) (c := 1) u) =
      some (mixedWrappedZY (a := a) (b := b) u) := by
  rw [Normal.predecessor_x_wrapped]
  · rfl
  · rfl
  · simp [mixedYTimesZ]
    omega
  · simp [mixedYTimesZ]

def mixedSoclesYZ (r u v : ℕ) (hr : r < a - 1) :
    Finset (Normal a b c) :=
  {mixedCore r u v (by omega), mixedY u, mixedZ v}

def mixedExpectedBorderYZ (ha : 2 ≤ a) (r u v : ℕ)
    (hr : r < a - 1) : Finset (Normal a b c) :=
  {mixedP r u hr, mixedQ r v hr, mixedYTimesY u, mixedZTimesZ v} ∪
    singletonIf (1 < r + 1) (mixedYTimesX ha u) ∪
    singletonIf (1 < r + 1) (mixedZTimesX ha v) ∪
    singletonIf (1 < c) (mixedYTimesZ u) ∪
    singletonIf (1 < b) (mixedZTimesY v)

/--
@isnad1 id=iff.5h7v.s8.b847cf1b05f3 from=translated src=- shape=25c29a62 vocab=6458f359
-/
theorem mem_standardSet_mixedSoclesYZ_iff
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hu : b ≤ u) (hv : c ≤ v)
    (hr : r < a - 1) (p : Normal a b c) :
    p ∈ standardSet (mixedSoclesYZ (a := a) (b := b) (c := c) r u v hr) ↔
      (p.y ≤ u ∧ p.z ≤ v ∧
        (p.x ≤ r ∨ (p.y + b ≤ u ∧ p.z + c ≤ v))) ∨
      (p.x = 0 ∧ p.y ≤ u + 1 ∧ p.z = 0) ∨
      (p.x = 0 ∧ p.y = 0 ∧ p.z ≤ v + 1) := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, mixedSoclesYZ, Normal.exact_divides_iff,
    Normal.DividesCriterion, mixedCore, mixedY, mixedZ]
  omega

def mixedYZStandardNat (a b c r u v x y z : ℕ) : Prop :=
  (y ≤ u ∧ z ≤ v ∧ (x ≤ r ∨ (y + b ≤ u ∧ z + c ≤ v))) ∨
  (x = 0 ∧ y ≤ u + 1 ∧ z = 0) ∨
  (x = 0 ∧ y = 0 ∧ z ≤ v + 1)

def mixedYZBorderNat (b c r u v x y z : ℕ) : Prop :=
  (x = r + 1 ∧ y = u + 1 - b ∧ z = 0) ∨
  (x = r + 1 ∧ y = 0 ∧ z = v + 1 - c) ∨
  (x = 0 ∧ y = u + 2 ∧ z = 0) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 2) ∨
  (1 < r + 1 ∧ x = 1 ∧ y = u + 1 ∧ z = 0) ∨
  (1 < r + 1 ∧ x = 1 ∧ y = 0 ∧ z = v + 1) ∨
  (1 < c ∧ x = 0 ∧ y = u + 1 ∧ z = 1) ∨
  (1 < b ∧ x = 0 ∧ y = 1 ∧ z = v + 1)

set_option maxHeartbeats 800000 in
/--
@isnad1 id=iff.2h7v.s6.6712e8757576 from=translated src=- shape=247b9f59 vocab=9dd71c74
-/
theorem mem_mixedExpectedBorderYZ_iff
    (ha : 2 ≤ a) (r u v : ℕ) (hr : r < a - 1) (m : Normal a b c) :
    m ∈ mixedExpectedBorderYZ (a := a) (b := b) (c := c) ha r u v hr ↔
      mixedYZBorderNat b c r u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  simp only [mixedExpectedBorderYZ, Finset.mem_union, Finset.mem_insert,
    Finset.mem_singleton, mem_singletonIf_iff, mixedP, mixedQ,
    mixedYTimesY, mixedZTimesZ, mixedYTimesX, mixedZTimesX,
    mixedYTimesZ, mixedZTimesY]
  simp only [Normal.mk.injEq]
  simpa only [mixedYZBorderNat, or_assoc]

set_option maxHeartbeats 6400000 in
/--
@isnad1 id=iff.7h9v.s8.190aa8c28acd from=translated src=- shape=184bbc15 vocab=45587deb
-/
theorem mixedYZ_border_arithmetic
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1)
    (x y z : ℕ) (hxlt : x < a) :
    (¬mixedYZStandardNat a b c r u v x y z ∧
      (if 0 < x then mixedYZStandardNat a b c r u v (x - 1) y z
       else if b ≤ y ∧ c ≤ z then
         mixedYZStandardNat a b c r u v (a - 1) (y - b) (z - c)
       else True) ∧
      (0 < y → mixedYZStandardNat a b c r u v x (y - 1) z) ∧
      (0 < z → mixedYZStandardNat a b c r u v x y (z - 1))) ↔
      mixedYZBorderNat b c r u v x y z := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y
    · by_cases hz : 0 < z
      · simp [hx, hy, hz, mixedYZStandardNat, mixedYZBorderNat]
        grind (splits := 32)
      · simp [hx, hy, hz, mixedYZStandardNat, mixedYZBorderNat]
        grind (splits := 32)
    · by_cases hz : 0 < z
      · simp [hx, hy, hz, mixedYZStandardNat, mixedYZBorderNat]
        grind (splits := 32)
      · simp [hx, hy, hz, mixedYZStandardNat, mixedYZBorderNat]
        grind (splits := 32)
  · have hx0 : x = 0 := by omega
    by_cases hby : b ≤ y
    · by_cases hcz : c ≤ z
      · by_cases hy : 0 < y <;> by_cases hz : 0 < z
        all_goals
          simp [hx, hx0, hby, hcz, hy, hz, mixedYZStandardNat,
            mixedYZBorderNat] <;> omega
      · by_cases hy : 0 < y <;> by_cases hz : 0 < z
        all_goals
          simp [hx, hx0, hby, hcz, hy, hz, mixedYZStandardNat,
            mixedYZBorderNat] <;> omega
    · by_cases hy : 0 < y <;> by_cases hz : 0 < z
      all_goals
        simp [hx, hx0, hby, hy, hz, mixedYZStandardNat,
          mixedYZBorderNat] <;> omega

/--
@isnad1 id=eq.6h6v.s6.4529a97ecc38 from=translated src=- shape=c7b7e3fc vocab=2c93cfcf
-/
theorem mixedBorderYZ_exact
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    borderFinset (mixedSoclesYZ (a := a) (b := b) (c := c) r u v hr) =
      mixedExpectedBorderYZ (a := a) (b := b) (c := c) ha r u v hr := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp [mixedSoclesYZ])]
  rw [mem_mixedExpectedBorderYZ_iff ha r u v hr]
  rcases m with ⟨mx, my, mz, hmx⟩
  have harith := mixedYZ_border_arithmetic ha hb hc hu hv hr mx my mz hmx
  by_cases hx : 0 < mx
  · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
      mem_standardSet_mixedSoclesYZ_iff hb hc hu hv hr,
      mixedYZStandardNat, Normal.predecessor, Normal.xPredecessor,
      Normal.yPredecessor, Normal.zPredecessor, hx] using harith
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · by_cases hcz : c ≤ mz
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_mixedSoclesYZ_iff hb hc hu hv hr,
          mixedYZStandardNat, Normal.predecessor, Normal.wrappedXPredecessor,
          Normal.yPredecessor, Normal.zPredecessor, hx, hx0, hby, hcz]
          using harith
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_mixedSoclesYZ_iff hb hc hu hv hr,
          mixedYZStandardNat, Normal.predecessor, Normal.yPredecessor,
          Normal.zPredecessor, hx, hx0, hby, hcz] using harith
    · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
        mem_standardSet_mixedSoclesYZ_iff hb hc hu hv hr,
        mixedYZStandardNat, Normal.predecessor, Normal.yPredecessor,
        Normal.zPredecessor, hx, hx0, hby] using harith

omit [NeZero a] in
/--
@isnad1 id=eq.1h6v.s6.72188951b0ea from=translated src=- shape=12d98611 vocab=0a0d5556
-/
theorem card_union_singletonIf (s : Finset (Normal a b c))
    (condition : Prop) [Decidable condition] (m : Normal a b c)
    (hnot : condition → m ∉ s) :
    (s ∪ singletonIf condition m).card = s.card + indicator condition := by
  by_cases h : condition
  · simp [singletonIf, indicator, h, Finset.card_insert_of_notMem (hnot h)]
  · simp [singletonIf, indicator, h]

/--
@isnad1 id=eq.6h6v.s7.07151086f712 from=translated src=- shape=a25bab2e vocab=d9535a54
-/
theorem mixedBorderYZ_card
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    (borderFinset
      (mixedSoclesYZ (a := a) (b := b) (c := c) r u v hr)).card =
      4 + 2 * indicator (1 < r + 1) + indicator (1 < b) +
        indicator (1 < c) := by
  rw [mixedBorderYZ_exact ha hb hc hu hv hr]
  let s0 : Finset (Normal a b c) :=
    {mixedP r u hr, mixedQ r v hr, mixedYTimesY u, mixedZTimesZ v}
  let s1 := s0 ∪ singletonIf (1 < r + 1) (mixedYTimesX ha u)
  let s2 := s1 ∪ singletonIf (1 < r + 1) (mixedZTimesX ha v)
  let s3 := s2 ∪ singletonIf (1 < c) (mixedYTimesZ u)
  have hP : mixedP (a := a) (b := b) (c := c) r u hr ∉
      ({mixedQ (a := a) (b := b) (c := c) r v hr,
        mixedYTimesY (a := a) (b := b) (c := c) u,
        mixedZTimesZ (a := a) (b := b) (c := c) v} :
        Finset (Normal a b c)) := by
    simp [mixedP, mixedQ, mixedYTimesY, mixedZTimesZ]
    omega
  have hQ : mixedQ (a := a) (b := b) (c := c) r v hr ∉
      ({mixedYTimesY (a := a) (b := b) (c := c) u,
        mixedZTimesZ (a := a) (b := b) (c := c) v} :
        Finset (Normal a b c)) := by
    simp [mixedQ, mixedYTimesY, mixedZTimesZ]
  have hYY : mixedYTimesY (a := a) (b := b) (c := c) u ∉
      ({mixedZTimesZ (a := a) (b := b) (c := c) v} :
        Finset (Normal a b c)) := by
    simp [mixedYTimesY, mixedZTimesZ]
  have hs0 : s0.card = 4 := by
    dsimp [s0]
    rw [Finset.card_insert_of_notMem hP]
    rw [Finset.card_insert_of_notMem hQ]
    rw [Finset.card_insert_of_notMem hYY]
    simp
  have hxY : 1 < r + 1 → mixedYTimesX (a := a) (b := b) (c := c) ha u ∉ s0 := by
    intro hh
    simp [s0, mixedP, mixedQ, mixedYTimesY, mixedZTimesZ, mixedYTimesX]
    omega
  have hs1 : s1.card = s0.card + indicator (1 < r + 1) := by
    exact card_union_singletonIf s0 _ _ hxY
  have hxZ : 1 < r + 1 → mixedZTimesX (a := a) (b := b) (c := c) ha v ∉ s1 := by
    intro hh
    simp [s1, s0, singletonIf, hh, mixedP, mixedQ, mixedYTimesY,
      mixedZTimesZ, mixedYTimesX, mixedZTimesX]
    omega
  have hs2 : s2.card = s1.card + indicator (1 < r + 1) := by
    exact card_union_singletonIf s1 _ _ hxZ
  have hzY : 1 < c → mixedYTimesZ (a := a) (b := b) (c := c) u ∉ s2 := by
    intro hc1
    simp [s2, s1, s0, singletonIf, mixedP, mixedQ, mixedYTimesY,
      mixedZTimesZ, mixedYTimesX, mixedZTimesX, mixedYTimesZ]
    split_ifs <;> simp_all <;> omega
  have hs3 : s3.card = s2.card + indicator (1 < c) := by
    exact card_union_singletonIf s2 _ _ hzY
  have hyZ : 1 < b → mixedZTimesY (a := a) (b := b) (c := c) v ∉ s3 := by
    intro hb1
    simp [s3, s2, s1, s0, singletonIf, mixedP, mixedQ, mixedYTimesY,
      mixedZTimesZ, mixedYTimesX, mixedZTimesX, mixedYTimesZ,
      mixedZTimesY]
    split_ifs <;> simp_all <;> omega
  have hs4 := card_union_singletonIf s3 (1 < b)
    (mixedZTimesY (a := a) (b := b) (c := c) v) hyZ
  change (s3 ∪ singletonIf (1 < b) (mixedZTimesY v)).card = _
  rw [hs4, hs3, hs2, hs1, hs0]
  omega

/-! ## The `Y,P` choice -/

def mixedSoclesYP (r u v : ℕ) (hr : r < a - 1) :
    Finset (Normal a b c) :=
  {mixedCore r u v (by omega), mixedY u, mixedP r u hr}

def mixedYPBase (r u v : ℕ) (hr : r < a - 1) :
    Finset (Normal a b c) :=
  {mixedZ v, mixedQ r v hr, mixedYTimesY u} ∪
    (if hh : r + 1 < a - 1 then {mixedPTimesX r u hh}
     else {mixedYTimesZ u})

def mixedExpectedBorderYP (ha : 2 ≤ a) (r u v : ℕ)
    (hr : r < a - 1) : Finset (Normal a b c) :=
  mixedYPBase r u v hr ∪
    singletonIf (1 < r + 1) (mixedYTimesX ha u) ∪
    singletonIf (1 < b ∨ r + 1 = 1) (mixedPTimesY r u hr) ∪
    singletonIf (c < v) (mixedPTimesZ r u hr) ∪
    singletonIf (1 < c ∧ r + 1 < a - 1) (mixedYTimesZ u)

def mixedYPStandardNat (b c r u v x y z : ℕ) : Prop :=
  (y ≤ u ∧ z ≤ v ∧ (x ≤ r ∨ (y + b ≤ u ∧ z + c ≤ v))) ∨
  (x = 0 ∧ y ≤ u + 1 ∧ z = 0) ∨
  (x ≤ r + 1 ∧ y ≤ u + 1 - b ∧ z = 0)

def mixedYPBorderNat (a b c r u v x y z : ℕ) : Prop :=
  (x = 0 ∧ y = 0 ∧ z = v + 1) ∨
  (x = r + 1 ∧ y = 0 ∧ z = v + 1 - c) ∨
  (x = 0 ∧ y = u + 2 ∧ z = 0) ∨
  ((r + 1 < a - 1 ∧ x = r + 2 ∧ y = u + 1 - b ∧ z = 0) ∨
   (¬r + 1 < a - 1 ∧ x = 0 ∧ y = u + 1 ∧ z = 1)) ∨
  (1 < r + 1 ∧ x = 1 ∧ y = u + 1 ∧ z = 0) ∨
  ((1 < b ∨ r + 1 = 1) ∧ x = r + 1 ∧ y = u + 2 - b ∧ z = 0) ∨
  (c < v ∧ x = r + 1 ∧ y = u + 1 - b ∧ z = 1) ∨
  (1 < c ∧ r + 1 < a - 1 ∧ x = 0 ∧ y = u + 1 ∧ z = 1)

/--
@isnad1 id=iff.5h7v.s6.a0c3bcd6c056 from=translated src=- shape=37667727 vocab=acf0fcec
-/
theorem mem_standardSet_mixedSoclesYP_iff
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hu : b ≤ u) (hv : c ≤ v)
    (hr : r < a - 1) (p : Normal a b c) :
    p ∈ standardSet (mixedSoclesYP (a := a) (b := b) (c := c) r u v hr) ↔
      mixedYPStandardNat b c r u v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, mixedSoclesYP, Normal.exact_divides_iff,
    Normal.DividesCriterion, mixedCore, mixedY, mixedP, mixedYPStandardNat]
  omega

set_option maxHeartbeats 1000000 in
/--
@isnad1 id=iff.2h7v.s6.8d502bbb8318 from=translated src=- shape=64ca5167 vocab=b1a6c005
-/
theorem mem_mixedExpectedBorderYP_iff
    (ha : 2 ≤ a) (r u v : ℕ) (hr : r < a - 1) (m : Normal a b c) :
    m ∈ mixedExpectedBorderYP (a := a) (b := b) (c := c) ha r u v hr ↔
      mixedYPBorderNat a b c r u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hh : r + 1 < a - 1
  · simp only [mixedExpectedBorderYP, mixedYPBase, hh, dite_true, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, mem_singletonIf_iff,
      mixedZ, mixedQ, mixedYTimesY, mixedPTimesX, mixedYTimesZ,
      mixedYTimesX, mixedPTimesY, mixedPTimesZ, Normal.mk.injEq]
    simp only [mixedYPBorderNat, hh, not_true_eq_false, false_and, or_false,
      true_and, and_true, and_assoc, or_assoc]
  · simp only [mixedExpectedBorderYP, mixedYPBase, hh, dite_false, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton, mem_singletonIf_iff,
      mixedZ, mixedQ, mixedYTimesY, mixedPTimesX, mixedYTimesZ,
      mixedYTimesX, mixedPTimesY, mixedPTimesZ, Normal.mk.injEq]
    simp only [mixedYPBorderNat, hh, false_and, not_false_eq_true, true_and,
      and_true, and_assoc, false_or, or_false, or_assoc]

set_option maxHeartbeats 6400000 in
omit [NeZero a] in
/--
@isnad1 id=iff.7h9v.s8.b9be5978a35c from=translated src=- shape=dcc2d1fe vocab=0c5cd99b
-/
theorem mixedYP_border_arithmetic
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1)
    (x y z : ℕ) (hxlt : x < a) :
    (¬mixedYPStandardNat b c r u v x y z ∧
      (if 0 < x then mixedYPStandardNat b c r u v (x - 1) y z
       else if b ≤ y ∧ c ≤ z then
         mixedYPStandardNat b c r u v (a - 1) (y - b) (z - c)
       else True) ∧
      (0 < y → mixedYPStandardNat b c r u v x (y - 1) z) ∧
      (0 < z → mixedYPStandardNat b c r u v x y (z - 1))) ↔
      mixedYPBorderNat a b c r u v x y z := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y <;> by_cases hz : 0 < z
    all_goals
      simp [hx, hy, hz, mixedYPStandardNat, mixedYPBorderNat]
      <;> grind (splits := 40)
  · have hx0 : x = 0 := by omega
    by_cases hby : b ≤ y
    · by_cases hcz : c ≤ z
      · by_cases hy : 0 < y <;> by_cases hz : 0 < z
        all_goals
          simp [hx0, hby, hcz, hy, hz, mixedYPStandardNat,
            mixedYPBorderNat] <;> grind (splits := 40)
      · by_cases hy : 0 < y <;> by_cases hz : 0 < z
        all_goals
          simp [hx0, hby, hcz, hy, hz, mixedYPStandardNat,
            mixedYPBorderNat] <;> grind (splits := 40)
    · by_cases hy : 0 < y <;> by_cases hz : 0 < z
      all_goals
        simp [hx0, hby, hy, hz, mixedYPStandardNat, mixedYPBorderNat]
        <;> grind (splits := 40)

/--
@isnad1 id=eq.6h6v.s6.113136e89243 from=translated src=- shape=c7b7e3fc vocab=be024e67
-/
theorem mixedBorderYP_exact
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    borderFinset (mixedSoclesYP (a := a) (b := b) (c := c) r u v hr) =
      mixedExpectedBorderYP (a := a) (b := b) (c := c) ha r u v hr := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp [mixedSoclesYP])]
  rw [mem_mixedExpectedBorderYP_iff ha r u v hr]
  rcases m with ⟨mx, my, mz, hmx⟩
  have harith := mixedYP_border_arithmetic ha hb hc hu hv hr mx my mz hmx
  by_cases hx : 0 < mx
  · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
      mem_standardSet_mixedSoclesYP_iff hb hc hu hv hr,
      mixedYPStandardNat, Normal.predecessor, Normal.xPredecessor,
      Normal.yPredecessor, Normal.zPredecessor, hx] using harith
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · by_cases hcz : c ≤ mz
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_mixedSoclesYP_iff hb hc hu hv hr,
          mixedYPStandardNat, Normal.predecessor, Normal.wrappedXPredecessor,
          Normal.yPredecessor, Normal.zPredecessor, hx, hx0, hby, hcz]
          using harith
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_mixedSoclesYP_iff hb hc hu hv hr,
          mixedYPStandardNat, Normal.predecessor, Normal.yPredecessor,
          Normal.zPredecessor, hx, hx0, hby, hcz] using harith
    · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
        mem_standardSet_mixedSoclesYP_iff hb hc hu hv hr,
        mixedYPStandardNat, Normal.predecessor, Normal.yPredecessor,
        Normal.zPredecessor, hx, hx0, hby] using harith

set_option maxHeartbeats 6400000 in
/--
@isnad1 id=eq.6h6v.s8.d6e2f0734db2 from=translated src=- shape=2bd1c1ee vocab=48b4030e
-/
theorem mixedBorderYP_card
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    (borderFinset
      (mixedSoclesYP (a := a) (b := b) (c := c) r u v hr)).card =
      4 + indicator (1 < r + 1) + indicator (1 < b ∨ r + 1 = 1) +
        indicator (c < v) + indicator (1 < c ∧ r + 1 < a - 1) := by
  rw [mixedBorderYP_exact ha hb hc hu hv hr]
  let s0 := mixedYPBase (a := a) (b := b) (c := c) r u v hr
  let s1 := s0 ∪ singletonIf (1 < r + 1) (mixedYTimesX ha u)
  let s2 := s1 ∪ singletonIf (1 < b ∨ r + 1 = 1) (mixedPTimesY r u hr)
  let s3 := s2 ∪ singletonIf (c < v) (mixedPTimesZ r u hr)
  have hs0 : s0.card = 4 := by
    dsimp [s0]
    by_cases hh : r + 1 < a - 1
    · simp [mixedYPBase, hh, mixedZ, mixedQ, mixedYTimesY, mixedPTimesX]
    · simp [mixedYPBase, hh, mixedZ, mixedQ, mixedYTimesY, mixedYTimesZ]
  have hxY : 1 < r + 1 → mixedYTimesX (a := a) (b := b) (c := c) ha u ∉ s0 := by
    intro h
    simp [s0, mixedYPBase, mixedZ, mixedQ, mixedYTimesY, mixedPTimesX,
      mixedYTimesZ, mixedYTimesX]
    split_ifs <;> simp_all <;> omega
  have hs1 : s1.card = s0.card + indicator (1 < r + 1) :=
    card_union_singletonIf s0 _ _ hxY
  have hyP : (1 < b ∨ r + 1 = 1) →
      mixedPTimesY (a := a) (b := b) (c := c) r u hr ∉ s1 := by
    intro h
    simp [s1, s0, mixedYPBase, singletonIf, mixedZ, mixedQ,
      mixedYTimesY, mixedPTimesX, mixedYTimesZ, mixedYTimesX,
      mixedPTimesY]
    split_ifs <;> simp_all <;> omega
  have hs2 : s2.card = s1.card + indicator (1 < b ∨ r + 1 = 1) :=
    card_union_singletonIf s1 _ _ hyP
  have hzP : c < v → mixedPTimesZ (a := a) (b := b) (c := c) r u hr ∉ s2 := by
    intro h
    simp [s2, s1, s0, mixedYPBase, singletonIf, mixedZ, mixedQ,
      mixedYTimesY, mixedPTimesX, mixedYTimesZ, mixedYTimesX,
      mixedPTimesY, mixedPTimesZ]
    split_ifs <;> simp_all <;> omega
  have hs3 : s3.card = s2.card + indicator (c < v) :=
    card_union_singletonIf s2 _ _ hzP
  have hzY : (1 < c ∧ r + 1 < a - 1) →
      mixedYTimesZ (a := a) (b := b) (c := c) u ∉ s3 := by
    intro h
    simp [s3, s2, s1, s0, mixedYPBase, singletonIf, mixedZ, mixedQ,
      mixedYTimesY, mixedPTimesX, mixedYTimesZ, mixedYTimesX,
      mixedPTimesY, mixedPTimesZ]
    split_ifs <;> simp_all <;> omega
  have hs4 := card_union_singletonIf s3 (1 < c ∧ r + 1 < a - 1)
    (mixedYTimesZ (a := a) (b := b) (c := c) u) hzY
  change (s3 ∪ singletonIf (1 < c ∧ r + 1 < a - 1)
    (mixedYTimesZ u)).card = _
  rw [hs4, hs3, hs2, hs1, hs0]

/-! ## The `Y,Q` choice -/

def mixedSoclesYQ (r u v : ℕ) (hr : r < a - 1) : Finset (Normal a b c) :=
  {mixedCore r u v (by omega), mixedY u, mixedQ r v hr}

def mixedExpectedBorderYQ (ha : 2 ≤ a) (r u v : ℕ)
    (hr : r < a - 1) : Finset (Normal a b c) :=
  {mixedZ v, mixedP r u hr, mixedYTimesY u} ∪
    singletonIf (1 < r + 1) (mixedYTimesX ha u) ∪
    singletonIf (1 < c) (mixedYTimesZ u) ∪
    singletonIf (1 < c) (mixedQTimesZ r v hr) ∪
    singletonProofIf (r + 1 < a - 1) (mixedQTimesX r v) ∪
    singletonIf (b < u) (mixedQTimesY r v hr)

def mixedYQStandardNat (b c r u v x y z : ℕ) : Prop :=
  (y ≤ u ∧ z ≤ v ∧ (x ≤ r ∨ (y + b ≤ u ∧ z + c ≤ v))) ∨
  (x = 0 ∧ y ≤ u + 1 ∧ z = 0) ∨
  (x ≤ r + 1 ∧ y = 0 ∧ z ≤ v + 1 - c)

def mixedYQBorderNat (a b c r u v x y z : ℕ) : Prop :=
  (x = 0 ∧ y = 0 ∧ z = v + 1) ∨
  (x = r + 1 ∧ y = u + 1 - b ∧ z = 0) ∨
  (x = 0 ∧ y = u + 2 ∧ z = 0) ∨
  (1 < r + 1 ∧ x = 1 ∧ y = u + 1 ∧ z = 0) ∨
  (1 < c ∧ x = 0 ∧ y = u + 1 ∧ z = 1) ∨
  (1 < c ∧ x = r + 1 ∧ y = 0 ∧ z = v + 2 - c) ∨
  (r + 1 < a - 1 ∧ x = r + 2 ∧ y = 0 ∧ z = v + 1 - c) ∨
  (b < u ∧ x = r + 1 ∧ y = 1 ∧ z = v + 1 - c)

/--
@isnad1 id=iff.5h7v.s6.1f4c7656f38a from=translated src=- shape=37667727 vocab=8162aa6a
-/
theorem mem_standardSet_mixedSoclesYQ_iff
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hu : b ≤ u) (hv : c ≤ v)
    (hr : r < a - 1) (p : Normal a b c) :
    p ∈ standardSet (mixedSoclesYQ (a := a) (b := b) (c := c) r u v hr) ↔
      mixedYQStandardNat b c r u v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, mixedSoclesYQ, Normal.exact_divides_iff,
    Normal.DividesCriterion, mixedCore, mixedY, mixedQ, mixedYQStandardNat]
  omega

set_option maxHeartbeats 1000000 in
/--
@isnad1 id=iff.2h7v.s6.9a849a683dca from=translated src=- shape=64ca5167 vocab=d02bfaea
-/
theorem mem_mixedExpectedBorderYQ_iff
    (ha : 2 ≤ a) (r u v : ℕ) (hr : r < a - 1) (m : Normal a b c) :
    m ∈ mixedExpectedBorderYQ (a := a) (b := b) (c := c) ha r u v hr ↔
      mixedYQBorderNat a b c r u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hh : r + 1 < a - 1
  · simp only [mixedExpectedBorderYQ, singletonProofIf, hh, dite_true, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton,
      mem_singletonIf_iff, mixedZ, mixedP, mixedYTimesY, mixedYTimesX,
      mixedYTimesZ, mixedQTimesZ, mixedQTimesX, mixedQTimesY,
      Normal.mk.injEq]
    simp only [mixedYQBorderNat, hh, true_and, or_assoc]
  · simp only [mixedExpectedBorderYQ, singletonProofIf, hh, dite_false, Finset.mem_union,
      Finset.mem_insert, Finset.mem_singleton,
      mem_singletonIf_iff, mixedZ, mixedP, mixedYTimesY, mixedYTimesX,
      mixedYTimesZ, mixedQTimesZ, mixedQTimesX, mixedQTimesY,
      Normal.mk.injEq]
    simp [mixedYQBorderNat, hh, or_assoc]

set_option maxHeartbeats 6400000 in
omit [NeZero a] in
/--
@isnad1 id=iff.7h9v.s8.82705dea2ee6 from=translated src=- shape=dcc2d1fe vocab=6d3c76a9
-/
theorem mixedYQ_border_arithmetic
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1)
    (x y z : ℕ) (hxlt : x < a) :
    (¬mixedYQStandardNat b c r u v x y z ∧
      (if 0 < x then mixedYQStandardNat b c r u v (x - 1) y z
       else if b ≤ y ∧ c ≤ z then
         mixedYQStandardNat b c r u v (a - 1) (y - b) (z - c)
       else True) ∧
      (0 < y → mixedYQStandardNat b c r u v x (y - 1) z) ∧
      (0 < z → mixedYQStandardNat b c r u v x y (z - 1))) ↔
      mixedYQBorderNat a b c r u v x y z := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y <;> by_cases hz : 0 < z
    all_goals
      simp [hx, hy, hz, mixedYQStandardNat, mixedYQBorderNat]
      <;> grind (splits := 40)
  · have hx0 : x = 0 := by omega
    by_cases hby : b ≤ y
    · by_cases hcz : c ≤ z
      · by_cases hy : 0 < y <;> by_cases hz : 0 < z
        all_goals
          simp [hx0, hby, hcz, hy, hz, mixedYQStandardNat,
            mixedYQBorderNat] <;> grind (splits := 40)
      · by_cases hy : 0 < y <;> by_cases hz : 0 < z
        all_goals
          simp [hx0, hby, hcz, hy, hz, mixedYQStandardNat,
            mixedYQBorderNat] <;> grind (splits := 40)
    · by_cases hy : 0 < y <;> by_cases hz : 0 < z
      all_goals
        simp [hx0, hby, hy, hz, mixedYQStandardNat, mixedYQBorderNat]
        <;> grind (splits := 40)

/--
@isnad1 id=eq.6h6v.s6.a6b4ecf681cd from=translated src=- shape=c7b7e3fc vocab=776934e4
-/
theorem mixedBorderYQ_exact
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    borderFinset (mixedSoclesYQ (a := a) (b := b) (c := c) r u v hr) =
      mixedExpectedBorderYQ (a := a) (b := b) (c := c) ha r u v hr := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp [mixedSoclesYQ])]
  rw [mem_mixedExpectedBorderYQ_iff ha r u v hr]
  rcases m with ⟨mx, my, mz, hmx⟩
  have harith := mixedYQ_border_arithmetic ha hb hc hu hv hr mx my mz hmx
  by_cases hx : 0 < mx
  · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
      mem_standardSet_mixedSoclesYQ_iff hb hc hu hv hr,
      mixedYQStandardNat, Normal.predecessor, Normal.xPredecessor,
      Normal.yPredecessor, Normal.zPredecessor, hx] using harith
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · by_cases hcz : c ≤ mz
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_mixedSoclesYQ_iff hb hc hu hv hr,
          mixedYQStandardNat, Normal.predecessor, Normal.wrappedXPredecessor,
          Normal.yPredecessor, Normal.zPredecessor, hx, hx0, hby, hcz]
          using harith
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_mixedSoclesYQ_iff hb hc hu hv hr,
          mixedYQStandardNat, Normal.predecessor, Normal.yPredecessor,
          Normal.zPredecessor, hx, hx0, hby, hcz] using harith
    · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
        mem_standardSet_mixedSoclesYQ_iff hb hc hu hv hr,
        mixedYQStandardNat, Normal.predecessor, Normal.yPredecessor,
        Normal.zPredecessor, hx, hx0, hby] using harith

set_option maxHeartbeats 6400000 in
set_option maxRecDepth 8192 in
/--
@isnad1 id=eq.6h6v.s8.bd13b9d3da8c from=translated src=- shape=47caa6d6 vocab=e893d31b
-/
theorem mixedBorderYQ_card
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    (borderFinset
      (mixedSoclesYQ (a := a) (b := b) (c := c) r u v hr)).card =
      3 + indicator (1 < r + 1) + indicator (r + 1 < a - 1) +
        2 * indicator (1 < c) + indicator (b < u) := by
  rw [mixedBorderYQ_exact ha hb hc hu hv hr]
  let s0 : Finset (Normal a b c) := {mixedZ v, mixedP r u hr, mixedYTimesY u}
  let s1 := s0 ∪ singletonIf (1 < r + 1) (mixedYTimesX ha u)
  let s2 := s1 ∪ singletonIf (1 < c) (mixedYTimesZ u)
  let s3 := s2 ∪ singletonIf (1 < c) (mixedQTimesZ r v hr)
  let s4 := s3 ∪ singletonProofIf (r + 1 < a - 1) (mixedQTimesX r v)
  have hs0 : s0.card = 3 := by
    simp [s0, mixedZ, mixedP, mixedYTimesY]
  have h1 : 1 < r + 1 → mixedYTimesX (a := a) (b := b) (c := c) ha u ∉ s0 := by
    intro h; simp [s0, mixedZ, mixedP, mixedYTimesY, mixedYTimesX]; omega
  have hs1 : s1.card = s0.card + indicator (1 < r + 1) :=
    card_union_singletonIf s0 _ _ h1
  have h2 : 1 < c → mixedYTimesZ (a := a) (b := b) (c := c) u ∉ s1 := by
    intro h; simp [s1, s0, singletonIf, mixedZ, mixedP, mixedYTimesY,
      mixedYTimesX, mixedYTimesZ]; split_ifs <;> simp_all <;> omega
  have hs2 : s2.card = s1.card + indicator (1 < c) :=
    card_union_singletonIf s1 _ _ h2
  have h3 : 1 < c → mixedQTimesZ (a := a) (b := b) (c := c) r v hr ∉ s2 := by
    intro h; simp [s2, s1, s0, singletonIf, mixedZ, mixedP, mixedYTimesY,
      mixedYTimesX, mixedYTimesZ, mixedQTimesZ]
    split_ifs <;> simp_all <;> omega
  have hs3 : s3.card = s2.card + indicator (1 < c) :=
    card_union_singletonIf s2 _ _ h3
  have h4 : ∀ hh : r + 1 < a - 1,
      mixedQTimesX (a := a) (b := b) (c := c) r v hh ∉ s3 := by
    intro hh; simp [s3, s2, s1, s0, singletonIf, mixedZ, mixedP,
      mixedYTimesY, mixedYTimesX, mixedYTimesZ, mixedQTimesZ,
      mixedQTimesX]
    split_ifs <;> simp_all <;> omega
  have hs4 : s4.card = s3.card + indicator (r + 1 < a - 1) :=
    card_union_singletonProofIf s3 _ _ h4
  have h5s3 : b < u →
      mixedQTimesY (a := a) (b := b) (c := c) r v hr ∉ s3 := by
    intro h
    have hn0 : mixedQTimesY (a := a) (b := b) (c := c) r v hr ∉ s0 := by
      simp [s0, mixedZ, mixedP, mixedYTimesY, mixedQTimesY]
      omega
    have hn1 : mixedQTimesY (a := a) (b := b) (c := c) r v hr ∉ s1 := by
      rw [show s1 = s0 ∪ singletonIf (1 < r + 1) (mixedYTimesX ha u) by rfl]
      simp only [Finset.mem_union, not_or]
      refine ⟨hn0, ?_⟩
      by_cases hcond : 1 < r + 1
      · simp [singletonIf, hcond, mixedYTimesX, mixedQTimesY]
        omega
      · simp [singletonIf, hcond]
    have hn2 : mixedQTimesY (a := a) (b := b) (c := c) r v hr ∉ s2 := by
      rw [show s2 = s1 ∪ singletonIf (1 < c) (mixedYTimesZ u) by rfl]
      simp only [Finset.mem_union, not_or]
      refine ⟨hn1, ?_⟩
      by_cases hcond : 1 < c
      · simp [singletonIf, hcond, mixedYTimesZ, mixedQTimesY]
      · simp [singletonIf, hcond]
    rw [show s3 = s2 ∪ singletonIf (1 < c) (mixedQTimesZ r v hr) by rfl]
    simp only [Finset.mem_union, not_or]
    refine ⟨hn2, ?_⟩
    by_cases hcond : 1 < c
    · simp [singletonIf, hcond, mixedQTimesZ, mixedQTimesY]
    · simp [singletonIf, hcond]
  have h5 : b < u → mixedQTimesY (a := a) (b := b) (c := c) r v hr ∉ s4 := by
    intro h
    have hs := h5s3 h
    by_cases hh : r + 1 < a - 1
    · rw [show s4 = s3 ∪ singletonProofIf (r + 1 < a - 1)
        (mixedQTimesX r v) by rfl]
      simp only [Finset.mem_union, not_or]
      refine ⟨hs, ?_⟩
      simp [singletonProofIf, hh, mixedQTimesX, mixedQTimesY]
    · rw [show s4 = s3 ∪ singletonProofIf (r + 1 < a - 1)
        (mixedQTimesX r v) by rfl]
      simp [singletonProofIf, hh, hs]
  have hs5 := card_union_singletonIf s4 (b < u)
    (mixedQTimesY (a := a) (b := b) (c := c) r v hr) h5
  change (s4 ∪ singletonIf (b < u) (mixedQTimesY r v hr)).card = _
  rw [hs5, hs4, hs3, hs2, hs1, hs0]
  by_cases hR : 1 < r + 1
  all_goals by_cases hh : r + 1 < a - 1
  all_goals by_cases hc1 : 1 < c
  all_goals by_cases hbu : b < u
  all_goals simp [indicator, hR, hh, hc1, hbu] <;> omega

/-! ## Exact y/z reflection -/

def swapYZ (m : Normal a b c) : Normal a c b :=
  ⟨m.x, m.z, m.y, m.x_lt⟩

/--
@isnad1 id=eq.0h4v.s5.d4a87d204cce from=translated src=- shape=157cc812 vocab=db6d00a0
-/
@[simp] theorem swapYZ_x (m : Normal a b c) : (swapYZ m).x = m.x := rfl
/--
@isnad1 id=eq.0h4v.s5.c78ceeb10059 from=translated src=- shape=96cdfdbd vocab=3cfd21c6
-/
@[simp] theorem swapYZ_y (m : Normal a b c) : (swapYZ m).y = m.z := rfl
/--
@isnad1 id=eq.0h4v.s5.8518be0d5894 from=translated src=- shape=96cdfdbd vocab=3cfd21c6
-/
@[simp] theorem swapYZ_z (m : Normal a b c) : (swapYZ m).z = m.y := rfl

/--
@isnad1 id=eq.0h4v.s5.71ad0033555f from=translated src=- shape=266dc1bb vocab=9afe88cd
-/
@[simp] theorem swapYZ_swapYZ (m : Normal a b c) : swapYZ (swapYZ m) = m := by
  cases m
  rfl

def swapYZEmbedding : Normal a b c ↪ Normal a c b where
  toFun := swapYZ
  inj' := by
    intro p q h
    have := congrArg swapYZ h
    simpa using this

def swapYZFinset (S : Finset (Normal a b c)) : Finset (Normal a c b) :=
  S.map swapYZEmbedding

/--
@isnad1 id=iff.0h5v.s5.a44f10ee2663 from=translated src=- shape=33c1a0ee vocab=f1adeb40
-/
theorem swapYZ_divides_iff (p q : Normal a b c) :
    swapYZ p ∣ swapYZ q ↔ p ∣ q := by
  simp [Normal.exact_divides_iff, Normal.DividesCriterion, swapYZ]
  tauto

/--
@isnad1 id=iff.0h5v.s6.c0d3fabe6b71 from=translated src=- shape=4dae1289 vocab=2cae8ec7
-/
theorem mem_standardSet_swapYZFinset_iff (S : Finset (Normal a b c))
    (p : Normal a b c) :
    swapYZ p ∈ standardSet (swapYZFinset S) ↔ p ∈ standardSet S := by
  constructor
  · rintro ⟨q, hq, hdiv⟩
    simp [swapYZFinset] at hq
    rcases hq with ⟨s, hs, rfl⟩
    exact ⟨s, hs, (swapYZ_divides_iff p s).mp hdiv⟩
  · rintro ⟨s, hs, hdiv⟩
    refine ⟨swapYZ s, ?_, (swapYZ_divides_iff p s).mpr hdiv⟩
    exact Finset.mem_map.mpr ⟨s, hs, rfl⟩

/--
@isnad1 id=eq.0h4v.s5.903afc651810 from=translated src=- shape=789486e4 vocab=3de36c0a
-/
theorem swapYZ_predecessor_x (m : Normal a b c) :
    Normal.predecessor .x (swapYZ m) =
      Option.map swapYZ (Normal.predecessor .x m) := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hx : 0 < mx
  · simp [Normal.predecessor, hx, Normal.xPredecessor, swapYZ]
  · have hx0 : mx = 0 := by omega
    by_cases hw : b ≤ my ∧ c ≤ mz
    · have hws : c ≤ mz ∧ b ≤ my := ⟨hw.2, hw.1⟩
      simp [Normal.predecessor, hx, hw, hws, Normal.wrappedXPredecessor,
        swapYZ]
    · have hws : ¬(c ≤ mz ∧ b ≤ my) := by tauto
      simp [Normal.predecessor, hx, hw, hws]

/--
@isnad1 id=eq.0h4v.s5.85c394ebd5c2 from=translated src=- shape=c03b9189 vocab=5ec9b696
-/
theorem swapYZ_predecessor_y (m : Normal a b c) :
    Normal.predecessor .y (swapYZ m) =
      Option.map swapYZ (Normal.predecessor .z m) := by
  rcases m with ⟨mx, my, mz, hmx⟩
  simp [Normal.predecessor, Normal.yPredecessor, Normal.zPredecessor, swapYZ]
  split_ifs <;> simp_all

/--
@isnad1 id=eq.0h4v.s5.fdb1ad011337 from=translated src=- shape=c03b9189 vocab=5ec9b696
-/
theorem swapYZ_predecessor_z (m : Normal a b c) :
    Normal.predecessor .z (swapYZ m) =
      Option.map swapYZ (Normal.predecessor .y m) := by
  rcases m with ⟨mx, my, mz, hmx⟩
  simp [Normal.predecessor, Normal.yPredecessor, Normal.zPredecessor, swapYZ]
  split_ifs <;> simp_all

/--
@isnad1 id=iff.0h5v.s5.055941216151 from=translated src=- shape=918edad7 vocab=e1fa421d
-/
theorem isMinimalBorder_swapYZFinset_iff (S : Finset (Normal a b c))
    (m : Normal a b c) :
    IsMinimalBorder (standardSet (swapYZFinset S)) (swapYZ m) ↔
      IsMinimalBorder (standardSet S) m := by
  simp only [IsMinimalBorder, ApplicablePredecessorsSurvive,
    mem_standardSet_swapYZFinset_iff, swapYZ_predecessor_x,
    swapYZ_predecessor_y, swapYZ_predecessor_z]
  constructor
  · rintro ⟨hm, hx, hy, hz⟩
    refine ⟨hm, ?_, ?_, ?_⟩
    · intro q hq
      have := hx (swapYZ q)
      simp [hq, mem_standardSet_swapYZFinset_iff] at this
      exact this
    · intro q hq
      have := hz (swapYZ q)
      simp [hq, mem_standardSet_swapYZFinset_iff] at this
      exact this
    · intro q hq
      have := hy (swapYZ q)
      simp [hq, mem_standardSet_swapYZFinset_iff] at this
      exact this
  · rintro ⟨hm, hx, hy, hz⟩
    refine ⟨hm, ?_, ?_, ?_⟩
    · intro q hq
      cases hp : Normal.predecessor .x m with
      | none => simp [hp, swapYZ_predecessor_x] at hq
      | some p =>
          have heq : swapYZ p = q := by
            simpa [swapYZ_predecessor_x, hp] using hq
          rw [← heq, mem_standardSet_swapYZFinset_iff]
          exact hx p hp
    · intro q hq
      cases hp : Normal.predecessor .z m with
      | none => simp [hp, swapYZ_predecessor_y] at hq
      | some p =>
          have heq : swapYZ p = q := by
            simpa [swapYZ_predecessor_y, hp] using hq
          rw [← heq, mem_standardSet_swapYZFinset_iff]
          exact hz p hp
    · intro q hq
      cases hp : Normal.predecessor .y m with
      | none => simp [hp, swapYZ_predecessor_z] at hq
      | some p =>
          have heq : swapYZ p = q := by
            simpa [swapYZ_predecessor_z, hp] using hq
          rw [← heq, mem_standardSet_swapYZFinset_iff]
          exact hy p hp

/--
@isnad1 id=eq.0h4v.s5.5db0edbe0c09 from=translated src=- shape=ee242f57 vocab=abdffda7
-/
theorem borderFinset_swapYZ_card (S : Finset (Normal a b c)) :
    (borderFinset (swapYZFinset S)).card = (borderFinset S).card := by
  classical
  by_cases hS : S.Nonempty
  · have hSwap : (swapYZFinset S).Nonempty := by
      rcases hS with ⟨s, hs⟩
      exact ⟨swapYZ s, Finset.mem_map.mpr ⟨s, hs, rfl⟩⟩
    refine Finset.card_bij (fun m _ => swapYZ m) ?_ ?_ ?_
    · intro m hm
      rw [mem_borderFinset_iff hS]
      exact (isMinimalBorder_swapYZFinset_iff S (swapYZ m)).1
        (by simpa using
          (mem_borderFinset_iff (S := swapYZFinset S) (m := m) hSwap).1 hm)
    · intro m₁ _ m₂ _ h
      exact swapYZEmbedding.injective h
    · intro q hq
      refine ⟨swapYZ q, ?_, by simp⟩
      rw [mem_borderFinset_iff hSwap]
      exact (isMinimalBorder_swapYZFinset_iff S q).2
        ((mem_borderFinset_iff (S := S) (m := q) hS).1 hq)
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rfl

/-- Exact equivariance of the finite border under the y/z reflection.
@isnad1 id=eq.0h4v.s5.e108420412ae from=translated src=- shape=bfa82f96 vocab=9a23cba9
-/
theorem borderFinset_swapYZ_exact (S : Finset (Normal a b c)) :
    borderFinset (swapYZFinset S) = swapYZFinset (borderFinset S) := by
  classical
  by_cases hS : S.Nonempty
  · have hSwap : (swapYZFinset S).Nonempty := by
      rcases hS with ⟨s, hs⟩
      exact ⟨swapYZ s, Finset.mem_map.mpr ⟨s, hs, rfl⟩⟩
    apply Finset.ext
    intro m
    rw [mem_borderFinset_iff hSwap]
    rw [show m ∈ swapYZFinset (borderFinset S) ↔
        ∃ q ∈ borderFinset S, swapYZ q = m by
      exact Finset.mem_map]
    constructor
    · intro hm
      refine ⟨swapYZ m, ?_, swapYZ_swapYZ m⟩
      rw [mem_borderFinset_iff hS]
      exact (isMinimalBorder_swapYZFinset_iff S (swapYZ m)).1 (by simpa using hm)
    · rintro ⟨q, hq, rfl⟩
      exact (isMinimalBorder_swapYZFinset_iff S q).2
        ((mem_borderFinset_iff hS q).1 hq)
  · have hEmpty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
    subst S
    rfl

/-! ## Reflected `Z,P` and `Z,Q` choices -/

def mixedSoclesZP (r u v : ℕ) (hr : r < a - 1) : Finset (Normal a b c) :=
  {mixedCore r u v (by omega), mixedZ v, mixedP r u hr}

def mixedSoclesZQ (r u v : ℕ) (hr : r < a - 1) : Finset (Normal a b c) :=
  {mixedCore r u v (by omega), mixedZ v, mixedQ r v hr}

/--
@isnad1 id=eq.1h6v.s6.532105fdb30f from=translated src=- shape=25734908 vocab=09e1f89d
-/
theorem swapYZFinset_mixedSoclesZP
    (hr : r < a - 1) :
    swapYZFinset (mixedSoclesZP (a := a) (b := b) (c := c) r u v hr) =
      mixedSoclesYQ (a := a) (b := c) (c := b) r v u hr := by
  ext m
  simp [swapYZFinset, mixedSoclesZP, mixedSoclesYQ, swapYZEmbedding,
    swapYZ, mixedCore, mixedY, mixedZ, mixedP, mixedQ]
  aesop

/--
@isnad1 id=eq.1h6v.s6.c5a5a28584ad from=translated src=- shape=25734908 vocab=f9bdcef6
-/
theorem swapYZFinset_mixedSoclesZQ
    (hr : r < a - 1) :
    swapYZFinset (mixedSoclesZQ (a := a) (b := b) (c := c) r u v hr) =
      mixedSoclesYP (a := a) (b := c) (c := b) r v u hr := by
  ext m
  simp [swapYZFinset, mixedSoclesZQ, mixedSoclesYP, swapYZEmbedding,
    swapYZ, mixedCore, mixedY, mixedZ, mixedP, mixedQ]
  aesop

/-- Exact reflected expected-border theorem for the `Z,P` choice.
@isnad1 id=eq.6h6v.s6.9e2db7fc46c4 from=translated src=- shape=896b7349 vocab=81b90b71
-/
theorem mixedBorderZP_exact
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    swapYZFinset (borderFinset
      (mixedSoclesZP (a := a) (b := b) (c := c) r u v hr)) =
      mixedExpectedBorderYQ (a := a) (b := c) (c := b) ha r v u hr := by
  rw [← borderFinset_swapYZ_exact, swapYZFinset_mixedSoclesZP]
  exact mixedBorderYQ_exact ha hc hb hv hu hr

/-- Exact reflected expected-border theorem for the `Z,Q` choice.
@isnad1 id=eq.6h6v.s6.b7d0087aeae6 from=translated src=- shape=896b7349 vocab=26670a9d
-/
theorem mixedBorderZQ_exact
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    swapYZFinset (borderFinset
      (mixedSoclesZQ (a := a) (b := b) (c := c) r u v hr)) =
      mixedExpectedBorderYP (a := a) (b := c) (c := b) ha r v u hr := by
  rw [← borderFinset_swapYZ_exact, swapYZFinset_mixedSoclesZQ]
  exact mixedBorderYP_exact ha hc hb hv hu hr

/--
@isnad1 id=eq.6h6v.s8.02c4bb42076f from=translated src=- shape=d69340c6 vocab=3aa12649
-/
theorem mixedBorderZP_card
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    (borderFinset
      (mixedSoclesZP (a := a) (b := b) (c := c) r u v hr)).card =
      3 + indicator (1 < r + 1) + indicator (r + 1 < a - 1) +
        2 * indicator (1 < b) + indicator (c < v) := by
  calc
    _ = (borderFinset (swapYZFinset
        (mixedSoclesZP (a := a) (b := b) (c := c) r u v hr))).card :=
      (borderFinset_swapYZ_card
        (mixedSoclesZP (a := a) (b := b) (c := c) r u v hr)).symm
    _ = (borderFinset
        (mixedSoclesYQ (a := a) (b := c) (c := b) r v u hr)).card := by
      rw [swapYZFinset_mixedSoclesZP]
    _ = _ := mixedBorderYQ_card ha hc hb hv hu hr

/--
@isnad1 id=eq.6h6v.s8.a77d408c3d56 from=translated src=- shape=200c0d59 vocab=a42acb14
-/
theorem mixedBorderZQ_card
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    (borderFinset
      (mixedSoclesZQ (a := a) (b := b) (c := c) r u v hr)).card =
      4 + indicator (1 < r + 1) + indicator (1 < c ∨ r + 1 = 1) +
        indicator (b < u) + indicator (1 < b ∧ r + 1 < a - 1) := by
  calc
    _ = (borderFinset (swapYZFinset
        (mixedSoclesZQ (a := a) (b := b) (c := c) r u v hr))).card :=
      (borderFinset_swapYZ_card
        (mixedSoclesZQ (a := a) (b := b) (c := c) r u v hr)).symm
    _ = (borderFinset
        (mixedSoclesYP (a := a) (b := c) (c := b) r v u hr)).card := by
      rw [swapYZFinset_mixedSoclesZQ]
    _ = _ := mixedBorderYP_card ha hc hb hv hu hr

/-! ## The `P,Q` choice -/

def mixedSoclesPQ (r u v : ℕ) (hr : r < a - 1) : Finset (Normal a b c) :=
  {mixedCore r u v (by omega), mixedP r u hr, mixedQ r v hr}

def mixedExpectedBorderPQ (r u v : ℕ) (hr : r < a - 1) :
    Finset (Normal a b c) :=
  {mixedY u, mixedZ v} ∪
    singletonProofIf (r + 1 < a - 1) (mixedPTimesX r u) ∪
    singletonProofIf (r + 1 < a - 1) (mixedQTimesX r v) ∪
    singletonIf (1 < b) (mixedPTimesY r u hr) ∪
    singletonIf (1 < c) (mixedQTimesZ r v hr) ∪
    singletonIf (c < v ∨ (u + 1 - b = 1 ∧ v + 1 - c = 1))
      (mixedPTimesZ r u hr) ∪
    singletonIf (b < u ∨ (u + 1 - b = 1 ∧ v + 1 - c = 1))
      (mixedQTimesY r v hr)

def mixedPQStandardNat (b c r u v x y z : ℕ) : Prop :=
  (y ≤ u ∧ z ≤ v ∧ (x ≤ r ∨ (y + b ≤ u ∧ z + c ≤ v))) ∨
  (x ≤ r + 1 ∧ y ≤ u + 1 - b ∧ z = 0) ∨
  (x ≤ r + 1 ∧ y = 0 ∧ z ≤ v + 1 - c)

def mixedPQBorderNat (a b c r u v x y z : ℕ) : Prop :=
  (x = 0 ∧ y = u + 1 ∧ z = 0) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 1) ∨
  (r + 1 < a - 1 ∧ x = r + 2 ∧ y = u + 1 - b ∧ z = 0) ∨
  (r + 1 < a - 1 ∧ x = r + 2 ∧ y = 0 ∧ z = v + 1 - c) ∨
  (1 < b ∧ x = r + 1 ∧ y = u + 2 - b ∧ z = 0) ∨
  (1 < c ∧ x = r + 1 ∧ y = 0 ∧ z = v + 2 - c) ∨
  ((c < v ∨ (u + 1 - b = 1 ∧ v + 1 - c = 1)) ∧
    x = r + 1 ∧ y = u + 1 - b ∧ z = 1) ∨
  ((b < u ∨ (u + 1 - b = 1 ∧ v + 1 - c = 1)) ∧
    x = r + 1 ∧ y = 1 ∧ z = v + 1 - c)

/--
@isnad1 id=iff.5h7v.s6.178003649f50 from=translated src=- shape=37667727 vocab=54438518
-/
theorem mem_standardSet_mixedSoclesPQ_iff
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hu : b ≤ u) (hv : c ≤ v)
    (hr : r < a - 1) (p : Normal a b c) :
    p ∈ standardSet (mixedSoclesPQ (a := a) (b := b) (c := c) r u v hr) ↔
      mixedPQStandardNat b c r u v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, mixedSoclesPQ, Normal.exact_divides_iff,
    Normal.DividesCriterion, mixedCore, mixedP, mixedQ, mixedPQStandardNat]
  omega

set_option maxHeartbeats 1200000 in
/--
@isnad1 id=iff.1h7v.s6.d87103197c1e from=translated src=- shape=375a085c vocab=5978f520
-/
theorem mem_mixedExpectedBorderPQ_iff
    (r u v : ℕ) (hr : r < a - 1) (m : Normal a b c) :
    m ∈ mixedExpectedBorderPQ (a := a) (b := b) (c := c) r u v hr ↔
      mixedPQBorderNat a b c r u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hh : r + 1 < a - 1
  · simp [mixedExpectedBorderPQ, singletonProofIf, hh,
      mem_singletonIf_iff,
      mixedPQBorderNat, mixedY, mixedZ, mixedPTimesX, mixedQTimesX,
      mixedPTimesY, mixedQTimesZ, mixedPTimesZ, mixedQTimesY, or_assoc]
  · simp [mixedExpectedBorderPQ, singletonProofIf, hh,
      mem_singletonIf_iff,
      mixedPQBorderNat, mixedY, mixedZ, mixedPTimesX, mixedQTimesX,
      mixedPTimesY, mixedQTimesZ, mixedPTimesZ, mixedQTimesY, or_assoc]

set_option maxHeartbeats 6400000 in
omit [NeZero a] in
/--
@isnad1 id=iff.7h9v.s8.be55aec3098e from=translated src=- shape=dcc2d1fe vocab=f97d60c5
-/
theorem mixedPQ_border_arithmetic
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1)
    (x y z : ℕ) (hxlt : x < a) :
    (¬mixedPQStandardNat b c r u v x y z ∧
      (if 0 < x then mixedPQStandardNat b c r u v (x - 1) y z
       else if b ≤ y ∧ c ≤ z then
         mixedPQStandardNat b c r u v (a - 1) (y - b) (z - c)
       else True) ∧
      (0 < y → mixedPQStandardNat b c r u v x (y - 1) z) ∧
      (0 < z → mixedPQStandardNat b c r u v x y (z - 1))) ↔
      mixedPQBorderNat a b c r u v x y z := by
  by_cases hx : 0 < x
  · by_cases hy : 0 < y <;> by_cases hz : 0 < z
    all_goals simp [hx, hy, hz, mixedPQStandardNat, mixedPQBorderNat]
      <;> grind (splits := 48)
  · have hx0 : x = 0 := by omega
    by_cases hby : b ≤ y
    · by_cases hcz : c ≤ z
      · by_cases hy : 0 < y <;> by_cases hz : 0 < z
        all_goals simp [hx0, hby, hcz, hy, hz, mixedPQStandardNat,
          mixedPQBorderNat] <;> grind (splits := 48)
      · by_cases hy : 0 < y <;> by_cases hz : 0 < z
        all_goals simp [hx0, hby, hcz, hy, hz, mixedPQStandardNat,
          mixedPQBorderNat] <;> grind (splits := 48)
    · by_cases hy : 0 < y <;> by_cases hz : 0 < z
      all_goals simp [hx0, hby, hy, hz, mixedPQStandardNat,
        mixedPQBorderNat] <;> grind (splits := 48)

/--
@isnad1 id=eq.6h6v.s6.8efcf61ffef3 from=translated src=- shape=37584727 vocab=21618e7f
-/
theorem mixedBorderPQ_exact
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    borderFinset (mixedSoclesPQ (a := a) (b := b) (c := c) r u v hr) =
      mixedExpectedBorderPQ (a := a) (b := b) (c := c) r u v hr := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp [mixedSoclesPQ])]
  rw [mem_mixedExpectedBorderPQ_iff r u v hr]
  rcases m with ⟨mx, my, mz, hmx⟩
  have harith := mixedPQ_border_arithmetic ha hb hc hu hv hr mx my mz hmx
  by_cases hx : 0 < mx
  · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
      mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr,
      mixedPQStandardNat, Normal.predecessor, Normal.xPredecessor,
      Normal.yPredecessor, Normal.zPredecessor, hx] using harith
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · by_cases hcz : c ≤ mz
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr,
          mixedPQStandardNat, Normal.predecessor, Normal.wrappedXPredecessor,
          Normal.yPredecessor, Normal.zPredecessor, hx, hx0, hby, hcz]
          using harith
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr,
          mixedPQStandardNat, Normal.predecessor, Normal.yPredecessor,
          Normal.zPredecessor, hx, hx0, hby, hcz] using harith
    · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
        mem_standardSet_mixedSoclesPQ_iff hb hc hu hv hr,
        mixedPQStandardNat, Normal.predecessor, Normal.yPredecessor,
        Normal.zPredecessor, hx, hx0, hby] using harith

set_option maxHeartbeats 12000000 in
set_option maxRecDepth 8192 in
/--
@isnad1 id=eq.6h6v.s8.6a9826bca8cb from=translated src=- shape=29799a00 vocab=e233b00b
-/
theorem mixedBorderPQ_card
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    (borderFinset
      (mixedSoclesPQ (a := a) (b := b) (c := c) r u v hr)).card =
      3 + 2 * indicator (r + 1 < a - 1) + indicator (1 < b) +
        indicator (1 < c) + indicator (b < u ∧ c < v) := by
  rw [mixedBorderPQ_exact ha hb hc hu hv hr]
  let s0 : Finset (Normal a b c) := {mixedY u, mixedZ v}
  let s1 := s0 ∪ singletonProofIf (r + 1 < a - 1) (mixedPTimesX r u)
  let s2 := s1 ∪ singletonProofIf (r + 1 < a - 1) (mixedQTimesX r v)
  let s3 := s2 ∪ singletonIf (1 < b) (mixedPTimesY r u hr)
  let s4 := s3 ∪ singletonIf (1 < c) (mixedQTimesZ r v hr)
  have hs0 : s0.card = 2 := by simp [s0, mixedY, mixedZ]
  have h1 : ∀ hh : r + 1 < a - 1,
      mixedPTimesX (a := a) (b := b) (c := c) r u hh ∉ s0 := by
    intro hh; simp [s0, mixedY, mixedZ, mixedPTimesX]
  have hs1 : s1.card = s0.card + indicator (r + 1 < a - 1) :=
    card_union_singletonProofIf s0 _ _ h1
  have h2 : ∀ hh : r + 1 < a - 1,
      mixedQTimesX (a := a) (b := b) (c := c) r v hh ∉ s1 := by
    intro hh; simp [s1, s0, singletonProofIf, mixedY, mixedZ,
      mixedPTimesX, mixedQTimesX]
    split_ifs <;> simp_all <;> omega
  have hs2 : s2.card = s1.card + indicator (r + 1 < a - 1) :=
    card_union_singletonProofIf s1 _ _ h2
  have h3 : 1 < b → mixedPTimesY (a := a) (b := b) (c := c) r u hr ∉ s2 := by
    intro hb1; simp [s2, s1, s0, singletonProofIf, mixedY, mixedZ,
      mixedPTimesX, mixedQTimesX, mixedPTimesY]
    split_ifs <;> simp_all <;> omega
  have hs3 : s3.card = s2.card + indicator (1 < b) :=
    card_union_singletonIf s2 _ _ h3
  have h4 : 1 < c → mixedQTimesZ (a := a) (b := b) (c := c) r v hr ∉ s3 := by
    intro hc1; simp [s3, s2, s1, s0, singletonProofIf, singletonIf,
      mixedY, mixedZ, mixedPTimesX, mixedQTimesX, mixedPTimesY,
      mixedQTimesZ]
    split_ifs <;> simp_all <;> omega
  have hs4 : s4.card = s3.card + indicator (1 < c) :=
    card_union_singletonIf s3 _ _ h4
  have hp : mixedPTimesZ (a := a) (b := b) (c := c) r u hr ∉ s4 := by
    simp [s4, s3, s2, s1, s0, singletonProofIf, singletonIf,
      mixedY, mixedZ, mixedPTimesX, mixedQTimesX, mixedPTimesY,
      mixedQTimesZ, mixedPTimesZ]
    split_ifs <;> simp_all <;> omega
  have hq : mixedQTimesY (a := a) (b := b) (c := c) r v hr ∉ s4 := by
    simp [s4, s3, s2, s1, s0, singletonProofIf, singletonIf,
      mixedY, mixedZ, mixedPTimesX, mixedQTimesX, mixedPTimesY,
      mixedQTimesZ, mixedQTimesY]
    split_ifs <;> simp_all <;> omega
  change (s4 ∪ singletonIf (c < v ∨ (u + 1 - b = 1 ∧ v + 1 - c = 1))
      (mixedPTimesZ r u hr) ∪
      singletonIf (b < u ∨ (u + 1 - b = 1 ∧ v + 1 - c = 1))
        (mixedQTimesY r v hr)).card = _
  by_cases hdu : b < u <;> by_cases hev : c < v
  · have hne : mixedQTimesY (a := a) (b := b) (c := c) r v hr ≠
        mixedPTimesZ r u hr := by
      intro heq
      have hy := congrArg Normal.y heq
      have hz := congrArg Normal.z heq
      simp [mixedPTimesZ, mixedQTimesY] at hy hz
      omega
    have hpafter : mixedPTimesZ (a := a) (b := b) (c := c) r u hr ∉
        insert (mixedQTimesY r v hr) s4 := by
      simp only [Finset.mem_insert, not_or]
      exact ⟨hne.symm, hp⟩
    simp [singletonIf, hdu, hev]
    rw [Finset.card_insert_of_notMem hpafter,
      Finset.card_insert_of_notMem hq, hs4, hs3, hs2, hs1, hs0]
    by_cases hh : r + 1 < a - 1 <;> by_cases hb1 : 1 < b <;>
      by_cases hc1 : 1 < c <;> simp [indicator, hh, hb1, hc1]
  · have hu1 : u + 1 - b ≠ 1 := by omega
    have hv1 : v + 1 - c = 1 := by omega
    simp [singletonIf, hdu, hev, hu1, hv1]
    rw [Finset.card_insert_of_notMem hq, hs4, hs3, hs2, hs1, hs0]
    by_cases hh : r + 1 < a - 1 <;> by_cases hb1 : 1 < b <;>
      by_cases hc1 : 1 < c <;> simp [indicator, hh, hb1, hc1]
  · have hu1 : u + 1 - b = 1 := by omega
    have hv1 : v + 1 - c ≠ 1 := by omega
    simp [singletonIf, hdu, hev, hu1, hv1]
    rw [Finset.card_insert_of_notMem hp, hs4, hs3, hs2, hs1, hs0]
    by_cases hh : r + 1 < a - 1 <;> by_cases hb1 : 1 < b <;>
      by_cases hc1 : 1 < c <;> simp [indicator, hh, hb1, hc1]
  · have hu1 : u + 1 - b = 1 := by omega
    have hv1 : v + 1 - c = 1 := by omega
    have heq : mixedPTimesZ (a := a) (b := b) (c := c) r u hr =
        mixedQTimesY r v hr := by
      ext <;> simp [mixedPTimesZ, mixedQTimesY, hu1, hv1]
    simp [singletonIf, hdu, hev, hu1, hv1, heq]
    rw [Finset.card_insert_of_notMem hq, hs4, hs3, hs2, hs1, hs0]
    by_cases hh : r + 1 < a - 1 <;> by_cases hb1 : 1 < b <;>
      by_cases hc1 : 1 < c <;> simp [indicator, hh, hb1, hc1]

/-! ## The exact-cardinality-four survivors

This wrapper only packages the six already-proved cardinalities.  Its
classification theorem is deliberately an implication: the later canonical
trace exclusions are outside Run 03.
-/

noncomputable def mixedDominantBorderCard (pair : MixedAddedPair)
    (r u v : ℕ) (hr : r < a - 1) : ℕ :=
  match pair with
  | .YZ => (borderFinset (mixedSoclesYZ (a := a) (b := b) (c := c) r u v hr)).card
  | .YP => (borderFinset (mixedSoclesYP (a := a) (b := b) (c := c) r u v hr)).card
  | .YQ => (borderFinset (mixedSoclesYQ (a := a) (b := b) (c := c) r u v hr)).card
  | .ZP => (borderFinset (mixedSoclesZP (a := a) (b := b) (c := c) r u v hr)).card
  | .ZQ => (borderFinset (mixedSoclesZQ (a := a) (b := b) (c := c) r u v hr)).card
  | .PQ => (borderFinset (mixedSoclesPQ (a := a) (b := b) (c := c) r u v hr)).card

/-- If a dominant mixed three-socle choice has exact border cardinality four,
then it is one of the three command-authorized survivor shapes, with the
`YQ` reflection `ZP` displayed explicitly.
@isnad1 id=or.7h7v.s7.33eaacd6f04d from=translated src=- shape=e35913cf vocab=baed9975
-/
theorem mixedDominant_card_eq_four_survivors
    (pair : MixedAddedPair)
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1)
    (hcard : mixedDominantBorderCard (a := a) (b := b) (c := c)
      pair r u v hr = 4) :
    (pair = .YZ ∧ r + 1 = 1 ∧ b = 1 ∧ c = 1) ∨
    (pair = .YQ ∧ c = 1) ∨
    (pair = .ZP ∧ b = 1) ∨
    (pair = .PQ ∧ r + 1 = a - 1 ∧ (1 < u ∨ 1 < v)) := by
  cases pair with
  | YZ =>
      simp only [mixedDominantBorderCard] at hcard
      rw [mixedBorderYZ_card ha hb hc hu hv hr] at hcard
      unfold indicator at hcard
      split_ifs at hcard <;> simp_all <;> omega
  | YP =>
      simp only [mixedDominantBorderCard] at hcard
      rw [mixedBorderYP_card ha hb hc hu hv hr] at hcard
      unfold indicator at hcard
      split_ifs at hcard <;> omega
  | YQ =>
      simp only [mixedDominantBorderCard] at hcard
      rw [mixedBorderYQ_card ha hb hc hu hv hr] at hcard
      unfold indicator at hcard
      split_ifs at hcard <;> simp_all <;> omega
  | ZP =>
      simp only [mixedDominantBorderCard] at hcard
      rw [mixedBorderZP_card ha hb hc hu hv hr] at hcard
      unfold indicator at hcard
      split_ifs at hcard <;> simp_all <;> omega
  | ZQ =>
      simp only [mixedDominantBorderCard] at hcard
      rw [mixedBorderZQ_card ha hb hc hu hv hr] at hcard
      unfold indicator at hcard
      split_ifs at hcard <;> omega
  | PQ =>
      simp only [mixedDominantBorderCard] at hcard
      rw [mixedBorderPQ_card ha hb hc hu hv hr] at hcard
      unfold indicator at hcard
      split_ifs at hcard <;> simp_all <;> omega

end P23.OneTie
