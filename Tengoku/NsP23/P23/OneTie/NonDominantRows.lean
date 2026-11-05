import Tengoku.NsP23.P23.OneTie.SemanticBorder
import Tengoku.NsP23.P23.OneTie.PureCases

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 1: exact non-dominant type-three rows

The rows in this module are the eight explicit three-socle configurations from
the human generator table. Nothing here states that they exhaust the
non-dominant directional-centre configurations.
-/

namespace P23.OneTie

private theorem a_pos {a : ℕ} [NeZero a] : 0 < a :=
  Nat.pos_of_ne_zero (NeZero.ne a)

/-! ## M2K and M2Z (`b=c=1`) -/

variable {a r u v : ℕ} [NeZero a]

def m2Core (ha : 2 ≤ a) (r u v : ℕ) (hr : r ≤ a - 2) : Normal a 1 1 :=
  ⟨r, u, v, by omega⟩

def m2Partner (ha : 2 ≤ a) (r u v : ℕ) (hr : r ≤ a - 2) : Normal a 1 1 :=
  ⟨r + 1, u - 1, v, by omega⟩

def m2KRoot (ha : 2 ≤ a) (r u : ℕ) (hr : r ≤ a - 2) : Normal a 1 1 :=
  ⟨r + 1, u, 0, by omega⟩

def m2ZRoot (v : ℕ) : Normal a 1 1 :=
  ⟨0, 0, v + 1, a_pos⟩

def m2KSocles (ha : 2 ≤ a) (r u v : ℕ) (hr : r ≤ a - 2) : Finset (Normal a 1 1) :=
  {m2Core ha r u v hr, m2Partner ha r u v hr, m2KRoot ha r u hr}

def m2ZSocles (ha : 2 ≤ a) (r u v : ℕ) (hr : r ≤ a - 2) : Finset (Normal a 1 1) :=
  {m2Core ha r u v hr, m2Partner ha r u v hr, m2ZRoot v}

def m2YBorder (u : ℕ) : Normal a 1 1 := ⟨0, u + 1, 0, a_pos⟩
def m2ZBorder (v : ℕ) : Normal a 1 1 := ⟨0, 0, v + 1, a_pos⟩
def m2KDiagonal (ha : 2 ≤ a) (r u : ℕ) (hr : r ≤ a - 2) : Normal a 1 1 :=
  ⟨r + 1, u, 1, by omega⟩

def m2KExpectedBorder (ha : 2 ≤ a) (r u v : ℕ) (hr : r ≤ a - 2) :
    Finset (Normal a 1 1) :=
  if h : r = a - 2 then
    {m2YBorder u, m2ZBorder v, m2KDiagonal ha r u hr}
  else
    {m2YBorder u, m2ZBorder v, m2KDiagonal ha r u hr,
      (⟨r + 2, u, 0, by omega⟩ : Normal a 1 1),
      (⟨r + 2, 0, v, by omega⟩ : Normal a 1 1)}

def m2ZExpectedBorder (ha : 2 ≤ a) (r u v : ℕ) (hr : r ≤ a - 2) :
    Finset (Normal a 1 1) :=
  if h : r = a - 2 then
    {m2YBorder u, (⟨0, 0, v + 2, a_pos⟩ : Normal a 1 1),
      (⟨1, 0, v + 1, by omega⟩ : Normal a 1 1),
      (⟨r + 1, u, 0, by omega⟩ : Normal a 1 1),
      (⟨0, 1, v + 1, a_pos⟩ : Normal a 1 1)}
  else
    {m2YBorder u, (⟨0, 0, v + 2, a_pos⟩ : Normal a 1 1),
      (⟨1, 0, v + 1, by omega⟩ : Normal a 1 1),
      (⟨r + 1, u, 0, by omega⟩ : Normal a 1 1),
      (⟨r + 2, 0, v, by omega⟩ : Normal a 1 1)}

/-- At `r=a-2`, `x^(r+2)y^u = y^(u+1)z`.-/
theorem m2K_endpoint_xK (ha : 2 ≤ a) (_hu : 1 ≤ u)
    (hr : r ≤ a - 2) (hend : r = a - 2) :
    m2KRoot (a := a) ha r u hr *
        (Normal.xGenerator : Normal a 1 1) =
      m2YBorder (a := a) u * (Normal.zGenerator : Normal a 1 1) := by
  have hsum : r + 1 + 1 = a := by omega
  have hdiv : a / a = 1 := Nat.div_self (by omega)
  apply Normal.ext
  · simp [m2KRoot, m2YBorder, Normal.xGenerator, Normal.zGenerator,
      show a ≠ 1 by omega, hsum]
  · simp [m2KRoot, m2YBorder, Normal.xGenerator, Normal.zGenerator,
      show a ≠ 1 by omega, hsum, hdiv]
  · simp [m2KRoot, m2YBorder, Normal.xGenerator, Normal.zGenerator,
      show a ≠ 1 by omega, hsum, hdiv]

/-- At `r=a-2`, `x^(r+2)z^v = yz^(v+1)`.-/
theorem m2K_endpoint_xQ (ha : 2 ≤ a) (_hv : 1 ≤ v)
    (hr : r ≤ a - 2) (hend : r = a - 2) :
    (⟨r + 1, 0, v, by omega⟩ : Normal a 1 1) *
        (Normal.xGenerator : Normal a 1 1) =
      m2ZBorder (a := a) v * (Normal.yGenerator : Normal a 1 1) := by
  have hsum : r + 1 + 1 = a := by omega
  have hdiv : a / a = 1 := Nat.div_self (by omega)
  apply Normal.ext
  · simp [m2ZBorder, Normal.xGenerator, Normal.yGenerator,
      show a ≠ 1 by omega, hsum]
  · simp [m2ZBorder, Normal.xGenerator, Normal.yGenerator,
      show a ≠ 1 by omega, hsum, hdiv]
  · simp [m2ZBorder, Normal.xGenerator, Normal.yGenerator,
      show a ≠ 1 by omega, hsum, hdiv]

theorem m2Z_endpoint_xQ (ha : 2 ≤ a) (_hv : 1 ≤ v)
    (hr : r ≤ a - 2) (hend : r = a - 2) :
    (⟨r + 1, 0, v, by omega⟩ : Normal a 1 1) *
        (Normal.xGenerator : Normal a 1 1) =
      (⟨0, 1, v + 1, a_pos⟩ : Normal a 1 1) := by
  have hsum : r + 1 + 1 = a := by omega
  have hdiv : a / a = 1 := Nat.div_self (by omega)
  apply Normal.ext
  · simp [Normal.xGenerator, show a ≠ 1 by omega, hsum]
  · simp [Normal.xGenerator, show a ≠ 1 by omega, hsum, hdiv]
  · simp [Normal.xGenerator, show a ≠ 1 by omega, hsum, hdiv]

def m2KStandardNat (r u v x y z : ℕ) : Prop :=
  (y ≤ u ∧ z ≤ v ∧ (x ≤ r ∨ (y + 1 ≤ u ∧ z + 1 ≤ v))) ∨
  (y ≤ u - 1 ∧ z ≤ v ∧
    (x ≤ r + 1 ∨ (y + 1 ≤ u - 1 ∧ z + 1 ≤ v))) ∨
  (y ≤ u ∧ z = 0 ∧ x ≤ r + 1)

def m2KBorderNat (a r u v x y z : ℕ) : Prop :=
  (x = 0 ∧ y = u + 1 ∧ z = 0) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 1) ∨
  (x = r + 1 ∧ y = u ∧ z = 1) ∨
  (r ≠ a - 2 ∧
    ((x = r + 2 ∧ y = u ∧ z = 0) ∨
     (x = r + 2 ∧ y = 0 ∧ z = v)))

def m2ZStandardNat (r u v x y z : ℕ) : Prop :=
  (y ≤ u ∧ z ≤ v ∧ (x ≤ r ∨ (y + 1 ≤ u ∧ z + 1 ≤ v))) ∨
  (y ≤ u - 1 ∧ z ≤ v ∧
    (x ≤ r + 1 ∨ (y + 1 ≤ u - 1 ∧ z + 1 ≤ v))) ∨
  (x = 0 ∧ y = 0 ∧ z ≤ v + 1)

def m2ZBorderNat (a r u v x y z : ℕ) : Prop :=
  (x = 0 ∧ y = u + 1 ∧ z = 0) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 2) ∨
  (x = 1 ∧ y = 0 ∧ z = v + 1) ∨
  (x = r + 1 ∧ y = u ∧ z = 0) ∨
  ((r = a - 2 ∧ x = 0 ∧ y = 1 ∧ z = v + 1) ∨
   (r ≠ a - 2 ∧ x = r + 2 ∧ y = 0 ∧ z = v))

theorem mem_standardSet_m2K_iff (ha : 2 ≤ a) (hu : 1 ≤ u) (hr : r ≤ a - 2)
    (p : Normal a 1 1) :
    p ∈ standardSet (m2KSocles (a := a) ha r u v hr) ↔
      m2KStandardNat r u v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, m2KSocles, m2Core, m2Partner, m2KRoot,
    Normal.exact_divides_iff, Normal.DividesCriterion, m2KStandardNat]

theorem mem_standardSet_m2Z_iff (ha : 2 ≤ a) (hu : 1 ≤ u) (hr : r ≤ a - 2)
    (p : Normal a 1 1) :
    p ∈ standardSet (m2ZSocles (a := a) ha r u v hr) ↔
      m2ZStandardNat r u v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, m2ZSocles, m2Core, m2Partner, m2ZRoot,
    Normal.exact_divides_iff, Normal.DividesCriterion, m2ZStandardNat]
  omega

theorem mem_m2KExpectedBorder_iff (ha : 2 ≤ a) (hr : r ≤ a - 2)
    (m : Normal a 1 1) :
    m ∈ m2KExpectedBorder (a := a) ha r u v hr ↔
      m2KBorderNat a r u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases h : r = a - 2 <;>
    simp [m2KExpectedBorder, h, m2KBorderNat, m2YBorder, m2ZBorder,
      m2KDiagonal, Normal.mk.injEq]

theorem mem_m2ZExpectedBorder_iff (ha : 2 ≤ a) (hr : r ≤ a - 2)
    (m : Normal a 1 1) :
    m ∈ m2ZExpectedBorder (a := a) ha r u v hr ↔
      m2ZBorderNat a r u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases h : r = a - 2 <;>
    simp [m2ZExpectedBorder, h, m2ZBorderNat, m2YBorder, Normal.mk.injEq]

set_option maxHeartbeats 6400000 in
theorem m2K_border_arithmetic (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : r ≤ a - 2) (x y z : ℕ) (hxlt : x < a) :
    (¬m2KStandardNat r u v x y z ∧
      (if 0 < x then m2KStandardNat r u v (x - 1) y z
       else if 1 ≤ y ∧ 1 ≤ z then
         m2KStandardNat r u v (a - 1) (y - 1) (z - 1)
       else True) ∧
      (0 < y → m2KStandardNat r u v x (y - 1) z) ∧
      (0 < z → m2KStandardNat r u v x y (z - 1))) ↔
      m2KBorderNat a r u v x y z := by
  by_cases hend : r = a - 2 <;>
    by_cases hx : 0 < x <;> by_cases hy : 1 ≤ y <;> by_cases hz : 1 ≤ z
  all_goals
    simp [hx, hy, hz, hend, Nat.lt_iff_add_one_le, m2KStandardNat,
      m2KBorderNat] <;> grind (splits := 32)

set_option maxHeartbeats 6400000 in
theorem m2Z_border_arithmetic (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : r ≤ a - 2) (x y z : ℕ) (hxlt : x < a) :
    (¬m2ZStandardNat r u v x y z ∧
      (if 0 < x then m2ZStandardNat r u v (x - 1) y z
       else if 1 ≤ y ∧ 1 ≤ z then
         m2ZStandardNat r u v (a - 1) (y - 1) (z - 1)
       else True) ∧
      (0 < y → m2ZStandardNat r u v x (y - 1) z) ∧
      (0 < z → m2ZStandardNat r u v x y (z - 1))) ↔
      m2ZBorderNat a r u v x y z := by
  by_cases hend : r = a - 2 <;>
    by_cases hx : 0 < x <;> by_cases hy : 1 ≤ y <;> by_cases hz : 1 ≤ z
  all_goals
    simp [hx, hy, hz, hend, Nat.lt_iff_add_one_le, m2ZStandardNat,
      m2ZBorderNat] <;> grind (splits := 32)

theorem m2K_border_exact (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : r ≤ a - 2) :
    borderFinset (m2KSocles (a := a) ha r u v hr) =
      m2KExpectedBorder (a := a) ha r u v hr := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp [m2KSocles])]
  rw [mem_m2KExpectedBorder_iff ha hr]
  rcases m with ⟨mx, my, mz, hmx⟩
  have harith := m2K_border_arithmetic ha hu hv hr mx my mz hmx
  by_cases hx : 0 < mx
  · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
      mem_standardSet_m2K_iff ha hu hr, Normal.predecessor,
      Normal.xPredecessor, Normal.yPredecessor, Normal.zPredecessor, hx]
      using harith
  · have hx0 : mx = 0 := by omega
    by_cases hy : 1 ≤ my
    · by_cases hz : 1 ≤ mz
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_m2K_iff ha hu hr, Normal.predecessor,
          Normal.wrappedXPredecessor, Normal.yPredecessor,
          Normal.zPredecessor, hx, hx0, hy, hz, Nat.lt_iff_add_one_le]
          using harith
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_m2K_iff ha hu hr, Normal.predecessor,
          Normal.yPredecessor, Normal.zPredecessor, hx, hx0, hy, hz,
          Nat.lt_iff_add_one_le] using harith
    · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
        mem_standardSet_m2K_iff ha hu hr, Normal.predecessor,
        Normal.yPredecessor, Normal.zPredecessor, hx, hx0, hy,
        Nat.lt_iff_add_one_le] using harith

theorem m2K_border_card (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : r ≤ a - 2) :
    (borderFinset (m2KSocles (a := a) ha r u v hr)).card =
      if r = a - 2 then 3 else 5 := by
  rw [m2K_border_exact ha hu hv hr]
  by_cases h : r = a - 2
  · simp [m2KExpectedBorder, h, m2YBorder, m2ZBorder, m2KDiagonal]
  · have hlt : r < a - 2 := by omega
    rw [show m2KExpectedBorder (a := a) ha r u v hr =
        {m2YBorder u, m2ZBorder v, m2KDiagonal ha r u hr,
          (⟨r + 2, u, 0, by omega⟩ : Normal a 1 1),
          (⟨r + 2, 0, v, by omega⟩ : Normal a 1 1)} by
      simp [m2KExpectedBorder, h]]
    have hY : m2YBorder (a := a) u ∉
        ({m2ZBorder (a := a) v, m2KDiagonal (a := a) ha r u hr,
          (⟨r + 2, u, 0, by omega⟩ : Normal a 1 1),
          (⟨r + 2, 0, v, by omega⟩ : Normal a 1 1)} :
          Finset (Normal a 1 1)) := by
      simp [m2YBorder, m2ZBorder, m2KDiagonal]
    have hZ : m2ZBorder (a := a) v ∉
        ({m2KDiagonal (a := a) ha r u hr,
          (⟨r + 2, u, 0, by omega⟩ : Normal a 1 1),
          (⟨r + 2, 0, v, by omega⟩ : Normal a 1 1)} :
          Finset (Normal a 1 1)) := by
      simp [m2ZBorder, m2KDiagonal]
    have hA : m2KDiagonal (a := a) ha r u hr ∉
        ({(⟨r + 2, u, 0, by omega⟩ : Normal a 1 1),
          (⟨r + 2, 0, v, by omega⟩ : Normal a 1 1)} :
          Finset (Normal a 1 1)) := by
      simp [m2KDiagonal]
    have hB : (⟨r + 2, u, 0, by omega⟩ : Normal a 1 1) ∉
        ({(⟨r + 2, 0, v, by omega⟩ : Normal a 1 1)} :
          Finset (Normal a 1 1)) := by
      simp
      omega
    rw [Finset.card_insert_of_notMem hY]
    rw [Finset.card_insert_of_notMem hZ]
    rw [Finset.card_insert_of_notMem hA]
    rw [Finset.card_insert_of_notMem hB]
    simpa [h]

theorem m2Z_border_exact (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : r ≤ a - 2) :
    borderFinset (m2ZSocles (a := a) ha r u v hr) =
      m2ZExpectedBorder (a := a) ha r u v hr := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp [m2ZSocles])]
  rw [mem_m2ZExpectedBorder_iff ha hr]
  rcases m with ⟨mx, my, mz, hmx⟩
  have harith := m2Z_border_arithmetic ha hu hv hr mx my mz hmx
  by_cases hx : 0 < mx
  · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
      mem_standardSet_m2Z_iff ha hu hr, Normal.predecessor,
      Normal.xPredecessor, Normal.yPredecessor, Normal.zPredecessor, hx]
      using harith
  · have hx0 : mx = 0 := by omega
    by_cases hy : 1 ≤ my
    · by_cases hz : 1 ≤ mz
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_m2Z_iff ha hu hr, Normal.predecessor,
          Normal.wrappedXPredecessor, Normal.yPredecessor,
          Normal.zPredecessor, hx, hx0, hy, hz, Nat.lt_iff_add_one_le]
          using harith
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
          mem_standardSet_m2Z_iff ha hu hr, Normal.predecessor,
          Normal.yPredecessor, Normal.zPredecessor, hx, hx0, hy, hz,
          Nat.lt_iff_add_one_le] using harith
    · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive,
        mem_standardSet_m2Z_iff ha hu hr, Normal.predecessor,
        Normal.yPredecessor, Normal.zPredecessor, hx, hx0, hy,
        Nat.lt_iff_add_one_le] using harith

theorem m2Z_border_card (ha : 2 ≤ a) (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hr : r ≤ a - 2) :
    (borderFinset (m2ZSocles (a := a) ha r u v hr)).card = 5 := by
  rw [m2Z_border_exact ha hu hv hr]
  by_cases h : r = a - 2 <;>
    simp [m2ZExpectedBorder, h, m2YBorder] <;> omega

/-! A shared transport from coordinate arithmetic to exact finite borders. -/

theorem borderFinset_eq_expected_of_nat {a b c : ℕ} [NeZero a]
    (S G : Finset (Normal a b c))
    (Std Border : ℕ → ℕ → ℕ → Prop)
    (hS : S.Nonempty)
    (hstd : ∀ p, p ∈ standardSet S ↔ Std p.x p.y p.z)
    (hG : ∀ m, m ∈ G ↔ Border m.x m.y m.z)
    (harith : ∀ x y z, x < a →
      ((¬Std x y z ∧
        (if 0 < x then Std (x - 1) y z
         else if b ≤ y ∧ c ≤ z then Std (a - 1) (y - b) (z - c)
         else True) ∧
        (0 < y → Std x (y - 1) z) ∧
        (0 < z → Std x y (z - 1))) ↔ Border x y z)) :
    borderFinset S = G := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff hS, hG m]
  rcases m with ⟨mx, my, mz, hmx⟩
  have h := harith mx my mz hmx
  by_cases hx : 0 < mx
  · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive, hstd,
      Normal.predecessor, Normal.xPredecessor, Normal.yPredecessor,
      Normal.zPredecessor, hx] using h
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · by_cases hcz : c ≤ mz
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive, hstd,
          Normal.predecessor, Normal.wrappedXPredecessor,
          Normal.yPredecessor, Normal.zPredecessor, hx, hx0, hby, hcz]
          using h
      · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive, hstd,
          Normal.predecessor, Normal.yPredecessor, Normal.zPredecessor,
          hx, hx0, hby, hcz] using h
    · simpa [IsMinimalBorder, ApplicablePredecessorsSurvive, hstd,
        Normal.predecessor, Normal.yPredecessor, Normal.zPredecessor,
        hx, hx0, hby] using h

/-! ## M3K -/

variable {b c : ℕ}

def m3D (v c : ℕ) : ℕ := v + 1 - c

def m3KCore (v : ℕ) : Normal a b c := ⟨0, b, v, a_pos⟩
def m3KPartner (v : ℕ) : Normal a b c := ⟨0, b - 1, v + 1, a_pos⟩
def m3KRoot (ha : 2 ≤ a) (v c : ℕ) : Normal a b c :=
  ⟨1, 0, m3D v c, by omega⟩

def m3KSocles (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b c) :=
  {m3KCore v, m3KPartner v, m3KRoot ha v c}

def m3KExpectedBorder (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b c) :=
  if h : a = 2 then
    {(⟨0, b + 1, 0, a_pos⟩ : Normal a b c),
      (⟨0, 0, v + 2, a_pos⟩ : Normal a b c),
      (⟨1, 1, 0, by omega⟩ : Normal a b c),
      (⟨0, b, v + 1, a_pos⟩ : Normal a b c),
      (⟨1, 0, m3D v c + 1, by omega⟩ : Normal a b c)}
  else
    {(⟨0, b + 1, 0, a_pos⟩ : Normal a b c),
      (⟨0, 0, v + 2, a_pos⟩ : Normal a b c),
      (⟨1, 1, 0, by omega⟩ : Normal a b c),
      (⟨2, 0, m3D v c, by omega⟩ : Normal a b c),
      (⟨1, 0, m3D v c + 1, by omega⟩ : Normal a b c)}

def m3KStandardNat (b c v x y z : ℕ) : Prop :=
  (y ≤ b ∧ z ≤ v ∧ (x = 0 ∨ (y + b ≤ b ∧ z + c ≤ v))) ∨
  (x = 0 ∧ y ≤ b - 1 ∧ z ≤ v + 1) ∨
  (x ≤ 1 ∧ y = 0 ∧ z ≤ m3D v c)

def m3KBorderNat (a b c v x y z : ℕ) : Prop :=
  (x = 0 ∧ y = b + 1 ∧ z = 0) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 2) ∨
  (x = 1 ∧ y = 1 ∧ z = 0) ∨
  ((a = 2 ∧ x = 0 ∧ y = b ∧ z = v + 1) ∨
   (a ≠ 2 ∧ x = 2 ∧ y = 0 ∧ z = m3D v c)) ∨
  (x = 1 ∧ y = 0 ∧ z = m3D v c + 1)

theorem mem_standardSet_m3K_iff (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hv : c ≤ v) (p : Normal a b c) :
    p ∈ standardSet (m3KSocles (a := a) (b := b) (c := c) ha v) ↔
      m3KStandardNat b c v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, m3KSocles, m3KCore, m3KPartner, m3KRoot,
    Normal.exact_divides_iff, Normal.DividesCriterion, m3KStandardNat, m3D]
  omega

theorem mem_m3KExpectedBorder_iff (ha : 2 ≤ a) (m : Normal a b c) :
    m ∈ m3KExpectedBorder (a := a) (b := b) (c := c) ha v ↔
      m3KBorderNat a b c v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases h : a = 2 <;>
    simp [m3KExpectedBorder, h, m3KBorderNat, Normal.mk.injEq]

set_option maxHeartbeats 6400000 in
theorem m3K_border_arithmetic (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : c ≤ v) (x y z : ℕ) (hxlt : x < a) :
    (¬m3KStandardNat b c v x y z ∧
      (if 0 < x then m3KStandardNat b c v (x - 1) y z
       else if b ≤ y ∧ c ≤ z then
         m3KStandardNat b c v (a - 1) (y - b) (z - c)
       else True) ∧
      (0 < y → m3KStandardNat b c v x (y - 1) z) ∧
      (0 < z → m3KStandardNat b c v x y (z - 1))) ↔
      m3KBorderNat a b c v x y z := by
  by_cases ha2 : a = 2 <;> by_cases hx : 0 < x <;>
    by_cases hby : b ≤ y <;> by_cases hcz : c ≤ z <;>
    by_cases hy : 0 < y <;> by_cases hz : 0 < z
  all_goals
    simp [ha2, hx, hby, hcz, hy, hz, m3KStandardNat, m3KBorderNat, m3D] <;>
      grind (splits := 32)

theorem m3K_border_exact (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : c ≤ v) :
    borderFinset (m3KSocles (a := a) (b := b) (c := c) ha v) =
      m3KExpectedBorder (a := a) (b := b) (c := c) ha v := by
  apply borderFinset_eq_expected_of_nat _ _ (m3KStandardNat b c v)
    (m3KBorderNat a b c v)
  · simp [m3KSocles]
  · exact mem_standardSet_m3K_iff ha hb hc hv
  · exact mem_m3KExpectedBorder_iff ha
  · exact m3K_border_arithmetic (v := v) ha hb hc hv

theorem m3K_border_card (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : c ≤ v) :
    (borderFinset (m3KSocles (a := a) (b := b) (c := c) ha v)).card = 5 := by
  rw [m3K_border_exact ha hb hc hv]
  by_cases h : a = 2 <;> simp [m3KExpectedBorder, h, m3D] <;> omega

theorem m3K_endpoint_xK (hb : 1 ≤ b) (hc : 1 ≤ c) (hv : c ≤ v)
    (ha2 : a = 2) :
    m3KRoot (a := a) (b := b) (by omega) v c *
        (Normal.xGenerator : Normal a b c) =
      (⟨0, b, v + 1, a_pos⟩ : Normal a b c) := by
  have hdiv : a / a = 1 := Nat.div_self (by omega)
  apply Normal.ext
  · simp [m3KRoot, Normal.xGenerator, show a ≠ 1 by omega, ha2]
  · simp [m3KRoot, Normal.xGenerator, show a ≠ 1 by omega, ha2, hdiv]
  · simp [m3KRoot, Normal.xGenerator, show a ≠ 1 by omega, ha2, hdiv, m3D]
    omega

/-! ## M4Y (`b=c=1`) -/

def m4YCore (ha : 2 ≤ a) (u v : ℕ) : Normal a 1 1 :=
  ⟨a - 1, u, v, by omega⟩
def m4YPartner (u v : ℕ) : Normal a 1 1 := ⟨0, u, v + 1, a_pos⟩
def m4YRoot (u : ℕ) : Normal a 1 1 := ⟨0, u + 1, 0, a_pos⟩

def m4YSocles (ha : 2 ≤ a) (u v : ℕ) : Finset (Normal a 1 1) :=
  {m4YCore ha u v, m4YPartner u v, m4YRoot u}

def m4YExpectedBorder (ha : 2 ≤ a) (u v : ℕ) : Finset (Normal a 1 1) :=
  {(⟨0, u + 2, 0, a_pos⟩ : Normal a 1 1),
    (⟨1, u + 1, 0, by omega⟩ : Normal a 1 1),
    (⟨0, u + 1, 1, a_pos⟩ : Normal a 1 1),
    (⟨0, 0, v + 2, a_pos⟩ : Normal a 1 1),
    (⟨1, 0, v + 1, by omega⟩ : Normal a 1 1)}

def m4YStandardNat (a u v x y z : ℕ) : Prop :=
  (y ≤ u ∧ z ≤ v) ∨
  (y ≤ u ∧ z ≤ v + 1 ∧ (x = 0 ∨ (y + 1 ≤ u ∧ z + 1 ≤ v + 1))) ∨
  (x = 0 ∧ y ≤ u + 1 ∧ z = 0)

def m4YBorderNat (u v x y z : ℕ) : Prop :=
  (x = 0 ∧ y = u + 2 ∧ z = 0) ∨
  (x = 1 ∧ y = u + 1 ∧ z = 0) ∨
  (x = 0 ∧ y = u + 1 ∧ z = 1) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 2) ∨
  (x = 1 ∧ y = 0 ∧ z = v + 1)

theorem mem_standardSet_m4Y_iff (ha : 2 ≤ a) (p : Normal a 1 1) :
    p ∈ standardSet (m4YSocles (a := a) ha u v) ↔
      m4YStandardNat a u v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, m4YSocles, m4YCore, m4YPartner, m4YRoot,
    Normal.exact_divides_iff, Normal.DividesCriterion, m4YStandardNat]
  omega

theorem mem_m4YExpectedBorder_iff (ha : 2 ≤ a) (m : Normal a 1 1) :
    m ∈ m4YExpectedBorder (a := a) ha u v ↔
      m4YBorderNat u v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  simp [m4YExpectedBorder, m4YBorderNat, Normal.mk.injEq]

set_option maxHeartbeats 6400000 in
theorem m4Y_border_arithmetic (ha : 2 ≤ a) (hu : 1 ≤ u)
    (x y z : ℕ) (hxlt : x < a) :
    (¬m4YStandardNat a u v x y z ∧
      (if 0 < x then m4YStandardNat a u v (x - 1) y z
       else if 1 ≤ y ∧ 1 ≤ z then
         m4YStandardNat a u v (a - 1) (y - 1) (z - 1)
       else True) ∧
      (0 < y → m4YStandardNat a u v x (y - 1) z) ∧
      (0 < z → m4YStandardNat a u v x y (z - 1))) ↔
      m4YBorderNat u v x y z := by
  by_cases hx : 0 < x <;> by_cases hy : 1 ≤ y <;> by_cases hz : 1 ≤ z
  all_goals
    simp [hx, hy, hz, Nat.lt_iff_add_one_le, m4YStandardNat, m4YBorderNat] <;>
      grind (splits := 32)

theorem m4Y_border_exact (ha : 2 ≤ a) (hu : 1 ≤ u) :
    borderFinset (m4YSocles (a := a) ha u v) =
      m4YExpectedBorder (a := a) ha u v := by
  apply borderFinset_eq_expected_of_nat _ _ (m4YStandardNat a u v)
    (m4YBorderNat u v)
  · simp [m4YSocles]
  · exact mem_standardSet_m4Y_iff ha
  · exact mem_m4YExpectedBorder_iff ha
  · exact m4Y_border_arithmetic (v := v) ha hu

theorem m4Y_border_card (ha : 2 ≤ a) (hu : 1 ≤ u) :
    (borderFinset (m4YSocles (a := a) ha u v)).card = 5 := by
  rw [m4Y_border_exact ha hu]
  simp [m4YExpectedBorder]

/-! ## M5Y and M5Z -/

def m5Core (ha : 2 ≤ a) (v : ℕ) : Normal a b c :=
  ⟨a - 1, 0, v, by omega⟩
def m5Partner (v c : ℕ) : Normal a b c :=
  ⟨0, b, v + c - 1, a_pos⟩
def m5YRoot : Normal a b c := ⟨0, b + 1, 0, a_pos⟩
def m5ZRoot (v c : ℕ) : Normal a b c := ⟨0, 0, v + c, a_pos⟩

def m5YSocles (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b c) :=
  {m5Core ha v, m5Partner v c, m5YRoot}
def m5ZSocles (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b c) :=
  {m5Core ha v, m5Partner v c, m5ZRoot v c}

def m5YExpectedBorder (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b c) :=
  if h : c = 1 then
    {(⟨0, b + 2, 0, a_pos⟩ : Normal a b c),
      (⟨0, 0, v + c, a_pos⟩ : Normal a b c),
      (⟨1, 1, 0, by omega⟩ : Normal a b c)}
  else
    {(⟨0, b + 2, 0, a_pos⟩ : Normal a b c),
      (⟨0, b + 1, 1, a_pos⟩ : Normal a b c),
      (⟨0, 0, v + c, a_pos⟩ : Normal a b c),
      (⟨1, 1, 0, by omega⟩ : Normal a b c),
      (⟨1, 0, v + 1, by omega⟩ : Normal a b c)}

def m5ZExpectedBorder (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b c) :=
  {(⟨0, b + 1, 0, a_pos⟩ : Normal a b c),
    (⟨0, 0, v + c + 1, a_pos⟩ : Normal a b c),
    (⟨0, 1, v + c, a_pos⟩ : Normal a b c),
    (⟨1, 1, 0, by omega⟩ : Normal a b c),
    (⟨1, 0, v + 1, by omega⟩ : Normal a b c)}

def m5YStandardNat (a b c v x y z : ℕ) : Prop :=
  (y = 0 ∧ z ≤ v) ∨
  (y ≤ b ∧ z ≤ v + c - 1 ∧
    (x = 0 ∨ (y + b ≤ b ∧ z + c ≤ v + c - 1))) ∨
  (x = 0 ∧ y ≤ b + 1 ∧ z = 0)

def m5ZStandardNat (a b c v x y z : ℕ) : Prop :=
  (y = 0 ∧ z ≤ v) ∨
  (y ≤ b ∧ z ≤ v + c - 1 ∧
    (x = 0 ∨ (y + b ≤ b ∧ z + c ≤ v + c - 1))) ∨
  (x = 0 ∧ y = 0 ∧ z ≤ v + c)

def m5YBorderNat (b c v x y z : ℕ) : Prop :=
  (x = 0 ∧ y = b + 2 ∧ z = 0) ∨
  (x = 0 ∧ y = 0 ∧ z = v + c) ∨
  (x = 1 ∧ y = 1 ∧ z = 0) ∨
  (c ≠ 1 ∧ ((x = 0 ∧ y = b + 1 ∧ z = 1) ∨
    (x = 1 ∧ y = 0 ∧ z = v + 1)))

def m5ZBorderNat (b c v x y z : ℕ) : Prop :=
  (x = 0 ∧ y = b + 1 ∧ z = 0) ∨
  (x = 0 ∧ y = 0 ∧ z = v + c + 1) ∨
  (x = 0 ∧ y = 1 ∧ z = v + c) ∨
  (x = 1 ∧ y = 1 ∧ z = 0) ∨
  (x = 1 ∧ y = 0 ∧ z = v + 1)

theorem mem_standardSet_m5Y_iff (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hv : 1 ≤ v) (p : Normal a b c) :
    p ∈ standardSet (m5YSocles (a := a) (b := b) (c := c) ha v) ↔
      m5YStandardNat a b c v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, m5YSocles, m5Core, m5Partner, m5YRoot,
    Normal.exact_divides_iff, Normal.DividesCriterion, m5YStandardNat]
  omega

theorem mem_standardSet_m5Z_iff (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hv : 1 ≤ v) (p : Normal a b c) :
    p ∈ standardSet (m5ZSocles (a := a) (b := b) (c := c) ha v) ↔
      m5ZStandardNat a b c v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, m5ZSocles, m5Core, m5Partner, m5ZRoot,
    Normal.exact_divides_iff, Normal.DividesCriterion, m5ZStandardNat]
  omega

theorem mem_m5YExpectedBorder_iff (ha : 2 ≤ a) (m : Normal a b c) :
    m ∈ m5YExpectedBorder (a := a) (b := b) (c := c) ha v ↔
      m5YBorderNat b c v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases h : c = 1 <;>
    simp [m5YExpectedBorder, h, m5YBorderNat, Normal.mk.injEq]
  aesop

theorem mem_m5ZExpectedBorder_iff (ha : 2 ≤ a) (m : Normal a b c) :
    m ∈ m5ZExpectedBorder (a := a) (b := b) (c := c) ha v ↔
      m5ZBorderNat b c v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  simp [m5ZExpectedBorder, m5ZBorderNat, Normal.mk.injEq]

set_option maxHeartbeats 6400000 in
theorem m5Y_border_arithmetic (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : 1 ≤ v) (x y z : ℕ) (hxlt : x < a) :
    (¬m5YStandardNat a b c v x y z ∧
      (if 0 < x then m5YStandardNat a b c v (x - 1) y z
       else if b ≤ y ∧ c ≤ z then
         m5YStandardNat a b c v (a - 1) (y - b) (z - c)
       else True) ∧
      (0 < y → m5YStandardNat a b c v x (y - 1) z) ∧
      (0 < z → m5YStandardNat a b c v x y (z - 1))) ↔
      m5YBorderNat b c v x y z := by
  by_cases hc1 : c = 1 <;> by_cases hx : 0 < x <;>
    by_cases hby : b ≤ y <;> by_cases hcz : c ≤ z <;>
    by_cases hy : 0 < y <;> by_cases hz : 0 < z
  all_goals
    simp [hc1, hx, hby, hcz, hy, hz, m5YStandardNat, m5YBorderNat] <;>
      grind (splits := 32)

set_option maxHeartbeats 6400000 in
theorem m5Z_border_arithmetic (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : 1 ≤ v) (x y z : ℕ) (hxlt : x < a) :
    (¬m5ZStandardNat a b c v x y z ∧
      (if 0 < x then m5ZStandardNat a b c v (x - 1) y z
       else if b ≤ y ∧ c ≤ z then
         m5ZStandardNat a b c v (a - 1) (y - b) (z - c)
       else True) ∧
      (0 < y → m5ZStandardNat a b c v x (y - 1) z) ∧
      (0 < z → m5ZStandardNat a b c v x y (z - 1))) ↔
      m5ZBorderNat b c v x y z := by
  by_cases hx : 0 < x <;> by_cases hby : b ≤ y <;>
    by_cases hcz : c ≤ z <;> by_cases hy : 0 < y <;> by_cases hz : 0 < z
  all_goals
    simp [hx, hby, hcz, hy, hz, m5ZStandardNat, m5ZBorderNat] <;>
      grind (splits := 32)

theorem m5Y_border_exact (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : 1 ≤ v) :
    borderFinset (m5YSocles (a := a) (b := b) (c := c) ha v) =
      m5YExpectedBorder (a := a) (b := b) (c := c) ha v := by
  apply borderFinset_eq_expected_of_nat _ _ (m5YStandardNat a b c v)
    (m5YBorderNat b c v)
  · simp [m5YSocles]
  · exact mem_standardSet_m5Y_iff ha hb hc hv
  · exact mem_m5YExpectedBorder_iff ha
  · exact m5Y_border_arithmetic (v := v) ha hb hc hv

theorem m5Z_border_exact (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : 1 ≤ v) :
    borderFinset (m5ZSocles (a := a) (b := b) (c := c) ha v) =
      m5ZExpectedBorder (a := a) (b := b) (c := c) ha v := by
  apply borderFinset_eq_expected_of_nat _ _ (m5ZStandardNat a b c v)
    (m5ZBorderNat b c v)
  · simp [m5ZSocles]
  · exact mem_standardSet_m5Z_iff ha hb hc hv
  · exact mem_m5ZExpectedBorder_iff ha
  · exact m5Z_border_arithmetic (v := v) ha hb hc hv

theorem m5Y_border_card (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : 1 ≤ v) :
    (borderFinset (m5YSocles (a := a) (b := b) (c := c) ha v)).card =
      if c = 1 then 3 else 5 := by
  rw [m5Y_border_exact ha hb hc hv]
  by_cases h : c = 1 <;> simp [m5YExpectedBorder, h] <;> omega

theorem m5Z_border_card (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hv : 1 ≤ v) :
    (borderFinset (m5ZSocles (a := a) (b := b) (c := c) ha v)).card = 5 := by
  rw [m5Z_border_exact ha hb hc hv]
  have hA : (⟨0, b + 1, 0, a_pos⟩ : Normal a b c) ∉
      ({(⟨0, 0, v + c + 1, a_pos⟩ : Normal a b c),
        (⟨0, 1, v + c, a_pos⟩ : Normal a b c),
        (⟨1, 1, 0, by omega⟩ : Normal a b c),
        (⟨1, 0, v + 1, by omega⟩ : Normal a b c)} : Finset (Normal a b c)) := by
    simp
    omega
  have hB : (⟨0, 0, v + c + 1, a_pos⟩ : Normal a b c) ∉
      ({(⟨0, 1, v + c, a_pos⟩ : Normal a b c),
        (⟨1, 1, 0, by omega⟩ : Normal a b c),
        (⟨1, 0, v + 1, by omega⟩ : Normal a b c)} : Finset (Normal a b c)) := by
    simp
  have hC : (⟨0, 1, v + c, a_pos⟩ : Normal a b c) ∉
      ({(⟨1, 1, 0, by omega⟩ : Normal a b c),
        (⟨1, 0, v + 1, by omega⟩ : Normal a b c)} : Finset (Normal a b c)) := by
    simp
  have hD : (⟨1, 1, 0, by omega⟩ : Normal a b c) ∉
      ({(⟨1, 0, v + 1, by omega⟩ : Normal a b c)} : Finset (Normal a b c)) := by
    simp
  rw [show m5ZExpectedBorder (a := a) (b := b) (c := c) ha v =
      {(⟨0, b + 1, 0, a_pos⟩ : Normal a b c),
        (⟨0, 0, v + c + 1, a_pos⟩ : Normal a b c),
        (⟨0, 1, v + c, a_pos⟩ : Normal a b c),
        (⟨1, 1, 0, by omega⟩ : Normal a b c),
        (⟨1, 0, v + 1, by omega⟩ : Normal a b c)} by rfl]
  rw [Finset.card_insert_of_notMem hA]
  rw [Finset.card_insert_of_notMem hB]
  rw [Finset.card_insert_of_notMem hC]
  rw [Finset.card_insert_of_notMem hD]
  simp

theorem m5Y_c_eq_one_redundancy_yz (ha : 2 ≤ a) (hc1 : c = 1) :
    (⟨0, b + 1, 1, a_pos⟩ : Normal a b c) =
      (⟨a - 1, 0, 0, by omega⟩ : Normal a b c) *
        (⟨1, 1, 0, by omega⟩ : Normal a b c) := by
  have hsum : a - 1 + 1 = a := by omega
  have hdiv : a / a = 1 := Nat.div_self (by omega)
  apply Normal.ext
  · simp [hsum]
  · simp [hsum, hdiv]
    omega
  · simp [hsum, hdiv, hc1]

theorem m5Y_c_eq_one_redundancy_xz (ha : 2 ≤ a) (hc1 : c = 1) :
    (⟨1, 0, v + 1, by omega⟩ : Normal a b c) =
      (⟨1, 0, v + c, by omega⟩ : Normal a b c) := by
  apply Normal.ext <;> simp [hc1]

/-! ## Pure P4Z and P5Z (`c=0`) -/

variable {V : ℕ}

def p4ZSocles (ha : 2 ≤ a) (V : ℕ) : Finset (Normal a b 0) :=
  {(⟨0, b, 0, a_pos⟩ : Normal a b 0),
    (⟨0, b - 1, V, a_pos⟩ : Normal a b 0),
    (⟨0, 0, V + 1, a_pos⟩ : Normal a b 0)}

def p5ZSocles (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b 0) :=
  {(⟨a - 1, 0, v, by omega⟩ : Normal a b 0),
    (⟨0, b, 0, a_pos⟩ : Normal a b 0),
    (⟨0, 0, v + 1, a_pos⟩ : Normal a b 0)}

def p4ZExpectedBorder (ha : 2 ≤ a) (V : ℕ) : Finset (Normal a b 0) :=
  {(⟨1, 1, 0, by omega⟩ : Normal a b 0),
    (⟨1, 0, 1, by omega⟩ : Normal a b 0),
    (⟨0, 0, V + 2, a_pos⟩ : Normal a b 0),
    (⟨0, 1, V + 1, a_pos⟩ : Normal a b 0)}

def p5ZExpectedBorder (ha : 2 ≤ a) (v : ℕ) : Finset (Normal a b 0) :=
  {(⟨1, 1, 0, by omega⟩ : Normal a b 0),
    (⟨0, 1, 1, a_pos⟩ : Normal a b 0),
    (⟨0, 0, v + 2, a_pos⟩ : Normal a b 0),
    (⟨1, 0, v + 1, by omega⟩ : Normal a b 0)}

def p4ZStandardNat (b V x y z : ℕ) : Prop :=
  (y ≤ b ∧ z = 0 ∧ (x = 0 ∨ y = 0)) ∨
  (x = 0 ∧ y ≤ b - 1 ∧ z ≤ V) ∨
  (x = 0 ∧ y = 0 ∧ z ≤ V + 1)

def p5ZStandardNat (b v x y z : ℕ) : Prop :=
  (y = 0 ∧ z ≤ v) ∨
  (y ≤ b ∧ z = 0 ∧ (x = 0 ∨ y = 0)) ∨
  (x = 0 ∧ y = 0 ∧ z ≤ v + 1)

def p4ZBorderNat (V x y z : ℕ) : Prop :=
  (x = 1 ∧ y = 1 ∧ z = 0) ∨ (x = 1 ∧ y = 0 ∧ z = 1) ∨
  (x = 0 ∧ y = 0 ∧ z = V + 2) ∨ (x = 0 ∧ y = 1 ∧ z = V + 1)

def p5ZBorderNat (v x y z : ℕ) : Prop :=
  (x = 1 ∧ y = 1 ∧ z = 0) ∨ (x = 0 ∧ y = 1 ∧ z = 1) ∨
  (x = 0 ∧ y = 0 ∧ z = v + 2) ∨ (x = 1 ∧ y = 0 ∧ z = v + 1)

theorem mem_standardSet_p4Z_iff (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hV : 1 ≤ V) (p : Normal a b 0) :
    p ∈ standardSet (p4ZSocles (a := a) (b := b) ha V) ↔
      p4ZStandardNat b V p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, p4ZSocles, Normal.exact_divides_iff,
    Normal.DividesCriterion, p4ZStandardNat]
  omega

theorem mem_standardSet_p5Z_iff (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hv : 1 ≤ v) (p : Normal a b 0) :
    p ∈ standardSet (p5ZSocles (a := a) (b := b) ha v) ↔
      p5ZStandardNat b v p.x p.y p.z := by
  rcases p with ⟨px, py, pz, hpx⟩
  simp [standardSet, p5ZSocles, Normal.exact_divides_iff,
    Normal.DividesCriterion, p5ZStandardNat]
  omega

theorem mem_p4ZExpectedBorder_iff (ha : 2 ≤ a) (m : Normal a b 0) :
    m ∈ p4ZExpectedBorder (a := a) (b := b) ha V ↔
      p4ZBorderNat V m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  simp [p4ZExpectedBorder, p4ZBorderNat, Normal.mk.injEq]

theorem mem_p5ZExpectedBorder_iff (ha : 2 ≤ a) (m : Normal a b 0) :
    m ∈ p5ZExpectedBorder (a := a) (b := b) ha v ↔
      p5ZBorderNat v m.x m.y m.z := by
  rcases m with ⟨mx, my, mz, hmx⟩
  simp [p5ZExpectedBorder, p5ZBorderNat, Normal.mk.injEq]

set_option maxHeartbeats 6400000 in
theorem p4Z_border_arithmetic (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V)
    (x y z : ℕ) (hxlt : x < a) :
    (¬p4ZStandardNat b V x y z ∧
      (if 0 < x then p4ZStandardNat b V (x - 1) y z
       else if b ≤ y ∧ 0 ≤ z then p4ZStandardNat b V (a - 1) (y - b) z
       else True) ∧
      (0 < y → p4ZStandardNat b V x (y - 1) z) ∧
      (0 < z → p4ZStandardNat b V x y (z - 1))) ↔ p4ZBorderNat V x y z := by
  by_cases hx : 0 < x <;> by_cases hby : b ≤ y <;>
    by_cases hy : 0 < y <;> by_cases hz : 0 < z
  all_goals
    simp [hx, hby, hy, hz, p4ZStandardNat, p4ZBorderNat] <;>
      grind (splits := 32)

set_option maxHeartbeats 6400000 in
theorem p5Z_border_arithmetic (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v)
    (x y z : ℕ) (hxlt : x < a) :
    (¬p5ZStandardNat b v x y z ∧
      (if 0 < x then p5ZStandardNat b v (x - 1) y z
       else if b ≤ y ∧ 0 ≤ z then p5ZStandardNat b v (a - 1) (y - b) z
       else True) ∧
      (0 < y → p5ZStandardNat b v x (y - 1) z) ∧
      (0 < z → p5ZStandardNat b v x y (z - 1))) ↔ p5ZBorderNat v x y z := by
  by_cases hx : 0 < x <;> by_cases hby : b ≤ y <;>
    by_cases hy : 0 < y <;> by_cases hz : 0 < z
  all_goals
    simp [hx, hby, hy, hz, p5ZStandardNat, p5ZBorderNat] <;>
      grind (splits := 32)

theorem p4Z_border_exact (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    borderFinset (p4ZSocles (a := a) (b := b) ha V) =
      p4ZExpectedBorder (a := a) (b := b) ha V := by
  apply borderFinset_eq_expected_of_nat _ _ (p4ZStandardNat b V) (p4ZBorderNat V)
  · simp [p4ZSocles]
  · exact mem_standardSet_p4Z_iff ha hb hV
  · exact mem_p4ZExpectedBorder_iff ha
  · exact p4Z_border_arithmetic (V := V) ha hb hV

theorem p5Z_border_exact (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    borderFinset (p5ZSocles (a := a) (b := b) ha v) =
      p5ZExpectedBorder (a := a) (b := b) ha v := by
  apply borderFinset_eq_expected_of_nat _ _ (p5ZStandardNat b v) (p5ZBorderNat v)
  · simp [p5ZSocles]
  · exact mem_standardSet_p5Z_iff ha hb hv
  · exact mem_p5ZExpectedBorder_iff ha
  · exact p5Z_border_arithmetic (v := v) ha hb hv

theorem p4Z_border_card (ha : 2 ≤ a) (hb : 2 ≤ b) (hV : 1 ≤ V) :
    (borderFinset (p4ZSocles (a := a) (b := b) ha V)).card = 4 := by
  rw [p4Z_border_exact ha hb hV]
  simp [p4ZExpectedBorder]

theorem p5Z_border_card (ha : 2 ≤ a) (hb : 2 ≤ b) (hv : 1 ≤ v) :
    (borderFinset (p5ZSocles (a := a) (b := b) ha v)).card = 4 := by
  rw [p5Z_border_exact ha hb hv]
  simp [p5ZExpectedBorder]

/-- The exact cards of all eight rows, without an exhaustion assertion.-/
structure NonDominantRowCardSummary : Prop where
  m2K : ∀ {a r u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hu : 1 ≤ u)
    (hv : 1 ≤ v) (hr : r ≤ a - 2),
    (borderFinset (m2KSocles ha r u v hr)).card = if r = a - 2 then 3 else 5
  m2Z : ∀ {a r u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hu : 1 ≤ u)
    (hv : 1 ≤ v) (hr : r ≤ a - 2), (borderFinset (m2ZSocles ha r u v hr)).card = 5
  m3K : ∀ {a b c v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hv : c ≤ v),
    (borderFinset (m3KSocles (b := b) (c := c) ha v)).card = 5
  m4Y : ∀ {a u v : ℕ} [NeZero a] (ha : 2 ≤ a) (hu : 1 ≤ u),
    (borderFinset (m4YSocles ha u v)).card = 5
  m5Y : ∀ {a b c v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hv : 1 ≤ v),
    (borderFinset (m5YSocles (b := b) (c := c) ha v)).card = if c = 1 then 3 else 5
  m5Z : ∀ {a b c v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 1 ≤ b)
    (hc : 1 ≤ c) (hv : 1 ≤ v),
    (borderFinset (m5ZSocles (b := b) (c := c) ha v)).card = 5
  p4Z : ∀ {a b V : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hV : 1 ≤ V), (borderFinset (p4ZSocles (b := b) ha V)).card = 4
  p5Z : ∀ {a b v : ℕ} [NeZero a] (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hv : 1 ≤ v), (borderFinset (p5ZSocles (b := b) ha v)).card = 4

theorem nonDominantRowCardSummary : NonDominantRowCardSummary :=
  ⟨m2K_border_card, m2Z_border_card, m3K_border_card, m4Y_border_card,
    m5Y_border_card, m5Z_border_card, p4Z_border_card, p5Z_border_card⟩

end P23.OneTie
