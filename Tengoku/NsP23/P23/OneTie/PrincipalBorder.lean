import Tengoku.NsP23.P23.OneTie.Border

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Phase 1: dominant principal-border geometry

This shared Run-03 layer contains only the symbolic principal-core border
formulas used by the dominant mixed and pure counts.  It does not introduce a
general theory of adjoining border socles.
-/

namespace P23.OneTie

variable {a b c r u v : ℕ} [NeZero a]

private theorem a_pos : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)

/-- A normal principal core `C=(r,u,v)`.-/
def mixedCore (r u v : ℕ) (hr : r < a) : Normal a b c :=
  ⟨r, u, v, hr⟩

/-- The vertical `y` border point `Y=y^(u+1)`.-/
def mixedY (u : ℕ) : Normal a b c :=
  ⟨0, u + 1, 0, a_pos⟩

/-- The vertical `z` border point `Z=z^(v+1)`.-/
def mixedZ (v : ℕ) : Normal a b c :=
  ⟨0, 0, v + 1, a_pos⟩

/-- The first horizontal border point `P=x^(r+1)y^(u+1-b)`.-/
def mixedP (r u : ℕ) (hr : r < a - 1) : Normal a b c :=
  ⟨r + 1, u + 1 - b, 0, by omega⟩

/-- The second horizontal border point `Q=x^(r+1)z^(v+1-c)`.-/
def mixedQ (r v : ℕ) (hr : r < a - 1) : Normal a b c :=
  ⟨r + 1, 0, v + 1 - c, by omega⟩

/-- On the last x-layer the mixed principal border is exactly `Y,Z`.-/
theorem mixedPrincipalBorder_last
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r = a - 1) :
    borderFinset ({mixedCore (a := a) (b := b) (c := c) r u v (by omega)} :
      Finset (Normal a b c)) =
      {mixedY (a := a) (b := b) (c := c) u,
        mixedZ (a := a) (b := b) (c := c) v} := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp)]
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hx : 0 < mx
  · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
      Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
      Normal.xPredecessor, Normal.yPredecessor,
      Normal.zPredecessor, mixedCore, mixedY, mixedZ, hx]
    omega
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · by_cases hcz : c ≤ mz
      · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
          Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
          Normal.wrappedXPredecessor, Normal.yPredecessor,
          Normal.zPredecessor, mixedCore, mixedY, mixedZ, hx0, hby, hcz]
        omega
      · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
          Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
          Normal.yPredecessor, Normal.zPredecessor, mixedCore, mixedY, mixedZ,
          hx0, hby, hcz]
        omega
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
        Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yPredecessor, Normal.zPredecessor, mixedCore, mixedY, mixedZ,
        hx0, hby]
      omega

/-- Below the last x-layer the mixed principal border is exactly `Y,Z,P,Q`.-/
theorem mixedPrincipalBorder_below
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    borderFinset ({mixedCore (a := a) (b := b) (c := c) r u v (by omega)} :
      Finset (Normal a b c)) =
      {mixedY (a := a) (b := b) (c := c) u,
        mixedZ (a := a) (b := b) (c := c) v,
        mixedP (a := a) (b := b) (c := c) r u hr,
        mixedQ (a := a) (b := b) (c := c) r v hr} := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp)]
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hx : 0 < mx
  · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
      Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
      Normal.xPredecessor, Normal.yPredecessor,
      Normal.zPredecessor, mixedCore, mixedY, mixedZ, mixedP, mixedQ, hx]
    omega
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · by_cases hcz : c ≤ mz
      · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
          Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
          Normal.wrappedXPredecessor, Normal.yPredecessor,
          Normal.zPredecessor, mixedCore, mixedY, mixedZ, mixedP, mixedQ,
          hx0, hby, hcz]
        omega
      · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
          Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
          Normal.yPredecessor, Normal.zPredecessor, mixedCore, mixedY, mixedZ,
          mixedP, mixedQ, hx0, hby, hcz]
        omega
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
        Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yPredecessor, Normal.zPredecessor, mixedCore, mixedY, mixedZ,
        mixedP, mixedQ, hx0, hby]
      omega

theorem mixedPrincipalBorder_last_card
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r = a - 1) :
    (borderFinset ({mixedCore (a := a) (b := b) (c := c) r u v (by omega)} :
      Finset (Normal a b c))).card = 2 := by
  rw [mixedPrincipalBorder_last ha hb hc hu hv hr]
  simp [mixedY, mixedZ]

theorem mixedPrincipalBorder_below_card
    (ha : 2 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (hu : b ≤ u) (hv : c ≤ v) (hr : r < a - 1) :
    (borderFinset ({mixedCore (a := a) (b := b) (c := c) r u v (by omega)} :
      Finset (Normal a b c))).card = 4 := by
  rw [mixedPrincipalBorder_below ha hb hc hu hv hr]
  have hPQ :
      mixedP (a := a) (b := b) (c := c) r u hr ≠
        mixedQ (a := a) (b := b) (c := c) r v hr := by
    intro heq
    have hy := congrArg Normal.y heq
    simp [mixedP, mixedQ] at hy
    omega
  have hY : mixedY (a := a) (b := b) (c := c) u ∉
      ({mixedZ (a := a) (b := b) (c := c) v,
        mixedP (a := a) (b := b) (c := c) r u hr,
        mixedQ (a := a) (b := b) (c := c) r v hr} :
          Finset (Normal a b c)) := by
    simp [mixedY, mixedZ, mixedP, mixedQ]
  have hZ : mixedZ (a := a) (b := b) (c := c) v ∉
      ({mixedP (a := a) (b := b) (c := c) r u hr,
        mixedQ (a := a) (b := b) (c := c) r v hr} :
          Finset (Normal a b c)) := by
    simp [mixedZ, mixedP, mixedQ]
  have hP : mixedP (a := a) (b := b) (c := c) r u hr ∉
      ({mixedQ (a := a) (b := b) (c := c) r v hr} :
        Finset (Normal a b c)) := by
    simpa using hPQ
  rw [Finset.card_insert_of_notMem hY]
  rw [Finset.card_insert_of_notMem hZ]
  rw [Finset.card_insert_of_notMem hP]
  simp

/-! ## Pure live-tie principal cores -/

/-- A pure principal core `C=(r,u,v)` for the tie `x^a=y^b`.-/
def pureCore (r u v : ℕ) (hr : r < a) : Normal a b 0 :=
  ⟨r, u, v, hr⟩

/-- The pure vertical border point `Z=z^(v+1)`.-/
def pureZ (v : ℕ) : Normal a b 0 :=
  ⟨0, 0, v + 1, a_pos⟩

/-- The horizontal pure border point.  Below the last x-layer it is
`x^(r+1)y^(u+1-b)`; on the last layer it is `y^(u+1)`.-/
def pureH (r u : ℕ) (hr : r < a) : Normal a b 0 :=
  if hbelow : r < a - 1 then
    ⟨r + 1, u + 1 - b, 0, by omega⟩
  else
    ⟨0, u + 1, 0, a_pos⟩

theorem purePrincipalBorder_below
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) (hr : r < a - 1) :
    borderFinset ({pureCore (a := a) (b := b) r u v (by omega)} :
      Finset (Normal a b 0)) =
      {pureH (a := a) (b := b) r u (by omega),
        pureZ (a := a) (b := b) v} := by
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp)]
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hx : 0 < mx
  · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
      Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
      Normal.xPredecessor, Normal.yPredecessor, Normal.zPredecessor,
      pureCore, pureH, pureZ, hx, hr]
    omega
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
        Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.wrappedXPredecessor, Normal.yPredecessor, Normal.zPredecessor,
        pureCore, pureH, pureZ, hx0, hby, hr]
      omega
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
        Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yPredecessor, Normal.zPredecessor, pureCore, pureH, pureZ,
        hx0, hby, hr]
      omega

theorem purePrincipalBorder_last
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b - 1 ≤ u) (hr : r = a - 1) :
    borderFinset ({pureCore (a := a) (b := b) r u v (by omega)} :
      Finset (Normal a b 0)) =
      {pureH (a := a) (b := b) r u (by omega),
        pureZ (a := a) (b := b) v} := by
  have hlast : ¬r < a - 1 := by omega
  apply Finset.ext
  intro m
  rw [mem_borderFinset_iff (by simp)]
  rcases m with ⟨mx, my, mz, hmx⟩
  by_cases hx : 0 < mx
  · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
      Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
      Normal.xPredecessor, Normal.yPredecessor, Normal.zPredecessor,
      pureCore, pureH, pureZ, hx, hlast]
    omega
  · have hx0 : mx = 0 := by omega
    by_cases hby : b ≤ my
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
        Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.wrappedXPredecessor, Normal.yPredecessor, Normal.zPredecessor,
        pureCore, pureH, pureZ, hx0, hby, hlast]
      omega
    · simp [IsMinimalBorder, ApplicablePredecessorsSurvive, standardSet,
        Normal.predecessor, Normal.exact_divides_iff, Normal.DividesCriterion,
        Normal.yPredecessor, Normal.zPredecessor, pureCore, pureH, pureZ,
        hx0, hby, hlast]
      omega

theorem purePrincipalBorder_below_card
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b ≤ u) (hr : r < a - 1) :
    (borderFinset ({pureCore (a := a) (b := b) r u v (by omega)} :
      Finset (Normal a b 0))).card = 2 := by
  rw [purePrincipalBorder_below ha hb hu hr]
  simp [pureH, pureZ, hr]

theorem purePrincipalBorder_last_card
    (ha : 2 ≤ a) (hb : 2 ≤ b) (hu : b - 1 ≤ u) (hr : r = a - 1) :
    (borderFinset ({pureCore (a := a) (b := b) r u v (by omega)} :
      Finset (Normal a b 0))).card = 2 := by
  rw [purePrincipalBorder_last ha hb hu hr]
  have hlast : ¬r < a - 1 := by omega
  simp [pureH, pureZ, hlast]

/-- At `r=a-2`, multiplication of the horizontal point by `x` wraps through
the pure tie and gives `y^(u+1)`; it is not an accidental redundancy.-/
theorem pure_xH_endpoint
    (ha : 2 ≤ a) (_hb : 2 ≤ b) (hu : b ≤ u) (hr : r = a - 2) :
    pureH (a := a) (b := b) r u (by omega) *
        (Normal.xGenerator : Normal a b 0) =
      mixedY (a := a) (b := b) (c := 0) u := by
  have hbelow : r < a - 1 := by omega
  have ha1 : a ≠ 1 := by omega
  have hsum : r + 1 + 1 = a := by omega
  have hdiv : a / a = 1 := Nat.div_self (by omega)
  apply Normal.ext
  · simp [pureH, hbelow, Normal.xGenerator, ha1, hsum, mixedY]
  · simp [pureH, hbelow, Normal.xGenerator, ha1, hsum, hdiv, mixedY]
    omega
  · simp [pureH, hbelow, Normal.xGenerator, ha1, hsum, mixedY]

end P23.OneTie
