import Tengoku.NsP23.P23.OneTie.NormalForm
import Tengoku.Seed.Data.Fintype.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.OneTie
namespace Normal

variable {a b c : ℕ} [NeZero a]

/-- Divisibility induced by multiplication in the normalized one-tie monoid.-/
instance : Dvd (Normal a b c) := ⟨fun p s => ∃ q, s = p * q⟩

/-- The coordinate criterion for divisibility in the normalized one-tie monoid.-/
def DividesCriterion (p s : Normal a b c) : Prop :=
  p.y ≤ s.y ∧ p.z ≤ s.z ∧
    (p.x ≤ s.x ∨ (p.y + b ≤ s.y ∧ p.z + c ≤ s.z))

/-- Actual monoid divisibility is exactly the ordinary-or-wrapped coordinate criterion.-/
theorem exact_divides_iff (p s : Normal a b c) :
    p ∣ s ↔ DividesCriterion p s := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  constructor
  · rintro ⟨q, rfl⟩
    unfold DividesCriterion
    have hp_lt := p.x_lt
    have hq_lt := q.x_lt
    have hsum_lt : p.x + q.x < 2 * a := by omega
    by_cases hnowrap : p.x + q.x < a
    · have hdiv : (p.x + q.x) / a = 0 := Nat.div_eq_of_lt hnowrap
      have hmod : (p.x + q.x) % a = p.x + q.x := Nat.mod_eq_of_lt hnowrap
      simp only [mul_x, mul_y, mul_z, hdiv, hmod, Nat.zero_mul, Nat.add_zero]
      exact ⟨by omega, by omega, Or.inl (by omega)⟩
    · have hdiv : (p.x + q.x) / a = 1 := by
        apply Nat.div_eq_of_lt_le
        · omega
        · omega
      have hdecomp := Nat.mod_add_div (p.x + q.x) a
      rw [hdiv] at hdecomp
      have hmod : (p.x + q.x) % a = p.x + q.x - a := by omega
      simp only [mul_x, mul_y, mul_z, hdiv, hmod, Nat.one_mul]
      exact ⟨by omega, by omega, Or.inr ⟨by omega, by omega⟩⟩
  · rintro ⟨hy, hz, hx⟩
    by_cases hordinary : p.x ≤ s.x
    · let q : Normal a b c :=
        ⟨s.x - p.x, s.y - p.y, s.z - p.z, by have := s.x_lt; omega⟩
      refine ⟨q, ?_⟩
      have hsum : p.x + q.x = s.x := by
        simpa [q] using Nat.add_sub_of_le hordinary
      have hdiv : (p.x + q.x) / a = 0 := by rw [hsum]; exact Nat.div_eq_of_lt s.x_lt
      have hmod : (p.x + q.x) % a = s.x := by rw [hsum]; exact Nat.mod_eq_of_lt s.x_lt
      apply Normal.ext
      · simp [hmod]
      · simp [q, hdiv]
        omega
      · simp [q, hdiv]
        omega
    · rcases hx with hx | hwrap
      · omega
      · let q : Normal a b c :=
          ⟨a + s.x - p.x, s.y - p.y - b, s.z - p.z - c, by omega⟩
        refine ⟨q, ?_⟩
        have hp_lt := p.x_lt
        have hsum : p.x + q.x = a + s.x := by simp [q]; omega
        have hsdiv : s.x / a = 0 := Nat.div_eq_of_lt s.x_lt
        have hsmod : s.x % a = s.x := Nat.mod_eq_of_lt s.x_lt
        have hdiv : (p.x + q.x) / a = 1 := by
          rw [hsum, Nat.add_div_left s.x ha, hsdiv]
        have hmod : (p.x + q.x) % a = s.x := by
          rw [hsum, Nat.add_mod_left, hsmod]
        apply Normal.ext
        · simp [hmod]
        · simp [q, hdiv]
          omega
        · simp [q, hdiv]
          omega

/-! Variable generators and predecessor lemmas. -/

def yGenerator : Normal a b c :=
  ⟨0, 1, 0, Nat.pos_of_ne_zero (NeZero.ne a)⟩

def zGenerator : Normal a b c :=
  ⟨0, 0, 1, Nat.pos_of_ne_zero (NeZero.ne a)⟩

/-- The normal form of the variable `x`. For `a = 1` this is `(0,b,c)`.-/
def xGenerator : Normal a b c :=
  if ha1 : a = 1 then
    ⟨0, b, c, by omega⟩
  else
    ⟨1, 0, 0, by
      have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
      omega⟩

def yPredecessor (p : Normal a b c) (_hy : 0 < p.y) : Normal a b c :=
  ⟨p.x, p.y - 1, p.z, p.x_lt⟩

def zPredecessor (p : Normal a b c) (_hz : 0 < p.z) : Normal a b c :=
  ⟨p.x, p.y, p.z - 1, p.x_lt⟩

def xPredecessor (p : Normal a b c) (hx : 0 < p.x) : Normal a b c :=
  ⟨p.x - 1, p.y, p.z, by have := p.x_lt; omega⟩

def wrappedXPredecessor (p : Normal a b c) (_hpx : p.x = 0)
    (_hy : b ≤ p.y) (_hz : c ≤ p.z) : Normal a b c :=
  ⟨a - 1, p.y - b, p.z - c, by
    have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
    omega⟩

theorem yPredecessor_mul (p : Normal a b c) (hy : 0 < p.y) :
    yPredecessor p hy * yGenerator = p := by
  have hdiv : p.x / a = 0 := Nat.div_eq_of_lt p.x_lt
  have hmod : p.x % a = p.x := Nat.mod_eq_of_lt p.x_lt
  apply Normal.ext
  · simp [yPredecessor, yGenerator, hmod]
  · simp [yPredecessor, yGenerator, hdiv]
    omega
  · simp [yPredecessor, yGenerator, hdiv]

theorem zPredecessor_mul (p : Normal a b c) (hz : 0 < p.z) :
    zPredecessor p hz * zGenerator = p := by
  have hdiv : p.x / a = 0 := Nat.div_eq_of_lt p.x_lt
  have hmod : p.x % a = p.x := Nat.mod_eq_of_lt p.x_lt
  apply Normal.ext
  · simp [zPredecessor, zGenerator, hmod]
  · simp [zPredecessor, zGenerator, hdiv]
  · simp [zPredecessor, zGenerator, hdiv]
    omega

theorem xPredecessor_mul (p : Normal a b c) (hx : 0 < p.x) :
    xPredecessor p hx * xGenerator = p := by
  have ha2 : 2 ≤ a := by have := p.x_lt; omega
  have ha1 : a ≠ 1 := by omega
  have hsum : p.x - 1 + 1 = p.x := by omega
  have hdiv : (p.x - 1 + 1) / a = 0 := by
    rw [hsum]
    exact Nat.div_eq_of_lt p.x_lt
  have hmod : (p.x - 1 + 1) % a = p.x := by
    rw [hsum]
    exact Nat.mod_eq_of_lt p.x_lt
  apply Normal.ext <;> simp [xPredecessor, xGenerator, ha1, hdiv, hmod]

theorem wrappedXPredecessor_mul (p : Normal a b c)
    (hpx : p.x = 0) (hy : b ≤ p.y) (hz : c ≤ p.z) :
    wrappedXPredecessor p hpx hy hz * xGenerator = p := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  by_cases ha1 : a = 1
  · subst a
    apply Normal.ext <;> simp [wrappedXPredecessor, xGenerator, hpx] <;> omega
  · have ha2 : 2 ≤ a := by omega
    have hsum : a - 1 + 1 = a := by omega
    have hdiv : (a - 1 + 1) / a = 1 := by simp [hsum, ha]
    have hmod : (a - 1 + 1) % a = 0 := by simp [hsum]
    apply Normal.ext
    · simp [wrappedXPredecessor, xGenerator, ha1, hmod, hpx]
    · simp [wrappedXPredecessor, xGenerator, ha1, hdiv]
      omega
    · simp [wrappedXPredecessor, xGenerator, ha1, hdiv]
      omega

theorem yPredecessor_unique (p : Normal a b c) (hy : 0 < p.y)
    (q : Normal a b c) (hq : q * yGenerator = p) : q = yPredecessor p hy := by
  have hxq : q.x = p.x := by
    have h := congrArg Normal.x hq
    simpa [yGenerator, Nat.mod_eq_of_lt q.x_lt] using h
  have hyq : q.y + 1 = p.y := by
    have h := congrArg Normal.y hq
    simpa [yGenerator, Nat.div_eq_of_lt q.x_lt] using h
  have hzq : q.z = p.z := by
    have h := congrArg Normal.z hq
    simpa [yGenerator, Nat.div_eq_of_lt q.x_lt] using h
  apply Normal.ext
  · simp [yPredecessor, hxq]
  · simp [yPredecessor]
    omega
  · simp [yPredecessor, hzq]

theorem zPredecessor_unique (p : Normal a b c) (hz : 0 < p.z)
    (q : Normal a b c) (hq : q * zGenerator = p) : q = zPredecessor p hz := by
  have hxq : q.x = p.x := by
    have h := congrArg Normal.x hq
    simpa [zGenerator, Nat.mod_eq_of_lt q.x_lt] using h
  have hyq : q.y = p.y := by
    have h := congrArg Normal.y hq
    simpa [zGenerator, Nat.div_eq_of_lt q.x_lt] using h
  have hzq : q.z + 1 = p.z := by
    have h := congrArg Normal.z hq
    simpa [zGenerator, Nat.div_eq_of_lt q.x_lt] using h
  apply Normal.ext
  · simp [zPredecessor, hxq]
  · simp [zPredecessor, hyq]
  · simp [zPredecessor]
    omega

theorem xPredecessor_unique (p : Normal a b c) (hx : 0 < p.x)
    (q : Normal a b c) (hq : q * xGenerator = p) : q = xPredecessor p hx := by
  have ha2 : 2 ≤ a := by have := p.x_lt; omega
  have ha1 : a ≠ 1 := by omega
  have hqx_lt := q.x_lt
  have hle : q.x + 1 ≤ a := by omega
  have hxcoord := congrArg Normal.x hq
  have hnowrap : q.x + 1 < a := by
    by_contra h
    have heq : q.x + 1 = a := by omega
    simp [xGenerator, ha1, heq] at hxcoord
    omega
  have hdiv : (q.x + 1) / a = 0 := Nat.div_eq_of_lt hnowrap
  have hmod : (q.x + 1) % a = q.x + 1 := Nat.mod_eq_of_lt hnowrap
  have hxq : q.x + 1 = p.x := by
    simpa [xGenerator, ha1, hmod] using hxcoord
  have hyq : q.y = p.y := by
    have h := congrArg Normal.y hq
    simpa [xGenerator, ha1, hdiv] using h
  have hzq : q.z = p.z := by
    have h := congrArg Normal.z hq
    simpa [xGenerator, ha1, hdiv] using h
  apply Normal.ext
  · simp [xPredecessor]
    omega
  · simp [xPredecessor, hyq]
  · simp [xPredecessor, hzq]

theorem wrappedXPredecessor_unique (p : Normal a b c)
    (hpx : p.x = 0) (hy : b ≤ p.y) (hz : c ≤ p.z)
    (q : Normal a b c) (hq : q * xGenerator = p) :
    q = wrappedXPredecessor p hpx hy hz := by
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  by_cases ha1 : a = 1
  · subst a
    have hqx : q.x = 0 := by have := q.x_lt; omega
    have hyq := congrArg Normal.y hq
    have hzq := congrArg Normal.z hq
    apply Normal.ext
    · simp [wrappedXPredecessor, hqx]
    · simp [xGenerator, hqx] at hyq
      simp [wrappedXPredecessor]
      omega
    · simp [xGenerator, hqx] at hzq
      simp [wrappedXPredecessor]
      omega
  · have ha2 : 2 ≤ a := by omega
    have hqx_lt := q.x_lt
    have hle : q.x + 1 ≤ a := by omega
    have hxcoord := congrArg Normal.x hq
    have hsum : q.x + 1 = a := by
      by_contra h
      have hlt : q.x + 1 < a := by omega
      have hmod : (q.x + 1) % a = q.x + 1 := Nat.mod_eq_of_lt hlt
      simp [xGenerator, ha1, hmod, hpx] at hxcoord
    have hdiv : (q.x + 1) / a = 1 := by simp [hsum, ha]
    have hyq : q.y + b = p.y := by
      have h := congrArg Normal.y hq
      simpa [xGenerator, ha1, hdiv] using h
    have hzq : q.z + c = p.z := by
      have h := congrArg Normal.z hq
      simpa [xGenerator, ha1, hdiv] using h
    apply Normal.ext
    · simp [wrappedXPredecessor]
      omega
    · simp [wrappedXPredecessor]
      omega
    · simp [wrappedXPredecessor]
      omega

theorem yGenerator_dvd_iff (p : Normal a b c) :
    yGenerator ∣ p ↔ 0 < p.y := by
  rw [exact_divides_iff]
  simp [DividesCriterion, yGenerator]
  omega

theorem zGenerator_dvd_iff (p : Normal a b c) :
    zGenerator ∣ p ↔ 0 < p.z := by
  rw [exact_divides_iff]
  simp [DividesCriterion, zGenerator]
  omega

theorem xGenerator_dvd_iff (p : Normal a b c) :
    xGenerator ∣ p ↔ 0 < p.x ∨ (b ≤ p.y ∧ c ≤ p.z) := by
  rw [exact_divides_iff]
  have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
  by_cases ha1 : a = 1
  · subst a
    have hpx : p.x = 0 := by have := p.x_lt; omega
    simp [DividesCriterion, xGenerator, hpx]
  · simp [DividesCriterion, xGenerator, ha1]
    omega

end Normal

/-- The three variable directions in the one-tie monoid.-/
inductive Direction where
  | x
  | y
  | z
deriving DecidableEq, Repr

namespace Direction

variable {a b c : ℕ} [NeZero a]

/-- The normalized variable generator belonging to a direction.-/
def generator : Direction → Normal a b c
  | .x => Normal.xGenerator
  | .y => Normal.yGenerator
  | .z => Normal.zGenerator

end Direction

namespace Normal

variable {a b c : ℕ} [NeZero a]

/-- The applicable immediate predecessor in a variable direction, if it exists.-/
def predecessor (e : Direction) (s : Normal a b c) : Option (Normal a b c) :=
  match e with
  | .x =>
      if hx : 0 < s.x then some (xPredecessor s hx)
      else if hw : b ≤ s.y ∧ c ≤ s.z then
        some (wrappedXPredecessor s (by omega) hw.1 hw.2)
      else none
  | .y =>
      if hy : 0 < s.y then some (yPredecessor s hy) else none
  | .z =>
      if hz : 0 < s.z then some (zPredecessor s hz) else none

@[simp] theorem predecessor_x_of_pos (s : Normal a b c) (hx : 0 < s.x) :
    predecessor .x s = some (xPredecessor s hx) := by
  simp [predecessor, hx]

@[simp] theorem predecessor_x_wrapped (s : Normal a b c) (hx : s.x = 0)
    (hy : b ≤ s.y) (hz : c ≤ s.z) :
    predecessor .x s = some (wrappedXPredecessor s hx hy hz) := by
  have hnot : ¬0 < s.x := by omega
  simp only [predecessor, hnot, dite_false, hy, hz, and_self, dite_true]

@[simp] theorem predecessor_x_none (s : Normal a b c) (hx : s.x = 0)
    (hw : ¬(b ≤ s.y ∧ c ≤ s.z)) : predecessor .x s = none := by
  have hnot : ¬0 < s.x := by omega
  simp [predecessor, hnot, hw]

@[simp] theorem predecessor_y_of_pos (s : Normal a b c) (hy : 0 < s.y) :
    predecessor .y s = some (yPredecessor s hy) := by
  simp [predecessor, hy]

@[simp] theorem predecessor_y_none (s : Normal a b c) (hy : s.y = 0) :
    predecessor .y s = none := by
  simp [predecessor, hy]

@[simp] theorem predecessor_z_of_pos (s : Normal a b c) (hz : 0 < s.z) :
    predecessor .z s = some (zPredecessor s hz) := by
  simp [predecessor, hz]

@[simp] theorem predecessor_z_none (s : Normal a b c) (hz : s.z = 0) :
    predecessor .z s = none := by
  simp [predecessor, hz]

omit [NeZero a] in
theorem x_predecessor_cases_exclusive (s : Normal a b c) :
    ¬(0 < s.x ∧ s.x = 0 ∧ b ≤ s.y ∧ c ≤ s.z) := by omega

/-- The predecessor interface returns exactly the unique factor by the variable generator.-/
theorem predecessor_eq_some_iff_mul (e : Direction) (s q : Normal a b c) :
    predecessor e s = some q ↔ q * e.generator = s := by
  constructor
  · intro h
    cases e with
    | x =>
        simp only [predecessor] at h
        split at h
        next hx =>
          simp only [Option.some.injEq] at h
          subst q
          exact xPredecessor_mul s hx
        next hx =>
          split at h
          next hw =>
            simp only [Option.some.injEq] at h
            subst q
            exact wrappedXPredecessor_mul s (by omega) hw.1 hw.2
          next => contradiction
    | y =>
        simp only [predecessor] at h
        split at h
        next hy =>
          simp only [Option.some.injEq] at h
          subst q
          exact yPredecessor_mul s hy
        next => contradiction
    | z =>
        simp only [predecessor] at h
        split at h
        next hz =>
          simp only [Option.some.injEq] at h
          subst q
          exact zPredecessor_mul s hz
        next => contradiction
  · intro h
    cases e with
    | x =>
        by_cases hx : 0 < s.x
        · rw [predecessor_x_of_pos s hx]
          congr
          exact (xPredecessor_unique s hx q h).symm
        · have hsx : s.x = 0 := by omega
          have hdvd : xGenerator ∣ s := by
            refine ⟨q, ?_⟩
            rw [mul_comm]
            exact h.symm
          have hw : b ≤ s.y ∧ c ≤ s.z := by
            rcases (xGenerator_dvd_iff s).1 hdvd with hpos | hwrap
            · omega
            · exact hwrap
          rw [predecessor_x_wrapped s hsx hw.1 hw.2]
          congr
          exact (wrappedXPredecessor_unique s hsx hw.1 hw.2 q h).symm
    | y =>
        have hy : 0 < s.y := by
          have hdvd : yGenerator ∣ s := by
            refine ⟨q, ?_⟩
            rw [mul_comm]
            exact h.symm
          exact (yGenerator_dvd_iff s).1 hdvd
        rw [predecessor_y_of_pos s hy]
        congr
        exact (yPredecessor_unique s hy q h).symm
    | z =>
        have hz : 0 < s.z := by
          have hdvd : zGenerator ∣ s := by
            refine ⟨q, ?_⟩
            rw [mul_comm]
            exact h.symm
          exact (zGenerator_dvd_iff s).1 hdvd
        rw [predecessor_z_of_pos s hz]
        congr
        exact (zPredecessor_unique s hz q h).symm

theorem predecessor_isSome_iff_dvd (e : Direction) (s : Normal a b c) :
    (predecessor e s).isSome ↔ e.generator ∣ s := by
  constructor
  · intro h
    rcases Option.isSome_iff_exists.mp h with ⟨q, hq⟩
    refine ⟨q, ?_⟩
    rw [mul_comm]
    exact (predecessor_eq_some_iff_mul e s q).1 hq |>.symm
  · rintro ⟨q, hq⟩
    apply Option.isSome_iff_exists.mpr
    refine ⟨q, (predecessor_eq_some_iff_mul e s q).2 ?_⟩
    rw [mul_comm]
    exact hq.symm

end Normal

/-- Public Run-01 checkpoint: actual monoid divisibility equals the exact criterion.-/
theorem exact_divides_iff {a b c : ℕ} [NeZero a]
    (p s : Normal a b c) : p ∣ s ↔ Normal.DividesCriterion p s :=
  Normal.exact_divides_iff p s

end P23.OneTie
