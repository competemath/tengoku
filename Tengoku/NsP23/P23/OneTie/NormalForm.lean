import Tengoku.Seed.Data.Nat.Basic
import Tengoku.Seed.Data.Nat.ModEq
import Tengoku.Seed.Algebra.Group.Defs
import Init.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace P23.OneTie

/-- A raw natural exponent triple `(x,y,z)`.-/
structure Raw where
  x : ℕ
  y : ℕ
  z : ℕ
deriving DecidableEq, Repr

namespace Raw

@[ext] theorem ext {p q : Raw} (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) :
    p = q := by
  cases p
  cases q
  simp_all

def add (p q : Raw) : Raw := ⟨p.x + q.x, p.y + q.y, p.z + q.z⟩
def zero : Raw := ⟨0, 0, 0⟩

instance : Add Raw := ⟨add⟩
instance : Zero Raw := ⟨zero⟩

instance : AddCommMonoid Raw where
  zero := zero
  add := add
  zero_add := by intro p; change add zero p = p; apply ext <;> simp [add, zero]
  add_zero := by intro p; change add p zero = p; apply ext <;> simp [add, zero]
  add_assoc := by
    intro p q r
    change add (add p q) r = add p (add q r)
    apply ext <;> simp [add, Nat.add_assoc]
  add_comm := by
    intro p q
    change add p q = add q p
    apply ext <;> simp [add, Nat.add_comm]
  nsmul := nsmulRec
  nsmul_zero := by intro p; rfl
  nsmul_succ := by intro n p; rfl

@[simp] theorem add_x (p q : Raw) : (p + q).x = p.x + q.x := rfl
@[simp] theorem add_y (p q : Raw) : (p + q).y = p.y + q.y := rfl
@[simp] theorem add_z (p q : Raw) : (p + q).z = p.z + q.z := rfl

end Raw

/-- Natural-exponent normal forms for the relation `x^a = y^b z^c`.-/
structure Normal (a b c : ℕ) where
  x : ℕ
  y : ℕ
  z : ℕ
  x_lt : x < a
deriving DecidableEq, Repr

namespace Normal

variable {a b c : ℕ}

@[ext] theorem ext {p q : Normal a b c}
    (hx : p.x = q.x) (hy : p.y = q.y) (hz : p.z = q.z) : p = q := by
  cases p
  cases q
  simp_all

def raw (p : Normal a b c) : Raw := ⟨p.x, p.y, p.z⟩

private theorem positive (a : ℕ) [NeZero a] : 0 < a :=
  Nat.pos_of_ne_zero (NeZero.ne a)

/-- Normalize a natural exponent triple by repeatedly replacing `x^a` by `y^b z^c`.-/
def normalize (a b c : ℕ) (ha : 0 < a) (p : Raw) : Normal a b c where
  x := p.x % a
  y := p.y + (p.x / a) * b
  z := p.z + (p.x / a) * c
  x_lt := Nat.mod_lt _ ha

@[simp] theorem normalize_x (ha : 0 < a) (p : Raw) :
    (normalize a b c ha p).x = p.x % a := rfl

@[simp] theorem normalize_y (ha : 0 < a) (p : Raw) :
    (normalize a b c ha p).y = p.y + (p.x / a) * b := rfl

@[simp] theorem normalize_z (ha : 0 < a) (p : Raw) :
    (normalize a b c ha p).z = p.z + (p.x / a) * c := rfl

@[simp] theorem normalize_raw (ha : 0 < a) (p : Normal a b c) :
    normalize a b c ha p.raw = p := by
  ext <;> simp [normalize, raw, Nat.mod_eq_of_lt p.x_lt, Nat.div_eq_of_lt p.x_lt]

private theorem div_normalize_add (ha : 0 < a) (m n : ℕ) :
    m / a + (m % a + n) / a = (m + n) / a := by
  simp only [Nat.add_div ha]
  have hm : m % a < a := Nat.mod_lt _ ha
  simp [Nat.div_eq_of_lt hm, Nat.mod_eq_of_lt hm, Nat.add_assoc]

/-- Normalizing the left summand before adding does not change the result.-/
theorem normalize_normalize_add (ha : 0 < a) (p q : Raw) :
    normalize a b c ha ((normalize a b c ha p).raw + q) =
      normalize a b c ha (p + q) := by
  apply Normal.ext
  · simp [normalize, raw, Nat.add_mod]
  · change (p.y + p.x / a * b + q.y) + (p.x % a + q.x) / a * b =
      p.y + q.y + (p.x + q.x) / a * b
    have hdiv := div_normalize_add (a := a) ha p.x q.x
    rw [← hdiv]
    simp only [Nat.add_mul]
    omega
  · change (p.z + p.x / a * c + q.z) + (p.x % a + q.x) / a * c =
      p.z + q.z + (p.x + q.x) / a * c
    have hdiv := div_normalize_add (a := a) ha p.x q.x
    rw [← hdiv]
    simp only [Nat.add_mul]
    omega

/-- Multiplication of normal forms is addition of exponents followed by normalization.-/
def mul [NeZero a] (p q : Normal a b c) : Normal a b c :=
  normalize a b c (positive a) (p.raw + q.raw)

def one [NeZero a] : Normal a b c := ⟨0, 0, 0, positive a⟩

instance [NeZero a] : CommMonoid (Normal a b c) where
  mul := mul
  one := one
  mul_assoc p q r := by
    change normalize a b c (positive a)
        ((normalize a b c (positive a) (p.raw + q.raw)).raw + r.raw) =
      normalize a b c (positive a)
        (p.raw + (normalize a b c (positive a) (q.raw + r.raw)).raw)
    rw [normalize_normalize_add]
    rw [show p.raw + (normalize a b c (positive a) (q.raw + r.raw)).raw =
        (normalize a b c (positive a) (q.raw + r.raw)).raw + p.raw by rw [add_comm]]
    rw [normalize_normalize_add]
    congr 1
    apply Raw.ext <;> simp [Nat.add_assoc, Nat.add_comm]
  one_mul p := by
    change normalize a b c (positive a) ((one (a := a) (b := b) (c := c)).raw + p.raw) = p
    rw [show (one (a := a) (b := b) (c := c)).raw + p.raw = p.raw by
      apply Raw.ext <;> simp [one, raw]]
    exact normalize_raw (a := a) (b := b) (c := c) (positive a) p
  mul_one p := by
    change normalize a b c (positive a) (p.raw + (one (a := a) (b := b) (c := c)).raw) = p
    rw [show p.raw + (one (a := a) (b := b) (c := c)).raw = p.raw by
      apply Raw.ext <;> simp [one, raw]]
    exact normalize_raw (a := a) (b := b) (c := c) (positive a) p
  mul_comm p q := by
    change normalize a b c (positive a) (p.raw + q.raw) =
      normalize a b c (positive a) (q.raw + p.raw)
    rw [add_comm]

@[simp] theorem one_x [NeZero a] : (1 : Normal a b c).x = 0 := rfl
@[simp] theorem one_y [NeZero a] : (1 : Normal a b c).y = 0 := rfl
@[simp] theorem one_z [NeZero a] : (1 : Normal a b c).z = 0 := rfl

@[simp] theorem mul_x [NeZero a] (p q : Normal a b c) :
    (p * q).x = (p.x + q.x) % a := rfl

@[simp] theorem mul_y [NeZero a] (p q : Normal a b c) :
    (p * q).y = p.y + q.y + ((p.x + q.x) / a) * b := rfl

@[simp] theorem mul_z [NeZero a] (p q : Normal a b c) :
    (p * q).z = p.z + q.z + ((p.x + q.x) / a) * c := rfl

/-- Left multiplication is injective in the normalized one-tie monoid.-/
theorem mul_left_cancel [NeZero a] {p q r : Normal a b c}
    (h : p * q = p * r) : q = r := by
  have hmod : Nat.ModEq a (p.x + q.x) (p.x + r.x) := congrArg Normal.x h
  have hqr : Nat.ModEq a q.x r.x := Nat.ModEq.add_left_cancel' p.x hmod
  have hx : q.x = r.x := by
    unfold Nat.ModEq at hqr
    simpa [Nat.mod_eq_of_lt q.x_lt, Nat.mod_eq_of_lt r.x_lt] using hqr
  have hy := congrArg Normal.y h
  have hz := congrArg Normal.z h
  apply Normal.ext hx
  · simp only [mul_y] at hy
    rw [hx] at hy
    omega
  · simp only [mul_z] at hz
    rw [hx] at hz
    omega

/-- Right multiplication is injective in the normalized one-tie monoid.-/
theorem mul_right_cancel [NeZero a] {p q r : Normal a b c}
    (h : q * p = r * p) : q = r := by
  rw [mul_comm q p, mul_comm r p] at h
  exact mul_left_cancel h

instance [NeZero a] : IsCancelMul (Normal a b c) where
  mul_left_cancel := fun _ _ _ h => mul_left_cancel h
  mul_right_cancel := fun _ _ _ h => mul_right_cancel h

/-- Normalization is idempotent after forgetting a normal form to raw exponents.-/
theorem normalize_idempotent [NeZero a] (p : Raw) :
    normalize a b c (positive a) (normalize a b c (positive a) p).raw =
      normalize a b c (positive a) p :=
  normalize_raw _ _

end Normal

end P23.OneTie
