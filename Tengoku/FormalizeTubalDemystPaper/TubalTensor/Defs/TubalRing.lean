import Tengoku.FormalizeTubalDemystPaper.TubalTensor.Defs.VonNeumannRegular

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
  TubalTensor/Defs/TubalRing.lean
  Definition 10: Abstract tubal ring.

  A tubal ring is a multiplication on ℝⁿ making it a commutative, unital,
  von Neumann regular ℝ-algebra, where addition is the standard vector addition
  and scalar multiplication is the standard one.

  ## Design: The Type-Synonym Pattern

  `TubalCarrier n` is defined as a plain `def` (not `abbrev`) equal to `Fin n → ℝ`.
  This makes it:
  - **Term-level transparent**: `Pi.single`, `funext`, `Matrix.mulVec`, etc. all work
    because Lean unfolds `def`s during elaboration.
  - **Typeclass-opaque**: instances on `TubalCarrier n` (e.g., `CommRing`) do NOT leak
    to `Fin n → ℝ`, avoiding conflicts with the pointwise `CommRing` instance.

  This follows Mathlib's idiom for "same type, different algebra" (cf. `Multiplicative`,
  `OrderDual`, `MulOpposite`).
-/

namespace TubalTensor

/-- The carrier type for an abstract tubal ring of dimension `n`.
    Definitionally `Fin n → ℝ`, but a plain `def` (not `abbrev`) so that
    typeclass instances registered on `TubalCarrier n` do not leak to `Fin n → ℝ`
    and vice versa.-/
def TubalCarrier (n : ℕ) := Fin n → ℝ

/-! ## Transferred instances on `TubalCarrier n`

These give `TubalCarrier n` the additive group and ℝ-module structure inherited
from `Fin n → ℝ`. The instances are definitionally the same as those on `Fin n → ℝ`. -/

namespace TubalCarrier

variable {n : ℕ}

instance : Zero (TubalCarrier n) := inferInstanceAs (Zero (Fin n → ℝ))
instance : Add (TubalCarrier n) := inferInstanceAs (Add (Fin n → ℝ))
instance : Neg (TubalCarrier n) := inferInstanceAs (Neg (Fin n → ℝ))
instance : Sub (TubalCarrier n) := inferInstanceAs (Sub (Fin n → ℝ))
instance : SMul ℝ (TubalCarrier n) := inferInstanceAs (SMul ℝ (Fin n → ℝ))
instance : AddCommGroup (TubalCarrier n) := inferInstanceAs (AddCommGroup (Fin n → ℝ))
noncomputable instance : Module ℝ (TubalCarrier n) := inferInstanceAs (Module ℝ (Fin n → ℝ))

/--
@isnad1 id=eq.1h3v.s4.42c3a749c069 from=translated src=- shape=96557b98 vocab=1cf5c96f
-/
@[ext]
theorem ext {a b : TubalCarrier n} (h : ∀ i, a i = b i) : a = b :=
  funext h

/-! ### Simp lemmas for pointwise operations

These are needed because `simp` doesn't see through the `inferInstanceAs` wrapper
to apply `Pi.zero_apply`, `Pi.add_apply`, etc. This is the standard pattern for
type synonyms in Mathlib (cf. `Multiplicative`, `OrderDual`). -/

/--
@isnad1 id=eq.0h2v.s4.a86c1cf22e02 from=translated src=- shape=06057f13 vocab=1cf5c96f
-/
@[simp] theorem zero_apply (i : Fin n) : (0 : TubalCarrier n) i = 0 := rfl
/--
@isnad1 id=eq.0h4v.s5.85167124fea1 from=translated src=- shape=be8eec5f vocab=9953dd10
-/
@[simp] theorem add_apply (a b : TubalCarrier n) (i : Fin n) : (a + b) i = a i + b i := rfl
/--
@isnad1 id=eq.0h3v.s4.638dc7d9463b from=translated src=- shape=fbef95a5 vocab=34bc4fec
-/
@[simp] theorem neg_apply (a : TubalCarrier n) (i : Fin n) : (-a) i = -(a i) := rfl
/--
@isnad1 id=eq.0h4v.s5.56716361515c from=translated src=- shape=be8eec5f vocab=1f4d2f6f
-/
@[simp] theorem sub_apply (a b : TubalCarrier n) (i : Fin n) : (a - b) i = a i - b i := rfl
/--
@isnad1 id=eq.0h4v.s5.b059055a961b from=translated src=- shape=1384f9a5 vocab=f340f2b4
-/
@[simp] theorem smul_apply (r : ℝ) (a : TubalCarrier n) (i : Fin n) :
    (r • a) i = r * a i := rfl
/--
@isnad1 id=eq.0h5v.s5.410d4308c58d from=translated src=- shape=d5b2aaa8 vocab=f1f55ad2
-/
@[simp] theorem sum_apply {ι : Type*} (s : Finset ι) (f : ι → TubalCarrier n) (i : Fin n) :
    (∑ j ∈ s, f j) i = ∑ j ∈ s, f j i :=
  Finset.sum_apply i s f

end TubalCarrier

/-- **Definition 10**: A *tubal ring* of dimension `n` is a multiplication `mul` on
    `TubalCarrier n` (= `Fin n → ℝ`) with a unit element `one`, such that
    `(TubalCarrier n, +, mul)` is a commutative, unital, von Neumann regular,
    associative ℝ-algebra, where `+` is standard vector addition
    and scalar `•` is standard scalar-vector multiplication.-/
structure TubalRing (n : ℕ) where
  /-- The ring multiplication.-/
  mul : TubalCarrier n → TubalCarrier n → TubalCarrier n
  /-- The multiplicative identity.-/
  one : TubalCarrier n
  /-- Multiplication is associative.-/
  mul_assoc : ∀ a b c, mul (mul a b) c = mul a (mul b c)
  /-- Multiplication is commutative.-/
  mul_comm : ∀ a b, mul a b = mul b a
  /-- `one` is a left identity for multiplication.-/
  one_mul : ∀ a, mul one a = a
  /-- Left distributivity: `a · (b + c) = a · b + a · c`.-/
  left_distrib : ∀ a b c, mul a (b + c) = mul a b + mul a c
  /-- Zero is absorbing on the left: `0 · a = 0`.-/
  zero_mul : ∀ a, mul 0 a = 0
  /-- Scalar multiplication commutes with ring multiplication (ℝ-algebra axiom).-/
  smul_mul : ∀ (r : ℝ) a b, mul (r • a) b = r • (mul a b)
  /-- Von Neumann regularity: for every `a`, there exists `x` with `a · x · a = a`.-/
  vnr : ∀ a, ∃ x, mul (mul a x) a = a

namespace TubalRing

variable {n : ℕ} (tr : TubalRing n)

/-! ## Derived properties

These are proved BEFORE `toCommRing`/`toAlgebra` so that `tr.mul` is not normalized
to `*` notation during proof elaboration. -/

/-- `one` is a right identity for multiplication.
@isnad1 id=eq.0h3v.s4.3880391d1613 from=translated src=- shape=a4da848d vocab=ab696adf
-/
theorem mul_one (a : TubalCarrier n) : tr.mul a tr.one = a := by
  rw [tr.mul_comm]; exact tr.one_mul a

/-- Right distributivity: `(a + b) · c = a · c + b · c`.
@isnad1 id=eq.0h5v.s5.1a5e7fbc352e from=translated src=- shape=c94475c8 vocab=adf559aa
-/
theorem right_distrib (a b c : TubalCarrier n) :
    tr.mul (a + b) c = tr.mul a c + tr.mul b c := by
  rw [tr.mul_comm, tr.left_distrib, tr.mul_comm c a, tr.mul_comm c b]

/-- Zero is absorbing on the right: `a · 0 = 0`.
@isnad1 id=eq.0h3v.s5.2b47608d65bb from=translated src=- shape=62849e3d vocab=788a5e37
-/
theorem mul_zero (a : TubalCarrier n) : tr.mul a 0 = 0 := by
  rw [tr.mul_comm]; exact tr.zero_mul a

/-- Scalar multiplication commutes with ring multiplication on the right.
@isnad1 id=eq.0h5v.s5.78730e4adb3c from=translated src=- shape=4757dc0c vocab=f2b1e86c
-/
theorem mul_smul (r : ℝ) (a b : TubalCarrier n) :
    tr.mul a (r • b) = r • (tr.mul a b) := by
  rw [tr.mul_comm, tr.smul_mul, tr.mul_comm]

/-- The multiplication map `x ↦ a · x` is ℝ-linear.-/
def mulLeftLinear (a : TubalCarrier n) : TubalCarrier n →ₗ[ℝ] TubalCarrier n where
  toFun x := tr.mul a x
  map_add' b c := tr.left_distrib a b c
  map_smul' r b := by simp [tr.mul_smul]

/--
@isnad1 id=eq.0h4v.s6.3d79b45c8fa3 from=translated src=- shape=bf73d481 vocab=c6c8ac05
-/
@[simp]
theorem mulLeftLinear_apply (a x : TubalCarrier n) :
    tr.mulLeftLinear a x = tr.mul a x := rfl

/-- `p = a * x` is idempotent when `a * x * a = a`.
@isnad1 id=eq.1h4v.s5.2f3a1a881388 from=translated src=- shape=14ae6e73 vocab=788a5e37
-/
theorem mul_idempotent_of_vnr {a x : TubalCarrier n} (hx : tr.mul (tr.mul a x) a = a) :
    tr.mul (tr.mul a x) (tr.mul a x) = tr.mul a x := by
  rw [← tr.mul_assoc, hx]

/-- VNR refinement: from `a · x · a = a` we can get `y` satisfying both
    `a · y · a = a` and `y · a · y = y`.
@isnad1 id=ex.0h3v.s5.6a559ebe4826 from=translated src=- shape=4eee083b vocab=788a5e37
-/
theorem vnr_refined (a : TubalCarrier n) :
    ∃ x, tr.mul (tr.mul a x) a = a ∧ tr.mul (tr.mul x a) x = x := by
  obtain ⟨x, hx⟩ := tr.vnr a
  have hpa : tr.mul (tr.mul a x) a = a := hx
  have hpp : tr.mul (tr.mul a x) (tr.mul a x) = tr.mul a x :=
    tr.mul_idempotent_of_vnr hx
  have hxa : tr.mul x a = tr.mul a x := tr.mul_comm x a
  have hap : tr.mul a (tr.mul a x) = a := by rw [tr.mul_comm]; exact hpa
  refine ⟨tr.mul (tr.mul x a) x, ?_, ?_⟩
  · have h1 : tr.mul a (tr.mul (tr.mul x a) x) = tr.mul a (tr.mul (tr.mul a x) x) := by
      rw [hxa]
    have h2 : tr.mul a (tr.mul (tr.mul a x) x) = tr.mul (tr.mul a (tr.mul a x)) x := by
      rw [← tr.mul_assoc]
    have h3 : tr.mul a (tr.mul (tr.mul x a) x) = tr.mul a x := by
      rw [h1, h2, hap]
    calc tr.mul (tr.mul a (tr.mul (tr.mul x a) x)) a
        = tr.mul (tr.mul a x) a := by rw [h3]
      _ = a := hpa
  · have h1 : tr.mul (tr.mul (tr.mul x a) x) a = tr.mul (tr.mul (tr.mul a x) x) a := by
      rw [hxa]
    have h2 : tr.mul (tr.mul (tr.mul a x) x) a = tr.mul (tr.mul a x) (tr.mul x a) := by
      rw [tr.mul_assoc]
    have h3 : tr.mul (tr.mul a x) (tr.mul x a) = tr.mul (tr.mul a x) (tr.mul a x) := by
      rw [hxa]
    have hya : tr.mul (tr.mul (tr.mul x a) x) a = tr.mul a x := by
      rw [h1, h2, h3, hpp]
    have h4 : tr.mul (tr.mul a x) (tr.mul (tr.mul x a) x) =
              tr.mul (tr.mul a x) (tr.mul (tr.mul a x) x) := by rw [hxa]
    have h5 : tr.mul (tr.mul a x) (tr.mul (tr.mul a x) x) =
              tr.mul (tr.mul (tr.mul a x) (tr.mul a x)) x := by rw [← tr.mul_assoc]
    calc tr.mul (tr.mul (tr.mul (tr.mul x a) x) a) (tr.mul (tr.mul x a) x)
        = tr.mul (tr.mul a x) (tr.mul (tr.mul x a) x) := by rw [hya]
      _ = tr.mul (tr.mul (tr.mul a x) (tr.mul a x)) x := by rw [h4, h5]
      _ = tr.mul (tr.mul a x) x := by rw [hpp]
      _ = tr.mul (tr.mul x a) x := by rw [hxa]

/-- The weak inverse: the canonical choice satisfying both MP conditions.-/
noncomputable def weakInv (a : TubalCarrier n) : TubalCarrier n :=
  (tr.vnr_refined a).choose

/-! ## CommRing and Algebra instances

Defined AFTER all derived properties to avoid `tr.mul` being normalized to `*`
during proof elaboration of the properties above. -/

/-- The `CommRing` instance on `TubalCarrier n` induced by the tubal ring multiplication.
    This extends the transferred `AddCommGroup` so that there is only one additive
    structure derivation path.-/
@[reducible] noncomputable def toCommRing : CommRing (TubalCarrier n) :=
  { (inferInstance : AddCommGroup (TubalCarrier n)) with
    mul := tr.mul
    one := tr.one
    mul_assoc := tr.mul_assoc
    mul_comm := tr.mul_comm
    one_mul := tr.one_mul
    mul_one := tr.mul_one
    left_distrib := tr.left_distrib
    right_distrib := tr.right_distrib
    zero_mul := tr.zero_mul
    mul_zero := tr.mul_zero }

/-- The `Algebra ℝ` instance on `TubalCarrier n` induced by the tubal ring.
    Uses the SAME `Module ℝ` as the one transferred from `Fin n → ℝ`, so
    `Algebra.toModule` is definitionally equal to the transferred `Module ℝ`.
    This eliminates the typeclass diamond that plagued the old approach.-/
@[reducible] noncomputable def toAlgebra : @Algebra ℝ (TubalCarrier n) _
    tr.toCommRing.toSemiring :=
  @Algebra.ofModule ℝ (TubalCarrier n) _ tr.toCommRing.toSemiring
    (inferInstance : Module ℝ (TubalCarrier n))
    tr.smul_mul
    tr.mul_smul

end TubalRing

end TubalTensor
