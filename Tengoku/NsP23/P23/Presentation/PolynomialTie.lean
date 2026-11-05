import Tengoku.NsP23.P23.Presentation.NormalMonoidAlgebra
import Tengoku.Seed.Algebra.MvPolynomial.Polynomial
import Tengoku.Seed.RingTheory.Polynomial.Ideal

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The public three-variable polynomial model and its normalized evaluation

The polynomial ring is genuinely `MvPolynomial (Fin 3) k`.  No quotient or
second exponent type is hidden in these definitions.
-/

namespace P23.Presentation

noncomputable section

open P23.OneTie
open scoped BigOperators

variable {k : Type*} [Field k]
variable {a b c : ℕ} [NeZero a]

/-- The public polynomial algebra `k[x,y,z]`.-/
abbrev ThreePoly (k : Type*) [Field k] := MvPolynomial (Fin 3) k

/-- The x variable in the public three-variable polynomial algebra.-/
def polyX : ThreePoly k := MvPolynomial.X 0

/-- The y variable in the public three-variable polynomial algebra.-/
def polyY : ThreePoly k := MvPolynomial.X 1

/-- The z variable in the public three-variable polynomial algebra.-/
def polyZ : ThreePoly k := MvPolynomial.X 2

/-- The unique defining tie polynomial.-/
def tiePolynomial (a b c : ℕ) : ThreePoly k :=
  polyX ^ a - polyY ^ b * polyZ ^ c

/-- Read a three-variable exponent as a raw exponent triple.-/
def exponentRaw (d : Fin 3 →₀ ℕ) : Raw :=
  ⟨d 0, d 1, d 2⟩

/-- Normalize a polynomial monomial exponent through the frozen one-tie
normalization.-/
def normalizeExponent (a b c : ℕ) [NeZero a] (d : Fin 3 →₀ ℕ) : Normal a b c :=
  Normal.normalize a b c (Nat.pos_of_ne_zero (NeZero.ne a)) (exponentRaw d)

/-- Re-encode a normalized exponent as a reduced three-variable exponent.-/
def normalExponent (p : Normal a b c) : Fin 3 →₀ ℕ :=
  Finsupp.single 0 p.x + Finsupp.single 1 p.y + Finsupp.single 2 p.z

@[simp] theorem normalExponent_x (p : Normal a b c) : normalExponent p 0 = p.x := by
  simp [normalExponent]

@[simp] theorem normalExponent_y (p : Normal a b c) : normalExponent p 1 = p.y := by
  simp [normalExponent]

@[simp] theorem normalExponent_z (p : Normal a b c) : normalExponent p 2 = p.z := by
  simp [normalExponent]

@[simp] theorem normalizeExponent_normalExponent (p : Normal a b c) :
    normalizeExponent a b c (normalExponent p) = p := by
  apply Normal.ext <;>
    simp [normalizeExponent, exponentRaw, Normal.normalize, Nat.mod_eq_of_lt p.x_lt,
      Nat.div_eq_of_lt p.x_lt]

private theorem add_div_remainders (m n a : ℕ) (ha : 0 < a) :
    m / a + n / a + (m % a + n % a) / a = (m + n) / a := by
  have hm : m % a < a := Nat.mod_lt _ ha
  have hn : n % a < a := Nat.mod_lt _ ha
  have hrem : (m % a + n % a) / a =
      if a ≤ m % a + n % a then 1 else 0 := by
    by_cases h : a ≤ m % a + n % a
    · rw [ite_eq_left h]
      exact Nat.div_eq_of_lt_le (k := 1) (by simpa using h) (by omega)
    · rw [ite_eq_right h]
      exact Nat.div_eq_of_lt (by omega)
  calc
    m / a + n / a + (m % a + n % a) / a =
        m / a + n / a + (if a ≤ m % a + n % a then 1 else 0) := by rw [hrem]
    _ = (m + n) / a := (Nat.add_div ha).symm

/-- Exponent addition is exactly frozen normalized-monoid multiplication.-/
theorem normalizeExponent_add (d e : Fin 3 →₀ ℕ) :
    normalizeExponent a b c (d + e) =
      normalizeExponent a b c d * normalizeExponent a b c e := by
  apply Normal.ext
  · simp [normalizeExponent, exponentRaw, Normal.mul, Normal.raw, Nat.add_mod]
  · simp only [normalizeExponent, exponentRaw, Normal.normalize_y, Finsupp.add_apply,
      Normal.mul_y, Normal.normalize_x]
    rw [← add_div_remainders (d 0) (e 0) a (Nat.pos_of_ne_zero (NeZero.ne a))]
    ring
  · simp only [normalizeExponent, exponentRaw, Normal.normalize_z, Finsupp.add_apply,
      Normal.mul_z, Normal.normalize_x]
    rw [← add_div_remainders (d 0) (e 0) a (Nat.pos_of_ne_zero (NeZero.ne a))]
    ring

@[simp] theorem normalizeExponent_zero :
    normalizeExponent a b c 0 = 1 := by
  apply Normal.ext <;> simp [normalizeExponent, exponentRaw, Normal.normalize]

@[simp] theorem normalizeExponent_single_x :
    normalizeExponent a b c (Finsupp.single 0 1) = Normal.xGenerator := by
  by_cases ha1 : a = 1
  · subst a
    apply Normal.ext <;>
      simp [normalizeExponent, exponentRaw, Normal.normalize, Normal.xGenerator]
  · have ha2 : 1 < a := by
      have ha : 0 < a := Nat.pos_of_ne_zero (NeZero.ne a)
      omega
    apply Normal.ext <;>
      simp [normalizeExponent, exponentRaw, Normal.normalize, Normal.xGenerator, ha1,
        Nat.mod_eq_of_lt ha2, Nat.div_eq_of_lt ha2]

@[simp] theorem normalizeExponent_single_y :
    normalizeExponent a b c (Finsupp.single 1 1) = Normal.yGenerator := by
  apply Normal.ext <;>
    simp [normalizeExponent, exponentRaw, Normal.normalize, Normal.yGenerator]

@[simp] theorem normalizeExponent_single_z :
    normalizeExponent a b c (Finsupp.single 2 1) = Normal.zGenerator := by
  apply Normal.ext <;>
    simp [normalizeExponent, exponentRaw, Normal.normalize, Normal.zGenerator]

/-- The normalized monomial assigned to a polynomial variable.-/
def normalizedVariable (i : Fin 3) : NormalMonoidAlgebra k a b c :=
  monomial (k := k) (normalizeExponent a b c (Finsupp.single i 1))

@[simp] theorem normalizedVariable_zero :
    normalizedVariable (k := k) (a := a) (b := b) (c := c) 0 =
      monomial (k := k) (Normal.xGenerator : Normal a b c) := by
  simp [normalizedVariable]

@[simp] theorem normalizedVariable_one :
    normalizedVariable (k := k) (a := a) (b := b) (c := c) 1 =
      monomial (k := k) (Normal.yGenerator : Normal a b c) := by
  simp [normalizedVariable]

@[simp] theorem normalizedVariable_two :
    normalizedVariable (k := k) (a := a) (b := b) (c := c) 2 =
      monomial (k := k) (Normal.zGenerator : Normal a b c) := by
  simp [normalizedVariable]

/-- The polynomial-to-normal-monoid-algebra homomorphism.-/
def polyToNormalAlg : ThreePoly k →ₐ[k] NormalMonoidAlgebra k a b c :=
  MvPolynomial.aeval (normalizedVariable (k := k) (a := a) (b := b) (c := c))

@[simp] theorem polyToNormalAlg_polyX :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c) polyX =
      monomial (k := k) (Normal.xGenerator : Normal a b c) := by
  simp [polyToNormalAlg, polyX]

@[simp] theorem polyToNormalAlg_polyY :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c) polyY =
      monomial (k := k) (Normal.yGenerator : Normal a b c) := by
  simp [polyToNormalAlg, polyY]

@[simp] theorem polyToNormalAlg_polyZ :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c) polyZ =
      monomial (k := k) (Normal.zGenerator : Normal a b c) := by
  simp [polyToNormalAlg, polyZ]

private theorem monomial_normalizeExponent_prod (d : Fin 3 →₀ ℕ) :
    d.prod (fun i n => normalizedVariable (k := k) (a := a) (b := b) (c := c) i ^ n) =
      monomial (k := k) (normalizeExponent a b c d) := by
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add d e hd he =>
      rw [Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
      simp [hd, he, normalizeExponent_add]
  | single i n =>
      rw [Finsupp.prod_single_index]
      · induction n with
        | zero => simp
        | succ n ih =>
            rw [pow_succ, ih]
            change monomial (k := k) (normalizeExponent a b c (Finsupp.single i n)) *
                monomial (k := k) (normalizeExponent a b c (Finsupp.single i 1)) = _
            rw [monomial_mul, ← normalizeExponent_add]
            congr 2
            ext j
            simp [Finsupp.single_apply, Nat.succ_eq_add_one]
      · simp

/-- Exact evaluation of an arbitrary polynomial monomial.-/
@[simp] theorem polyToNormalAlg_monomial (d : Fin 3 →₀ ℕ) (r : k) :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c)
        (MvPolynomial.monomial d r) =
      r • monomial (k := k) (normalizeExponent a b c d) := by
  rw [polyToNormalAlg, MvPolynomial.aeval_monomial]
  rw [monomial_normalizeExponent_prod]
  simp [Algebra.smul_def]

@[simp] theorem polyToNormalAlg_tiePolynomial :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c)
        (tiePolynomial (k := k) a b c) = 0 := by
  have hnorm :
      normalizeExponent a b c (Finsupp.single 0 a) =
        normalizeExponent a b c (Finsupp.single 1 b + Finsupp.single 2 c) := by
    apply Normal.ext <;>
      simp [normalizeExponent, exponentRaw, Normal.normalize,
        Nat.mod_eq_zero_of_dvd (dvd_refl a), Nat.div_self (Nat.pos_of_ne_zero (NeZero.ne a))]
  simp only [tiePolynomial, polyX, polyY, polyZ, map_sub, map_mul,
    MvPolynomial.X_pow_eq_monomial, polyToNormalAlg_monomial, one_smul]
  rw [monomial_mul, ← normalizeExponent_add, hnorm]
  simp

/-- Every normalized monomial has its reduced exponent monomial as a preimage.-/
theorem polyToNormalAlg_normalExponent (p : Normal a b c) :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c)
        (MvPolynomial.monomial (normalExponent p) (1 : k)) =
      monomial (k := k) p := by
  simp

/-- The polynomial map onto the normalized monoid algebra is surjective.-/
theorem polyToNormalAlg_surjective :
    Function.Surjective (polyToNormalAlg (k := k) (a := a) (b := b) (c := c)) := by
  intro f
  induction f using MonoidAlgebra.induction_linear with
  | zero => exact ⟨0, by simp⟩
  | add f g hf hg =>
      rcases hf with ⟨pf, rfl⟩
      rcases hg with ⟨pg, rfl⟩
      exact ⟨pf + pg, by simp⟩
  | single p r =>
      refine ⟨MvPolynomial.monomial (normalExponent p) r, ?_⟩
      simp [monomial, MonoidAlgebra.smul_single]

end

end P23.Presentation
