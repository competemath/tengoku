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

/--
@isnad1 id=eq.0h4v.s6.8267133212c8 from=translated src=- shape=4597e60d vocab=67759eff
-/
@[simp] theorem normalExponent_x (p : Normal a b c) : normalExponent p 0 = p.x := by
  simp [normalExponent]

/--
@isnad1 id=eq.0h4v.s6.6cb5cf76197b from=translated src=- shape=4597e60d vocab=3887cbe0
-/
@[simp] theorem normalExponent_y (p : Normal a b c) : normalExponent p 1 = p.y := by
  simp [normalExponent]

/--
@isnad1 id=eq.0h4v.s6.3c4c83207136 from=translated src=- shape=4597e60d vocab=79df5118
-/
@[simp] theorem normalExponent_z (p : Normal a b c) : normalExponent p 2 = p.z := by
  simp [normalExponent]

/--
@isnad1 id=eq.0h4v.s5.7632f9ab7fb2 from=translated src=- shape=4074d063 vocab=1d4ae355
-/
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

/-- Exponent addition is exactly frozen normalized-monoid multiplication.
@isnad1 id=eq.0h5v.s7.1a8072a7b163 from=translated src=- shape=06e6b011 vocab=4d830cdb
-/
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

/--
@isnad1 id=eq.0h3v.s6.e69fd1fc0f1f from=translated src=- shape=79cb59f5 vocab=c7b6096e
-/
@[simp] theorem normalizeExponent_zero :
    normalizeExponent a b c 0 = 1 := by
  apply Normal.ext <;> simp [normalizeExponent, exponentRaw, Normal.normalize]

/--
@isnad1 id=eq.0h3v.s5.3bb9b097df82 from=translated src=- shape=631fc4c6 vocab=6647143f
-/
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

/--
@isnad1 id=eq.0h3v.s5.efe9b2f4e2d1 from=translated src=- shape=631fc4c6 vocab=4f3dabf6
-/
@[simp] theorem normalizeExponent_single_y :
    normalizeExponent a b c (Finsupp.single 1 1) = Normal.yGenerator := by
  apply Normal.ext <;>
    simp [normalizeExponent, exponentRaw, Normal.normalize, Normal.yGenerator]

/--
@isnad1 id=eq.0h3v.s5.133da8b7023a from=translated src=- shape=631fc4c6 vocab=6d3cba10
-/
@[simp] theorem normalizeExponent_single_z :
    normalizeExponent a b c (Finsupp.single 2 1) = Normal.zGenerator := by
  apply Normal.ext <;>
    simp [normalizeExponent, exponentRaw, Normal.normalize, Normal.zGenerator]

/-- The normalized monomial assigned to a polynomial variable.-/
def normalizedVariable (i : Fin 3) : NormalMonoidAlgebra k a b c :=
  monomial (k := k) (normalizeExponent a b c (Finsupp.single i 1))

/--
@isnad1 id=eq.0h4v.s5.c7a183a02840 from=translated src=- shape=65078e91 vocab=f57ec4b4
-/
@[simp] theorem normalizedVariable_zero :
    normalizedVariable (k := k) (a := a) (b := b) (c := c) 0 =
      monomial (k := k) (Normal.xGenerator : Normal a b c) := by
  simp [normalizedVariable]

/--
@isnad1 id=eq.0h4v.s5.c0c266b8a5be from=translated src=- shape=65078e91 vocab=1b53fb9e
-/
@[simp] theorem normalizedVariable_one :
    normalizedVariable (k := k) (a := a) (b := b) (c := c) 1 =
      monomial (k := k) (Normal.yGenerator : Normal a b c) := by
  simp [normalizedVariable]

/--
@isnad1 id=eq.0h4v.s5.190601f59334 from=translated src=- shape=65078e91 vocab=ed9ca4ce
-/
@[simp] theorem normalizedVariable_two :
    normalizedVariable (k := k) (a := a) (b := b) (c := c) 2 =
      monomial (k := k) (Normal.zGenerator : Normal a b c) := by
  simp [normalizedVariable]

/-- The polynomial-to-normal-monoid-algebra homomorphism.-/
def polyToNormalAlg : ThreePoly k →ₐ[k] NormalMonoidAlgebra k a b c :=
  MvPolynomial.aeval (normalizedVariable (k := k) (a := a) (b := b) (c := c))

/--
@isnad1 id=eq.0h4v.s8.9ee8369dc938 from=translated src=- shape=6c6a9f93 vocab=8adf0d3c
-/
@[simp] theorem polyToNormalAlg_polyX :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c) polyX =
      monomial (k := k) (Normal.xGenerator : Normal a b c) := by
  simp [polyToNormalAlg, polyX]

/--
@isnad1 id=eq.0h4v.s8.588266d86f64 from=translated src=- shape=6c6a9f93 vocab=854cb93c
-/
@[simp] theorem polyToNormalAlg_polyY :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c) polyY =
      monomial (k := k) (Normal.yGenerator : Normal a b c) := by
  simp [polyToNormalAlg, polyY]

/--
@isnad1 id=eq.0h4v.s8.d77fadf124d0 from=translated src=- shape=6c6a9f93 vocab=ac094a63
-/
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

/-- Exact evaluation of an arbitrary polynomial monomial.
@isnad1 id=eq.0h6v.s9.fe25e15232b2 from=translated src=- shape=b16a4481 vocab=0af0334c
-/
@[simp] theorem polyToNormalAlg_monomial (d : Fin 3 →₀ ℕ) (r : k) :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c)
        (MvPolynomial.monomial d r) =
      r • monomial (k := k) (normalizeExponent a b c d) := by
  rw [polyToNormalAlg, MvPolynomial.aeval_monomial]
  rw [monomial_normalizeExponent_prod]
  simp [Algebra.smul_def]

/--
@isnad1 id=eq.0h4v.s8.b2f82ea138ce from=translated src=- shape=789dc8f6 vocab=e6de72d9
-/
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

/-- Every normalized monomial has its reduced exponent monomial as a preimage.
@isnad1 id=eq.0h5v.s9.b774913f0b0b from=translated src=- shape=48356c3b vocab=a0e0a0b6
-/
theorem polyToNormalAlg_normalExponent (p : Normal a b c) :
    polyToNormalAlg (k := k) (a := a) (b := b) (c := c)
        (MvPolynomial.monomial (normalExponent p) (1 : k)) =
      monomial (k := k) p := by
  simp

/-- The polynomial map onto the normalized monoid algebra is surjective.
@isnad1 id=surjecti.0h4v.s8.64cbe87524c9 from=translated src=- shape=aad59161 vocab=5a3382fc
-/
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
