import Tengoku.NsP23.P23.OneTie.CoverGeometry
import Tengoku.Seed.Algebra.Algebra.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Finrank
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Defs
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.StrongRankCondition
import Tengoku.Seed.LinearAlgebra.Finsupp.VectorSpace

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite standard-monomial algebra

This module gives the frozen finite one-tie standard set a direct finite
algebra interpretation.  It does not identify that model with a polynomial
quotient.
--/

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {a b c : ℕ} [NeZero a]

/-- A nonempty selected-root set always has the unit monomial in its standard
set.-/
theorem one_mem_standardSet (S : Finset (Normal a b c)) (hS : S.Nonempty) :
    (1 : Normal a b c) ∈ standardSet S := by
  obtain ⟨s, hs⟩ := hS
  exact ⟨s, hs, one_dvd s⟩

/-- Finite-set form of `one_mem_standardSet`.-/
theorem one_mem_standardFinset (S : Finset (Normal a b c)) (hS : S.Nonempty) :
    (1 : Normal a b c) ∈ standardFinset S :=
  (mem_standardFinset_iff_standardSet S 1).2 (one_mem_standardSet S hS)

/-- The finite type indexing the surviving normal monomials.-/
abbrev MonomialIndex (S : Finset (Normal a b c)) :=
  {p : Normal a b c // p ∈ standardFinset S}

/-- Direct finite vector-space model on the surviving standard monomials.-/
structure MonomialArtin (k : Type*) [Field k]
    (S : Finset (Normal a b c)) where
  /-- Finitely supported coordinates in the standard-monomial basis.-/
  ofCoeff ::
  coeff : MonomialIndex S →₀ k

namespace MonomialArtin

variable {k : Type*} [Field k]
variable {S : Finset (Normal a b c)}

/-- Coordinate representation of the direct finite model.-/
def coeffEquiv (k : Type*) [Field k] (S : Finset (Normal a b c)) :
    MonomialArtin k S ≃ (MonomialIndex S →₀ k) where
  toFun := coeff
  invFun := ofCoeff
  left_inv _ := rfl
  right_inv _ := rfl

theorem coeff_injective :
    Function.Injective (coeff : MonomialArtin k S → MonomialIndex S →₀ k) :=
  (coeffEquiv k S).injective

@[ext]
theorem ext {x y : MonomialArtin k S} (h : x.coeff = y.coeff) : x = y :=
  coeff_injective h

instance : AddCommGroup (MonomialArtin k S) :=
  (coeffEquiv k S).addCommGroup

/-- Coordinate representation as an additive equivalence.-/
def coeffAddEquiv (k : Type*) [Field k] (S : Finset (Normal a b c)) :
    MonomialArtin k S ≃+ (MonomialIndex S →₀ k) :=
  (coeffEquiv k S).addEquiv

instance : Module k (MonomialArtin k S) :=
  (coeffAddEquiv k S).module k

/-- Coordinate representation as a linear equivalence.-/
def coeffLinearEquiv (k : Type*) [Field k] (S : Finset (Normal a b c)) :
    MonomialArtin k S ≃ₗ[k] (MonomialIndex S →₀ k) :=
  (coeffAddEquiv k S).linearEquiv k

@[simp] theorem coeff_zero :
    coeff (0 : MonomialArtin k S) = 0 := rfl

@[simp] theorem coeff_add (x y : MonomialArtin k S) :
    coeff (x + y) = coeff x + coeff y := rfl

@[simp] theorem coeff_neg (x : MonomialArtin k S) :
    coeff (-x) = -coeff x := rfl

@[simp] theorem coeff_smul (r : k) (x : MonomialArtin k S) :
    coeff (r • x) = r • coeff x := rfl

/-- Linear induction principle transported from finitely supported
coordinates.-/
@[elab_as_elim]
theorem induction_linear {P : MonomialArtin k S → Prop}
    (x : MonomialArtin k S) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (single : ∀ p r, P (.ofCoeff (Finsupp.single p r))) : P x := by
  change P (.ofCoeff x.coeff)
  induction x.coeff using Finsupp.induction_linear with
  | zero => exact zero
  | add x y hx hy => exact add (.ofCoeff x) (.ofCoeff y) hx hy
  | single p r => exact single p r

/-- A standard-monomial coordinate vector.-/
def X (S : Finset (Normal a b c)) (p : Normal a b c)
    (hp : p ∈ standardFinset S) : MonomialArtin k S :=
  .ofCoeff (Finsupp.single ⟨p, hp⟩ 1)

@[simp]
theorem coeff_X (S : Finset (Normal a b c)) (p : Normal a b c)
    (hp : p ∈ standardFinset S) (q : MonomialIndex S) :
    (X (k := k) S p hp).coeff q = if q.1 = p then 1 else 0 := by
  classical
  simp [X, Finsupp.single_apply, eq_comm, Subtype.ext_iff]

@[simp]
theorem smul_X (r : k) (S : Finset (Normal a b c)) (p : Normal a b c)
    (hp : p ∈ standardFinset S) :
    r • X (k := k) S p hp =
      .ofCoeff (Finsupp.single ⟨p, hp⟩ r) := by
  ext
  simp [X, Finsupp.single_apply]

/-- Truncated product of two basis indices.-/
def basisProduct (S : Finset (Normal a b c))
    (p q : MonomialIndex S) : MonomialArtin k S :=
  if h : p.1 * q.1 ∈ standardFinset S then X (k := k) S (p.1 * q.1) h else 0

/-- Bilinear extension of normalized multiplication, with products outside the
standard set killed.-/
def mul (x y : MonomialArtin k S) : MonomialArtin k S :=
  x.coeff.sum fun p rp ↦
    y.coeff.sum fun q rq ↦ (rp * rq) • basisProduct (k := k) S p q

instance : Mul (MonomialArtin k S) := ⟨mul⟩

theorem mul_def (x y : MonomialArtin k S) :
    x * y = x.coeff.sum fun p rp ↦
      y.coeff.sum fun q rq ↦ (rp * rq) • basisProduct (k := k) S p q := rfl

instance : NonUnitalNonAssocRing (MonomialArtin k S) where
  zero_mul := by simp [mul_def]
  mul_zero := by simp [mul_def]
  left_distrib := by
    classical
    intro x y z
    simp only [mul_def, coeff_add]
    rw [← Finsupp.sum_add]
    apply Finsupp.sum_congr
    intro p _
    rw [Finsupp.sum_add_index']
    · simp
    · intro q rq sq
      simp [mul_add, add_smul]
  right_distrib := by
    classical
    intro x y z
    simp only [mul_def, coeff_add]
    rw [Finsupp.sum_add_index']
    · simp
    · intro p rp sp
      simp [add_mul, add_smul, Finsupp.sum_add]

@[simp]
theorem X_mul_X (S : Finset (Normal a b c)) (p q : Normal a b c)
    (hp : p ∈ standardFinset S) (hq : q ∈ standardFinset S) :
    X (k := k) S p hp * X (k := k) S q hq =
      if h : p * q ∈ standardFinset S then X (k := k) S (p * q) h else 0 := by
  classical
  simp [mul_def, X, basisProduct]

theorem smul_mul_raw (r : k) (x y : MonomialArtin k S) :
    (r • x) * y = r • (x * y) := by
  classical
  simp only [mul_def, coeff_smul]
  rw [Finsupp.sum_smul_index (h0 := by simp)]
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro p _
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro q _
  rw [smul_smul]
  apply congrArg (fun t : k ↦ t • basisProduct (k := k) S p q)
  ring

theorem mul_smul_raw (r : k) (x y : MonomialArtin k S) :
    x * (r • y) = r • (x * y) := by
  classical
  simp only [mul_def, coeff_smul]
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro p _
  rw [Finsupp.sum_smul_index (h0 := by simp)]
  rw [Finsupp.smul_sum]
  apply Finsupp.sum_congr
  intro q _
  rw [smul_smul]
  apply congrArg (fun t : k ↦ t • basisProduct (k := k) S p q)
  ring

theorem mem_standardFinset_of_mul_mem_left (S : Finset (Normal a b c))
    {p q : Normal a b c} (h : p * q ∈ standardFinset S) :
    p ∈ standardFinset S := by
  rw [mem_standardFinset_iff_standardSet] at h ⊢
  exact standardSet_dvd_closed S h ⟨q, rfl⟩

theorem mem_standardFinset_of_mul_mem_right (S : Finset (Normal a b c))
    {p q : Normal a b c} (h : p * q ∈ standardFinset S) :
    q ∈ standardFinset S := by
  rw [mem_standardFinset_iff_standardSet] at h ⊢
  exact standardSet_dvd_closed S h ⟨p, by rw [mul_comm]⟩

private theorem X_mul_X_mul_X (S : Finset (Normal a b c))
    (p q r : MonomialIndex S) :
    (X (k := k) S p.1 p.2 * X (k := k) S q.1 q.2) * X (k := k) S r.1 r.2 =
      X (k := k) S p.1 p.2 * (X (k := k) S q.1 q.2 * X (k := k) S r.1 r.2) := by
  classical
  by_cases htotal : (p.1 * q.1) * r.1 ∈ standardFinset S
  · have hpq : p.1 * q.1 ∈ standardFinset S :=
      mem_standardFinset_of_mul_mem_left S htotal
    have hqr : q.1 * r.1 ∈ standardFinset S := by
      apply mem_standardFinset_of_mul_mem_right S (p := p.1)
      simpa [mul_assoc] using htotal
    simp [X_mul_X, hpq, hqr, htotal, mul_assoc]
  · have htotal' : p.1 * (q.1 * r.1) ∉ standardFinset S := by
      simpa [mul_assoc] using htotal
    by_cases hpq : p.1 * q.1 ∈ standardFinset S <;>
      by_cases hqr : q.1 * r.1 ∈ standardFinset S <;>
      simp [X_mul_X, hpq, hqr, htotal, htotal', mul_assoc]

private theorem X_mul_X_comm (S : Finset (Normal a b c))
    (p q : MonomialIndex S) :
    X (k := k) S p.1 p.2 * X (k := k) S q.1 q.2 =
      X (k := k) S q.1 q.2 * X (k := k) S p.1 p.2 := by
  classical
  simp [X_mul_X, mul_comm]

instance : NonUnitalRing (MonomialArtin k S) where
  mul_assoc := by
    classical
    intro x y z
    induction x using induction_linear with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂, add_mul]
    | single p rp =>
      induction y using induction_linear with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂, mul_add, add_mul]
      | single q rq =>
        induction z using induction_linear with
        | zero => simp
        | add z₁ z₂ hz₁ hz₂ => simp [hz₁, hz₂, mul_add, add_mul]
        | single r rr =>
          rw [← smul_X rp, ← smul_X rq, ← smul_X rr]
          simp only [smul_mul_raw, mul_smul_raw, smul_smul]
          convert
            congrArg (fun t : MonomialArtin k S ↦ (rp * rq * rr) • t)
              (X_mul_X_mul_X (k := k) S p q r) using 1 <;> ring_nf

instance : NonUnitalCommRing (MonomialArtin k S) where
  mul_comm := by
    classical
    intro x y
    induction x using induction_linear with
    | zero => simp
    | add x₁ x₂ hx₁ hx₂ => simp [hx₁, hx₂, add_mul, mul_add]
    | single p rp =>
      induction y using induction_linear with
      | zero => simp
      | add y₁ y₂ hy₁ hy₂ => simp [hy₁, hy₂, add_mul, mul_add]
      | single q rq =>
        rw [← smul_X rp, ← smul_X rq]
        simp only [smul_mul_raw, mul_smul_raw, smul_smul]
        rw [mul_comm rp rq, X_mul_X_comm]

/-- The unit is the unit basis vector when it survives, and the unique zero
element in the empty standard model otherwise.-/
def one (S : Finset (Normal a b c)) : MonomialArtin k S :=
  if h : (1 : Normal a b c) ∈ standardFinset S then X (k := k) S 1 h else 0

instance : One (MonomialArtin k S) := ⟨one (k := k) S⟩

theorem one_def : (1 : MonomialArtin k S) =
    if h : (1 : Normal a b c) ∈ standardFinset S then X (k := k) S 1 h else 0 := rfl

private theorem standardFinset_nonempty_of_index (p : MonomialIndex S) : S.Nonempty := by
  have hp := p.2
  rw [mem_standardFinset_iff] at hp
  rcases hp with ⟨s, hs, -⟩
  exact ⟨s, hs⟩

private theorem one_mul_X (p : MonomialIndex S) :
    (1 : MonomialArtin k S) * X (k := k) S p.1 p.2 = X (k := k) S p.1 p.2 := by
  have h1 := one_mem_standardFinset S (standardFinset_nonempty_of_index p)
  simp [one_def, h1, X_mul_X]

instance : NonAssocRing (MonomialArtin k S) where
  natCast n := n • (1 : MonomialArtin k S)
  natCast_zero := by simp
  natCast_succ n := by
    change (n + 1) • (1 : MonomialArtin k S) = n • 1 + 1
    rw [add_nsmul, one_nsmul]
  intCast z := match z with
    | .ofNat n => n • (1 : MonomialArtin k S)
    | .negSucc n => -((n + 1) • (1 : MonomialArtin k S))
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl
  one_mul := by
    classical
    intro x
    induction x using induction_linear with
    | zero => simp
    | add x y hx hy => simp [mul_add, hx, hy]
    | single p r =>
      rw [← smul_X r, mul_smul_raw, one_mul_X]
  mul_one := by
    classical
    intro x
    induction x using induction_linear with
    | zero => simp
    | add x y hx hy => simp [add_mul, hx, hy]
    | single p r =>
      rw [← smul_X r, smul_mul_raw, mul_comm, one_mul_X]

instance : Ring (MonomialArtin k S) where

instance : CommRing (MonomialArtin k S) where

theorem smul_mul_assoc' (r : k) (x y : MonomialArtin k S) :
    (r • x) * y = r • (x * y) := by
  exact smul_mul_raw r x y

theorem mul_smul_comm' (r : k) (x y : MonomialArtin k S) :
    x * (r • y) = r • (x * y) := by
  exact mul_smul_raw r x y

instance : Algebra k (MonomialArtin k S) :=
  Algebra.ofModule smul_mul_assoc' mul_smul_comm'

/-- The surviving unit basis vector is the algebra unit.-/
theorem X_one (S : Finset (Normal a b c)) (hS : S.Nonempty) :
    X (k := k) S 1 (one_mem_standardFinset S hS) = 1 := by
  simp [one_def, one_mem_standardFinset S hS]

/-- A standard monomial gives a nonzero basis vector.-/
theorem X_ne_zero (S : Finset (Normal a b c)) (p : Normal a b c)
    (hp : p ∈ standardFinset S) : X (k := k) S p hp ≠ 0 := by
  intro h
  have hc := congrArg (fun x : MonomialArtin k S ↦ x.coeff ⟨p, hp⟩) h
  simpa [coeff_X] using hc

/-- A monomial survives in the direct finite model precisely when it has a
nonzero standard basis vector.-/
def BasisSurvives (k : Type*) [Field k] (S : Finset (Normal a b c))
    (p : Normal a b c) : Prop :=
  ∃ hp : p ∈ standardFinset S, X (k := k) S p hp ≠ 0

theorem basisSurvives_iff (k : Type*) [Field k]
    (S : Finset (Normal a b c)) (p : Normal a b c) :
    BasisSurvives k S p ↔ p ∈ standardSet S := by
  constructor
  · rintro ⟨hp, -⟩
    exact (mem_standardFinset_iff_standardSet S p).1 hp
  · intro hp
    have hp' := (mem_standardFinset_iff_standardSet S p).2 hp
    exact ⟨hp', X_ne_zero (k := k) S p hp'⟩

/-- Exact bridge from the frozen live-tie predicate to survival and
nonvanishing of the x/y/z/tie basis elements.-/
theorem isLiveTie_iff_basisSurvives (k : Type*) [Field k]
    (S : Finset (Normal a b c)) :
    IsLiveTie S ↔
      BasisSurvives k S Normal.xGenerator ∧
      BasisSurvives k S Normal.yGenerator ∧
      BasisSurvives k S Normal.zGenerator ∧
      BasisSurvives k S liveTiePoint := by
  simp only [IsLiveTie, basisSurvives_iff]

/-- The canonical standard-monomial basis.-/
noncomputable def monomialBasis (k : Type*) [Field k]
    (S : Finset (Normal a b c)) :
    Module.Basis (MonomialIndex S) k (MonomialArtin k S) :=
  Finsupp.basisSingleOne.map (coeffLinearEquiv k S).symm

@[simp]
theorem monomialBasis_apply (S : Finset (Normal a b c)) (p : MonomialIndex S) :
    monomialBasis k S p = X (k := k) S p.1 p.2 := by
  rfl

/-- Every element has its unique finite standard-monomial expansion.-/
theorem basis_expansion (x : MonomialArtin k S) :
    x = x.coeff.sum fun p r ↦ r • X (k := k) S p.1 p.2 := by
  classical
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [coeff_add, Finsupp.sum_add_index']
      · exact congrArg₂ (fun u v : MonomialArtin k S ↦ u + v) hx hy
      · simp
      · intro p r s
        exact add_smul r s _
  | single p r =>
      rw [Finsupp.sum_single_index]
      · exact (smul_X r S p.1 p.2).symm
      · simp

/-- Dimension equals the number of surviving standard monomials.-/
theorem finrank_monomialArtin (k : Type*) [Field k]
    (S : Finset (Normal a b c)) :
    Module.finrank k (MonomialArtin k S) = (standardFinset S).card := by
  rw [Module.finrank_eq_card_basis (monomialBasis k S), Fintype.card_coe]

end MonomialArtin

export MonomialArtin (X X_mul_X X_one X_ne_zero BasisSurvives
  basisSurvives_iff isLiveTie_iff_basisSurvives monomialBasis basis_expansion
  finrank_monomialArtin)

end

end P23.Artin
