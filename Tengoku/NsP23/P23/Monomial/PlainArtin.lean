import Tengoku.NsP23.P23.Monomial.PlainGeometry
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Ordinary finite standard-monomial algebra. No tie relation is used.
The coefficient-space construction follows the accepted Run07 architecture. -/
namespace P23.Monomial
noncomputable section
local instance plainArtinDecidable (p : Prop) : Decidable p := Classical.propDecidable p

theorem zero_mem_plainStandardFinset (S : Finset PlainExp) (hS : S.Nonempty) :
    (0 : PlainExp) ∈ plainStandardFinset S :=
  (mem_plainStandardFinset S 0).mpr (plain_zero_mem_standard S hS)

/-- The finite type indexing the surviving normal monomials.-/
abbrev PlainMonomialIndex (S : Finset (PlainExp)) :=
  {p : PlainExp // p ∈ plainStandardFinset S}

/-- Direct finite vector-space model on the surviving standard monomials.-/
structure PlainMonomialArtin (k : Type*) [Field k]
    (S : Finset (PlainExp)) where
  /-- Finitely supported coordinates in the standard-monomial basis.-/
  ofCoeff ::
  coeff : PlainMonomialIndex S →₀ k

namespace PlainMonomialArtin

variable {k : Type*} [Field k]
variable {S : Finset (PlainExp)}

/-- Coordinate representation of the direct finite model.-/
def coeffEquiv (k : Type*) [Field k] (S : Finset (PlainExp)) :
    PlainMonomialArtin k S ≃ (PlainMonomialIndex S →₀ k) where
  toFun := coeff
  invFun := ofCoeff
  left_inv _ := rfl
  right_inv _ := rfl

theorem coeff_injective :
    Function.Injective (coeff : PlainMonomialArtin k S → PlainMonomialIndex S →₀ k) :=
  (coeffEquiv k S).injective

@[ext]
theorem ext {x y : PlainMonomialArtin k S} (h : x.coeff = y.coeff) : x = y :=
  coeff_injective h

instance : AddCommGroup (PlainMonomialArtin k S) :=
  (coeffEquiv k S).addCommGroup

/-- Coordinate representation as an additive equivalence.-/
def coeffAddEquiv (k : Type*) [Field k] (S : Finset (PlainExp)) :
    PlainMonomialArtin k S ≃+ (PlainMonomialIndex S →₀ k) :=
  (coeffEquiv k S).addEquiv

instance : Module k (PlainMonomialArtin k S) :=
  (coeffAddEquiv k S).module k

/-- Coordinate representation as a linear equivalence.-/
def coeffLinearEquiv (k : Type*) [Field k] (S : Finset (PlainExp)) :
    PlainMonomialArtin k S ≃ₗ[k] (PlainMonomialIndex S →₀ k) :=
  (coeffAddEquiv k S).linearEquiv k

@[simp] theorem coeff_zero :
    coeff (0 : PlainMonomialArtin k S) = 0 := rfl

@[simp] theorem coeff_add (x y : PlainMonomialArtin k S) :
    coeff (x + y) = coeff x + coeff y := rfl

@[simp] theorem coeff_neg (x : PlainMonomialArtin k S) :
    coeff (-x) = -coeff x := rfl

@[simp] theorem coeff_smul (r : k) (x : PlainMonomialArtin k S) :
    coeff (r • x) = r • coeff x := rfl

/-- Linear induction principle transported from finitely supported
coordinates.-/
@[elab_as_elim]
theorem induction_linear {P : PlainMonomialArtin k S → Prop}
    (x : PlainMonomialArtin k S) (zero : P 0)
    (add : ∀ x y, P x → P y → P (x + y))
    (single : ∀ p r, P (.ofCoeff (Finsupp.single p r))) : P x := by
  change P (.ofCoeff x.coeff)
  induction x.coeff using Finsupp.induction_linear with
  | zero => exact zero
  | add x y hx hy => exact add (.ofCoeff x) (.ofCoeff y) hx hy
  | single p r => exact single p r

/-- A standard-monomial coordinate vector.-/
def PX (S : Finset (PlainExp)) (p : PlainExp)
    (hp : p ∈ plainStandardFinset S) : PlainMonomialArtin k S :=
  .ofCoeff (Finsupp.single ⟨p, hp⟩ 1)

@[simp]
theorem coeff_PX (S : Finset (PlainExp)) (p : PlainExp)
    (hp : p ∈ plainStandardFinset S) (q : PlainMonomialIndex S) :
    (PX (k := k) S p hp).coeff q = if q.1 = p then 1 else 0 := by
  classical
  simp [PX, Finsupp.single_apply, eq_comm, Subtype.ext_iff]

@[simp]
theorem smul_PX (r : k) (S : Finset (PlainExp)) (p : PlainExp)
    (hp : p ∈ plainStandardFinset S) :
    r • PX (k := k) S p hp =
      .ofCoeff (Finsupp.single ⟨p, hp⟩ r) := by
  ext
  simp [PX, Finsupp.single_apply]

/-- Truncated product of two basis indices.-/
def basisProduct (S : Finset (PlainExp))
    (p q : PlainMonomialIndex S) : PlainMonomialArtin k S :=
  if h : p.1 + q.1 ∈ plainStandardFinset S then PX (k := k) S (p.1 + q.1) h else 0

/-- Bilinear extension of ordinary exponent addition, with products outside the
standard set killed.-/
def mul (x y : PlainMonomialArtin k S) : PlainMonomialArtin k S :=
  x.coeff.sum fun p rp ↦
    y.coeff.sum fun q rq ↦ (rp * rq) • basisProduct (k := k) S p q

instance : Mul (PlainMonomialArtin k S) := ⟨mul⟩

theorem mul_def (x y : PlainMonomialArtin k S) :
    x * y = x.coeff.sum fun p rp ↦
      y.coeff.sum fun q rq ↦ (rp * rq) • basisProduct (k := k) S p q := rfl

instance : NonUnitalNonAssocRing (PlainMonomialArtin k S) where
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
theorem PX_mul_PX (S : Finset (PlainExp)) (p q : PlainExp)
    (hp : p ∈ plainStandardFinset S) (hq : q ∈ plainStandardFinset S) :
    PX (k := k) S p hp * PX (k := k) S q hq =
      if h : p + q ∈ plainStandardFinset S then PX (k := k) S (p + q) h else 0 := by
  classical
  simp [mul_def, PX, basisProduct]

theorem smul_mul_raw (r : k) (x y : PlainMonomialArtin k S) :
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

theorem mul_smul_raw (r : k) (x y : PlainMonomialArtin k S) :
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

theorem mem_plainStandardFinset_of_add_mem_left (S : Finset (PlainExp))
    {p q : PlainExp} (h : p + q ∈ plainStandardFinset S) :
    p ∈ plainStandardFinset S := by
  rw [mem_plainStandardFinset] at h ⊢
  exact plainStandard_downward S h (fun j => Nat.le_add_right _ _)

theorem mem_plainStandardFinset_of_add_mem_right (S : Finset (PlainExp))
    {p q : PlainExp} (h : p + q ∈ plainStandardFinset S) :
    q ∈ plainStandardFinset S := by
  rw [mem_plainStandardFinset] at h ⊢
  exact plainStandard_downward S h (fun j => Nat.le_add_left _ _)

private theorem PX_mul_PX_mul_PX (S : Finset (PlainExp))
    (p q r : PlainMonomialIndex S) :
    (PX (k := k) S p.1 p.2 * PX (k := k) S q.1 q.2) * PX (k := k) S r.1 r.2 =
      PX (k := k) S p.1 p.2 * (PX (k := k) S q.1 q.2 * PX (k := k) S r.1 r.2) := by
  classical
  by_cases htotal : (p.1 + q.1) + r.1 ∈ plainStandardFinset S
  · have hpq : p.1 + q.1 ∈ plainStandardFinset S :=
      mem_plainStandardFinset_of_add_mem_left S htotal
    have hqr : q.1 + r.1 ∈ plainStandardFinset S := by
      apply mem_plainStandardFinset_of_add_mem_right S (p := p.1)
      simpa [add_assoc] using htotal
    simp [PX_mul_PX, hpq, hqr, htotal, add_assoc]
  · have htotal' : p.1 + (q.1 + r.1) ∉ plainStandardFinset S := by
      simpa [add_assoc] using htotal
    by_cases hpq : p.1 + q.1 ∈ plainStandardFinset S <;>
      by_cases hqr : q.1 + r.1 ∈ plainStandardFinset S <;>
      simp [PX_mul_PX, hpq, hqr, htotal, htotal', add_assoc]

private theorem PX_mul_PX_comm (S : Finset (PlainExp))
    (p q : PlainMonomialIndex S) :
    PX (k := k) S p.1 p.2 * PX (k := k) S q.1 q.2 =
      PX (k := k) S q.1 q.2 * PX (k := k) S p.1 p.2 := by
  classical
  simp [PX_mul_PX, add_comm]

instance : NonUnitalRing (PlainMonomialArtin k S) where
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
          rw [← smul_PX rp, ← smul_PX rq, ← smul_PX rr]
          simp only [smul_mul_raw, mul_smul_raw, smul_smul]
          convert
            congrArg (fun t : PlainMonomialArtin k S ↦ (rp * rq * rr) • t)
              (PX_mul_PX_mul_PX (k := k) S p q r) using 1 <;> ring_nf

instance : NonUnitalCommRing (PlainMonomialArtin k S) where
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
        rw [← smul_PX rp, ← smul_PX rq]
        simp only [smul_mul_raw, mul_smul_raw, smul_smul]
        rw [mul_comm rp rq, PX_mul_PX_comm]

/-- The unit is the unit basis vector when it survives, and the unique zero
element in the empty standard model otherwise.-/
def one (S : Finset (PlainExp)) : PlainMonomialArtin k S :=
  if h : (0 : PlainExp) ∈ plainStandardFinset S then PX (k := k) S 0 h else 0

instance : One (PlainMonomialArtin k S) := ⟨one (k := k) S⟩

theorem one_def : (1 : PlainMonomialArtin k S) =
    if h : (0 : PlainExp) ∈ plainStandardFinset S then PX (k := k) S 0 h else 0 := rfl

private theorem plainStandardFinset_nonempty_of_index (p : PlainMonomialIndex S) : S.Nonempty := by
  have hp := p.2
  rw [mem_plainStandardFinset] at hp
  rcases hp with ⟨s, hs, -⟩
  exact ⟨s, hs⟩

private theorem one_mul_PX (p : PlainMonomialIndex S) :
    (1 : PlainMonomialArtin k S) * PX (k := k) S p.1 p.2 = PX (k := k) S p.1 p.2 := by
  have h1 := zero_mem_plainStandardFinset S (plainStandardFinset_nonempty_of_index p)
  simp [one_def, h1, PX_mul_PX]

instance : NonAssocRing (PlainMonomialArtin k S) where
  natCast n := n • (1 : PlainMonomialArtin k S)
  natCast_zero := by simp
  natCast_succ n := by
    change (n + 1) • (1 : PlainMonomialArtin k S) = n • 1 + 1
    rw [add_nsmul, one_nsmul]
  intCast z := match z with
    | .ofNat n => n • (1 : PlainMonomialArtin k S)
    | .negSucc n => -((n + 1) • (1 : PlainMonomialArtin k S))
  intCast_ofNat _ := rfl
  intCast_negSucc _ := rfl
  one_mul := by
    classical
    intro x
    induction x using induction_linear with
    | zero => simp
    | add x y hx hy => simp [mul_add, hx, hy]
    | single p r =>
      rw [← smul_PX r, mul_smul_raw, one_mul_PX]
  mul_one := by
    classical
    intro x
    induction x using induction_linear with
    | zero => simp
    | add x y hx hy => simp [add_mul, hx, hy]
    | single p r =>
      rw [← smul_PX r, smul_mul_raw, mul_comm, one_mul_PX]

instance : Ring (PlainMonomialArtin k S) where

instance : CommRing (PlainMonomialArtin k S) where

theorem smul_mul_assoc' (r : k) (x y : PlainMonomialArtin k S) :
    (r • x) * y = r • (x * y) := by
  exact smul_mul_raw r x y

theorem mul_smul_comm' (r : k) (x y : PlainMonomialArtin k S) :
    x * (r • y) = r • (x * y) := by
  exact mul_smul_raw r x y

instance : Algebra k (PlainMonomialArtin k S) :=
  Algebra.ofModule smul_mul_assoc' mul_smul_comm'

/-- The surviving unit basis vector is the algebra unit.-/
theorem PX_one (S : Finset (PlainExp)) (hS : S.Nonempty) :
    PX (k := k) S 0 (zero_mem_plainStandardFinset S hS) = 1 := by
  simp [one_def, zero_mem_plainStandardFinset S hS]

/-- A standard monomial gives a nonzero basis vector.-/
theorem PX_ne_zero (S : Finset (PlainExp)) (p : PlainExp)
    (hp : p ∈ plainStandardFinset S) : PX (k := k) S p hp ≠ 0 := by
  intro h
  have hc := congrArg (fun x : PlainMonomialArtin k S ↦ x.coeff ⟨p, hp⟩) h
  simpa [coeff_PX] using hc

/-- A monomial survives in the direct finite model precisely when it has a
nonzero standard basis vector.-/
def BasisSurvives (k : Type*) [Field k] (S : Finset (PlainExp))
    (p : PlainExp) : Prop :=
  ∃ hp : p ∈ plainStandardFinset S, PX (k := k) S p hp ≠ 0

theorem basisSurvives_iff (k : Type*) [Field k]
    (S : Finset (PlainExp)) (p : PlainExp) :
    BasisSurvives k S p ↔ p ∈ plainStandardSet S := by
  constructor
  · rintro ⟨hp, -⟩
    exact (mem_plainStandardFinset S p).1 hp
  · intro hp
    have hp' := (mem_plainStandardFinset S p).2 hp
    exact ⟨hp', PX_ne_zero (k := k) S p hp'⟩

/-- The canonical standard-monomial basis.-/
noncomputable def monomialBasis (k : Type*) [Field k]
    (S : Finset (PlainExp)) :
    Module.Basis (PlainMonomialIndex S) k (PlainMonomialArtin k S) :=
  Finsupp.basisSingleOne.map (coeffLinearEquiv k S).symm

@[simp]
theorem monomialBasis_apply (S : Finset (PlainExp)) (p : PlainMonomialIndex S) :
    monomialBasis k S p = PX (k := k) S p.1 p.2 := by
  rfl

/-- Every element has its unique finite standard-monomial expansion.-/
theorem basis_expansion (x : PlainMonomialArtin k S) :
    x = x.coeff.sum fun p r ↦ r • PX (k := k) S p.1 p.2 := by
  classical
  induction x using induction_linear with
  | zero => simp
  | add x y hx hy =>
      rw [coeff_add, Finsupp.sum_add_index']
      · exact congrArg₂ (fun u v : PlainMonomialArtin k S ↦ u + v) hx hy
      · simp
      · intro p r s
        exact add_smul r s _
  | single p r =>
      rw [Finsupp.sum_single_index]
      · exact (smul_PX r S p.1 p.2).symm
      · simp

/-- Dimension equals the number of surviving standard monomials.-/
theorem finrank_plainMonomialArtin (k : Type*) [Field k]
    (S : Finset (PlainExp)) :
    Module.finrank k (PlainMonomialArtin k S) = (plainStandardFinset S).card := by
  rw [Module.finrank_eq_card_basis (monomialBasis k S), Fintype.card_coe]

end PlainMonomialArtin

export PlainMonomialArtin (PX PX_mul_PX PX_one PX_ne_zero BasisSurvives
  basisSurvives_iff monomialBasis basis_expansion
  finrank_plainMonomialArtin)

end

end P23.Monomial
