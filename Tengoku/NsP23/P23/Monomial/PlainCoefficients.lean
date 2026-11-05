import Tengoku.NsP23.P23.Monomial.PlainCanonicalDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace P23.Monomial
noncomputable section
variable {k : Type*} [Field k]
/-- Scalar coordinate at a surviving standard monomial.-/
def plainCoeffAt (S : Finset PlainExp) (p : PlainMonomialIndex S) :
    PlainMonomialArtin k S →ₗ[k] k where
  toFun v := v.coeff p
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

@[simp]
theorem plainCoeffAt_apply (S : Finset PlainExp) (p : PlainMonomialIndex S)
    (v : PlainMonomialArtin k S) : plainCoeffAt (k := k) S p v = v.coeff p := rfl

theorem plainCoeffAt_PX (S : Finset PlainExp) (p q : PlainMonomialIndex S) :
    plainCoeffAt (k := k) S p (PX (k := k) S q.1 q.2) =
      if p = q then 1 else 0 := by
  change (PX (k := k) S q.1 q.2).coeff p = _
  rw [PlainMonomialArtin.coeff_PX]
  by_cases h : p = q <;> simp [h]

/-- The surviving unit monomial as a standard-monomial index.-/
def plainUnitIndex (S : Finset PlainExp) (hS : S.Nonempty) : PlainMonomialIndex S :=
  ⟨0, zero_mem_plainStandardFinset S hS⟩

/-- Degree-zero coefficient in a nonempty direct standard-monomial model.-/
def plainConstantCoeff (S : Finset PlainExp) (hS : S.Nonempty) :
    PlainMonomialArtin k S →ₗ[k] k :=
  plainCoeffAt (k := k) S (plainUnitIndex S hS)

@[simp]
theorem plainConstantCoeff_one (S : Finset PlainExp) (hS : S.Nonempty) :
    plainConstantCoeff (k := k) S hS 1 = 1 := by
  rw [← PlainMonomialArtin.PX_one (k := k) S hS]
  simp [plainConstantCoeff, plainUnitIndex]

/-- Left multiplication by a surviving monomial transports coefficients
exactly along a cancellative normalized product.-/
theorem plainCoeffAt_PX_mul (S : Finset PlainExp)
    (m e t : PlainMonomialIndex S) (hmet : m.1 + e.1 = t.1)
    (v : PlainMonomialArtin k S) :
    plainCoeffAt (k := k) S t (PX (k := k) S m.1 m.2 * v) =
      plainCoeffAt (k := k) S e v := by
  classical
  induction v using PlainMonomialArtin.induction_linear with
  | zero => simp
  | add v w hv hw =>
      rw [mul_add, map_add, map_add, hv, hw]
  | single q r =>
      rw [← PlainMonomialArtin.smul_PX (k := k) r S q.1 q.2]
      rw [PlainMonomialArtin.mul_smul_comm']
      by_cases hqe : q = e
      · subst q
        simp [PlainMonomialArtin.PX_mul_PX, hmet, t.2, plainCoeffAt_PX]
      · have hprod : m.1 + q.1 ≠ t.1 := by
          intro hp
          apply hqe
          apply Subtype.ext
          apply add_left_cancel
          exact hp.trans hmet.symm
        by_cases hsurv : m.1 + q.1 ∈ plainStandardFinset S
        · rw [PlainMonomialArtin.PX_mul_PX]
          simp only [dite_eq_left hsurv, map_smul]
          simp only [plainCoeffAt_apply, PlainMonomialArtin.coeff_PX]
          have ht : t ≠ ⟨m.1 + q.1, hsurv⟩ := by
            intro heq
            apply hprod
            exact (congrArg Subtype.val heq).symm
          have heq : e ≠ q := fun heq => hqe heq.symm
          have hval : t.1 ≠ m.1 + q.1 := fun hval => hprod hval.symm
          simp [ht, heq, hval]
        · simp [PlainMonomialArtin.PX_mul_PX, hsurv, hqe, plainCoeffAt_PX]

/-- Right-multiplication form of coefficient transport.-/
theorem plainCoeffAt_mul_PX (S : Finset PlainExp)
    (m e t : PlainMonomialIndex S) (hmet : e.1 + m.1 = t.1)
    (v : PlainMonomialArtin k S) :
    plainCoeffAt (k := k) S t (v * PX (k := k) S m.1 m.2) =
      plainCoeffAt (k := k) S e v := by
  rw [mul_comm]
  exact plainCoeffAt_PX_mul (k := k) S m e t (by simpa [add_comm] using hmet) v

theorem plain_add_eq_zero_iff (p q : PlainExp) : p + q = 0 ↔ p = 0 ∧ q = 0 := by
  constructor
  · intro h
    have hc j := congrArg (fun p : PlainExp => p j) h
    constructor <;> ext j <;> specialize hc j <;> simp only [Finsupp.add_apply,Finsupp.zero_apply] at hc ⊢ <;> omega
  · rintro ⟨rfl,rfl⟩; simp

theorem plain_variable_is_atom (j : Fin 3) (p q : PlainExp)
    (h : p+q=plainUnitVector j) : p=0 ∨ q=0 := by
  have hc r := congrArg (fun p : PlainExp => p r) h
  have hj : p j + q j = 1 := by simpa using hc j
  have ho r (hr : r ≠ j) : p r = 0 ∧ q r = 0 := by
    have := hc r
    simp [plainUnitVector,Finsupp.single_apply,Ne.symm hr] at this
    exact this
  have hp : p j = 0 ∨ q j = 0 := by omega
  rcases hp with hp | hq
  · left; ext r; by_cases hr : r=j
    · subst r; exact hp
    · exact (ho r hr).1
  · right; ext r; by_cases hr : r=j
    · subst r; exact hq
    · exact (ho r hr).2

private theorem plainConstantCoeff_PX_mul_PX (S : Finset PlainExp) (hS : S.Nonempty)
    (p q : PlainMonomialIndex S) :
    plainConstantCoeff (k := k) S hS (PX S p.1 p.2 * PX S q.1 q.2) =
      plainConstantCoeff (k := k) S hS (PX S p.1 p.2) *
      plainConstantCoeff (k := k) S hS (PX S q.1 q.2) := by
  classical
  rw [PX_mul_PX]
  by_cases hpq : p.1 + q.1 ∈ plainStandardFinset S
  · simp only [dite_eq_left hpq]
    have hu := plain_add_eq_zero_iff p.1 q.1
    simp only [plainConstantCoeff,plainCoeffAt_PX,plainUnitIndex]
    by_cases hp : p.1=0 <;> by_cases hq : q.1=0 <;>
      simp_all [Subtype.ext_iff,eq_comm]
  · simp only [dite_eq_right hpq,map_zero]
    have hnotboth : ¬ (p.1=0 ∧ q.1=0) := by
      rintro ⟨hp,hq⟩
      exact hpq (by simpa [hp,hq] using zero_mem_plainStandardFinset S hS)
    simp only [plainConstantCoeff,plainCoeffAt_PX,plainUnitIndex]
    by_cases hp : p.1=0 <;> by_cases hq : q.1=0 <;>
      simp_all [Subtype.ext_iff,eq_comm]

theorem plainConstantCoeff_mul (S : Finset PlainExp) (hS : S.Nonempty)
    (u v : PlainMonomialArtin k S) :
    plainConstantCoeff (k := k) S hS (u*v) =
      plainConstantCoeff (k := k) S hS u * plainConstantCoeff S hS v := by
  induction u using PlainMonomialArtin.induction_linear with
  | zero => simp
  | add u₁ u₂ hu₁ hu₂ => rw [add_mul,map_add,map_add,hu₁,hu₂,add_mul]
  | single p rp =>
    rw [←PlainMonomialArtin.smul_PX rp S p.1 p.2]
    induction v using PlainMonomialArtin.induction_linear with
    | zero => simp
    | add v₁ v₂ hv₁ hv₂ => rw [mul_add,map_add,map_add,hv₁,hv₂,mul_add]
    | single q rq =>
      rw [←PlainMonomialArtin.smul_PX rq S q.1 q.2]
      simp only [PlainMonomialArtin.smul_mul_assoc',PlainMonomialArtin.mul_smul_comm',
        map_smul,smul_eq_mul]
      rw [plainConstantCoeff_PX_mul_PX S hS p q]
      ring

 theorem plainCoeffAt_mul_eq_zero_of_right (S : Finset PlainExp)
    (hS : S.Nonempty)
    (e : Fin 3) (heS : plainUnitVector e ∈ plainStandardFinset S)
    (u v : PlainMonomialArtin k S)
    (hv0 : plainConstantCoeff (k := k) S hS v = 0)
    (hve : plainCoeffAt (k := k) S ⟨plainUnitVector e, heS⟩ v = 0) :
    plainCoeffAt (k := k) S ⟨plainUnitVector e, heS⟩ (u * v) = 0 := by
  classical
  let ei : PlainMonomialIndex S := ⟨plainUnitVector e, heS⟩
  have he_ne_one : plainUnitVector e ≠ (0 : PlainExp) := by
    intro h
    have hc := congrArg (fun p : PlainExp => p e) h
    simpa using hc
  have hother (p : PlainMonomialIndex S) (hp1 : p.1 ≠ 0)
      (hpe : p.1 ≠ plainUnitVector e) (w : PlainMonomialArtin k S) :
      plainCoeffAt (k := k) S ei (PX (k := k) S p.1 p.2 * w) = 0 := by
    induction w using PlainMonomialArtin.induction_linear with
    | zero => simp
    | add w₁ w₂ hw₁ hw₂ => rw [mul_add, map_add, hw₁, hw₂, add_zero]
    | single q r =>
        rw [← PlainMonomialArtin.smul_PX (k := k) r S q.1 q.2]
        rw [PlainMonomialArtin.mul_smul_comm']
        rw [PlainMonomialArtin.PX_mul_PX]
        by_cases hpq : p.1 + q.1 ∈ plainStandardFinset S
        · simp only [dite_eq_left hpq, map_smul]
          have hprod : p.1 + q.1 ≠ plainUnitVector e := by
            intro hprod
            rcases plain_variable_is_atom e p.1 q.1 hprod with hp | hq
            · exact hp1 hp
            · apply hpe
              simpa [hq] using hprod
          have hidx : (⟨p.1 + q.1, hpq⟩ : PlainMonomialIndex S) ≠ ei := by
            intro hidx
            apply hprod
            exact congrArg Subtype.val hidx
          have hprod' : plainUnitVector e ≠ p.1 + q.1 := fun h => hprod h.symm
          simp only [plainCoeffAt_apply, PlainMonomialArtin.coeff_PX]
          simp [ei, hprod']
        · simp [hpq]
  have hbasis (p : PlainMonomialIndex S) :
      plainCoeffAt (k := k) S ei (PX (k := k) S p.1 p.2 * v) = 0 := by
    by_cases hp1 : p.1 = 0
    · have hp : p = plainUnitIndex S hS := by
        apply Subtype.ext
        exact hp1
      subst p
      have hX : PX (k := k) S (plainUnitIndex S hS).1 (plainUnitIndex S hS).2 = 1 := by
        simpa [plainUnitIndex] using PlainMonomialArtin.PX_one (k := k) S hS
      rw [hX, one_mul]
      exact hve
    by_cases hpe : p.1 = plainUnitVector e
    · have hp : p = ei := by
        apply Subtype.ext
        exact hpe
      subst p
      rw [plainCoeffAt_PX_mul (k := k) S ei (plainUnitIndex S hS) ei]
      · exact hv0
      · simp [plainUnitIndex]
    exact hother p hp1 hpe v
  induction u using PlainMonomialArtin.induction_linear with
  | zero => simp
  | add u w hu hw => rw [add_mul, map_add, hu, hw, add_zero]
  | single p r =>
      rw [← PlainMonomialArtin.smul_PX (k := k) r S p.1 p.2]
      rw [PlainMonomialArtin.smul_mul_assoc', map_smul, hbasis]
      simp

end
end P23.Monomial
