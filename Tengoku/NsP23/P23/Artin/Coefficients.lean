import Tengoku.NsP23.P23.Artin.CanonicalDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Coefficients in the finite standard-monomial algebra

Scalar coordinate functionals, cancellation transport, and symbolic
atomicity of the live variable generators.  All statements stay inside the
direct finite model.
-/

namespace P23.Artin

noncomputable section

open P23.OneTie

variable {a b c : ℕ} [NeZero a]
variable {k : Type*} [Field k]

/-- The mixed-or-pure parameter domain used by the P23 live one-tie model.-/
def IsLiveParameterDomain (a b c : ℕ) : Prop :=
  2 ≤ a ∧ ((1 ≤ b ∧ 1 ≤ c) ∨ (2 ≤ b ∧ c = 0))

/-- Scalar coordinate at a surviving standard monomial.-/
def coeffAt (S : Finset (Normal a b c)) (p : MonomialIndex S) :
    MonomialArtin k S →ₗ[k] k where
  toFun v := v.coeff p
  map_add' _ _ := by simp
  map_smul' _ _ := by simp

/--
@isnad1 id=eq.0h7v.s8.b92303443749 from=translated src=- shape=430bf636 vocab=d74a0136
-/
@[simp]
theorem coeffAt_apply (S : Finset (Normal a b c)) (p : MonomialIndex S)
    (v : MonomialArtin k S) : coeffAt (k := k) S p v = v.coeff p := rfl

/--
@isnad1 id=eq.0h7v.s8.992931943634 from=translated src=- shape=17458a09 vocab=477c5c2f
-/
theorem coeffAt_X (S : Finset (Normal a b c)) (p q : MonomialIndex S) :
    coeffAt (k := k) S p (X (k := k) S q.1 q.2) =
      if p = q then 1 else 0 := by
  change (X (k := k) S q.1 q.2).coeff p = _
  rw [MonomialArtin.coeff_X]
  by_cases h : p = q <;> simp [h]

/-- The surviving unit monomial as a standard-monomial index.-/
def unitIndex (S : Finset (Normal a b c)) (hS : S.Nonempty) : MonomialIndex S :=
  ⟨1, one_mem_standardFinset S hS⟩

/-- Degree-zero coefficient in a nonempty direct standard-monomial model.-/
def constantCoeff (S : Finset (Normal a b c)) (hS : S.Nonempty) :
    MonomialArtin k S →ₗ[k] k :=
  coeffAt (k := k) S (unitIndex S hS)

/--
@isnad1 id=eq.1h5v.s8.fd7c3bf19e12 from=translated src=- shape=f2009bca vocab=a113b6d2
-/
@[simp]
theorem constantCoeff_one (S : Finset (Normal a b c)) (hS : S.Nonempty) :
    constantCoeff (k := k) S hS 1 = 1 := by
  rw [← MonomialArtin.X_one (k := k) S hS]
  simp [constantCoeff, unitIndex]

/-- Left multiplication by a surviving monomial transports coefficients
exactly along a cancellative normalized product.
@isnad1 id=eq.1h9v.s9.5f270ad68d54 from=translated src=- shape=6b3d512f vocab=8e930555
-/
theorem coeffAt_X_mul (S : Finset (Normal a b c))
    (m e t : MonomialIndex S) (hmet : m.1 * e.1 = t.1)
    (v : MonomialArtin k S) :
    coeffAt (k := k) S t (X (k := k) S m.1 m.2 * v) =
      coeffAt (k := k) S e v := by
  classical
  induction v using MonomialArtin.induction_linear with
  | zero => simp
  | add v w hv hw =>
      rw [mul_add, map_add, map_add, hv, hw]
  | single q r =>
      rw [← MonomialArtin.smul_X (k := k) r S q.1 q.2]
      rw [MonomialArtin.mul_smul_comm']
      by_cases hqe : q = e
      · subst q
        simp [MonomialArtin.X_mul_X, hmet, t.2, coeffAt_X]
      · have hprod : m.1 * q.1 ≠ t.1 := by
          intro hp
          apply hqe
          apply Subtype.ext
          apply Normal.mul_left_cancel
          exact hp.trans hmet.symm
        by_cases hsurv : m.1 * q.1 ∈ standardFinset S
        · rw [MonomialArtin.X_mul_X]
          simp only [dite_eq_left hsurv, map_smul]
          simp only [coeffAt_apply, MonomialArtin.coeff_X]
          have ht : t ≠ ⟨m.1 * q.1, hsurv⟩ := by
            intro heq
            apply hprod
            exact (congrArg Subtype.val heq).symm
          have heq : e ≠ q := fun heq => hqe heq.symm
          have hval : t.1 ≠ m.1 * q.1 := fun hval => hprod hval.symm
          simp [ht, heq, hval]
        · simp [MonomialArtin.X_mul_X, hsurv, hqe, coeffAt_X]

/-- Right-multiplication form of coefficient transport.
@isnad1 id=eq.1h9v.s9.047ac029f796 from=translated src=- shape=b305b9ed vocab=8e930555
-/
theorem coeffAt_mul_X (S : Finset (Normal a b c))
    (m e t : MonomialIndex S) (hmet : e.1 * m.1 = t.1)
    (v : MonomialArtin k S) :
    coeffAt (k := k) S t (v * X (k := k) S m.1 m.2) =
      coeffAt (k := k) S e v := by
  rw [mul_comm]
  exact coeffAt_X_mul (k := k) S m e t (by simpa [mul_comm] using hmet) v

private theorem normal_eq_one_iff (p : Normal a b c) :
    p = 1 ↔ p.x = 0 ∧ p.y = 0 ∧ p.z = 0 := by
  constructor
  · rintro rfl
    simp
  · rintro ⟨hx, hy, hz⟩
    apply Normal.ext <;> simp [hx, hy, hz]

/-- In the actual mixed/pure live domain, the normalized monoid has no
nontrivial factorization of its unit.
@isnad1 id=iff.1h5v.s7.526173d5ff4c from=translated src=- shape=a74ad478 vocab=fb6b71b4
-/
theorem mul_eq_one_iff (hdom : IsLiveParameterDomain a b c)
    (p q : Normal a b c) : p * q = 1 ↔ p = 1 ∧ q = 1 := by
  constructor
  · intro h
    have hx := congrArg Normal.x h
    have hy := congrArg Normal.y h
    have hz := congrArg Normal.z h
    rw [normal_eq_one_iff p, normal_eq_one_iff q]
    unfold IsLiveParameterDomain at hdom
    rcases hdom with ⟨ha, hmixed | hpure⟩
    all_goals
      have hbpos : 0 < b := by omega
      simp only [Normal.mul_x, Normal.mul_y, Normal.mul_z,
        Normal.one_x, Normal.one_y, Normal.one_z] at hx hy hz
      have hmul : ((p.x + q.x) / a) * b = 0 := by
        by_contra hn
        have hg : 0 < ((p.x + q.x) / a) * b := Nat.pos_of_ne_zero hn
        omega
      have hdiv : (p.x + q.x) / a = 0 := by
        rcases Nat.mul_eq_zero.mp hmul with hzero | hzero
        · exact hzero
        · omega
      have hsumlt : p.x + q.x < a :=
        (Nat.div_eq_zero_iff_lt (by omega)).1 hdiv
      have hmod : (p.x + q.x) % a = p.x + q.x :=
        Nat.mod_eq_of_lt hsumlt
      rw [hmod] at hx
      omega
  · rintro ⟨rfl, rfl⟩
    simp

private theorem constantCoeff_X_mul_X (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c)
    (p q : MonomialIndex S) :
    constantCoeff (k := k) S hS
        (X (k := k) S p.1 p.2 * X (k := k) S q.1 q.2) =
      constantCoeff (k := k) S hS (X (k := k) S p.1 p.2) *
        constantCoeff (k := k) S hS (X (k := k) S q.1 q.2) := by
  classical
  rw [MonomialArtin.X_mul_X]
  by_cases hpq : p.1 * q.1 ∈ standardFinset S
  · simp only [dite_eq_left hpq]
    have hu := mul_eq_one_iff (a := a) (b := b) (c := c) hdom p.1 q.1
    simp only [constantCoeff, coeffAt_X, unitIndex]
    by_cases hp : p.1 = 1 <;> by_cases hq : q.1 = 1 <;>
      simp_all [Subtype.ext_iff, eq_comm]
  · simp only [dite_eq_right hpq, map_zero]
    have hnotboth : ¬(p.1 = 1 ∧ q.1 = 1) := by
      rintro ⟨hp, hq⟩
      apply hpq
      simpa [hp, hq] using one_mem_standardFinset S hS
    simp only [constantCoeff, coeffAt_X, unitIndex]
    by_cases hp : p.1 = 1 <;> by_cases hq : q.1 = 1 <;>
      simp_all [Subtype.ext_iff, eq_comm]

/-- Exact degree-zero coefficient of a product in the P23 live parameter
domain.
@isnad1 id=eq.2h7v.s9.d88c168a3528 from=translated src=- shape=d0fc5241 vocab=0e8ec973
-/
theorem constantCoeff_mul (S : Finset (Normal a b c)) (hS : S.Nonempty)
    (hdom : IsLiveParameterDomain a b c) (u v : MonomialArtin k S) :
    constantCoeff (k := k) S hS (u * v) =
      constantCoeff (k := k) S hS u * constantCoeff (k := k) S hS v := by
  classical
  induction u using MonomialArtin.induction_linear with
  | zero => simp
  | add u₁ u₂ hu₁ hu₂ => rw [add_mul, map_add, map_add, hu₁, hu₂, add_mul]
  | single p rp =>
      rw [← MonomialArtin.smul_X (k := k) rp S p.1 p.2]
      induction v using MonomialArtin.induction_linear with
      | zero => simp
      | add v₁ v₂ hv₁ hv₂ =>
          rw [mul_add, map_add, map_add, hv₁, hv₂, mul_add]
      | single q rq =>
          rw [← MonomialArtin.smul_X (k := k) rq S q.1 q.2]
          simp only [MonomialArtin.smul_mul_assoc', MonomialArtin.mul_smul_comm',
            map_smul, smul_eq_mul]
          rw [constantCoeff_X_mul_X (k := k) S hS hdom p q]
          ring

/-- Each live variable generator is an atom of the normalized monoid in the
mixed/pure P23 parameter domain.
@isnad1 id=or.2h6v.s7.abc85d9dfd06 from=translated src=- shape=449ba399 vocab=c502f2c3
-/
theorem variableGenerator_is_atom (hdom : IsLiveParameterDomain a b c)
    (e : Direction) (p q : Normal a b c) (h : p * q = e.generator) :
    p = 1 ∨ q = 1 := by
  have hx := congrArg Normal.x h
  have hy := congrArg Normal.y h
  have hz := congrArg Normal.z h
  rw [normal_eq_one_iff p, normal_eq_one_iff q]
  unfold IsLiveParameterDomain at hdom
  rcases hdom with ⟨ha, hmixed | hpure⟩
  · rcases e with _ | _ | _
    · have ha1 : a ≠ 1 := by omega
      simp [Direction.generator, Normal.xGenerator, ha1, Normal.mul_x,
        Normal.mul_y, Normal.mul_z] at hx hy hz
      obtain ⟨⟨hpy, hqy⟩, hltOr⟩ := hy
      have hlt : p.x + q.x < a := by
        rcases hltOr with (ha0 | hlt) | hb0 <;> omega
      have hmod : (p.x + q.x) % a = p.x + q.x := Nat.mod_eq_of_lt hlt
      rw [hmod] at hx
      omega
    · simp only [Direction.generator, Normal.yGenerator, Normal.mul_x,
        Normal.mul_y, Normal.mul_z] at hx hy hz
      have hmul : ((p.x + q.x) / a) * c = 0 := by omega
      have hdiv : (p.x + q.x) / a = 0 := by
        rcases Nat.mul_eq_zero.mp hmul with hzero | hzero <;> omega
      have hlt := (Nat.div_eq_zero_iff_lt (by omega)).1 hdiv
      have hmod : (p.x + q.x) % a = p.x + q.x := Nat.mod_eq_of_lt hlt
      rw [hmod] at hx
      omega
    · simp only [Direction.generator, Normal.zGenerator, Normal.mul_x,
        Normal.mul_y, Normal.mul_z] at hx hy hz
      have hmul : ((p.x + q.x) / a) * b = 0 := by omega
      have hdiv : (p.x + q.x) / a = 0 := by
        rcases Nat.mul_eq_zero.mp hmul with hzero | hzero <;> omega
      have hlt := (Nat.div_eq_zero_iff_lt (by omega)).1 hdiv
      have hmod : (p.x + q.x) % a = p.x + q.x := Nat.mod_eq_of_lt hlt
      rw [hmod] at hx
      omega
  · rcases e with _ | _ | _
    · have ha1 : a ≠ 1 := by omega
      simp [Direction.generator, Normal.xGenerator, ha1, Normal.mul_x,
        Normal.mul_y, Normal.mul_z] at hx hy hz
      obtain ⟨⟨hpy, hqy⟩, hltOr⟩ := hy
      have hlt : p.x + q.x < a := by
        rcases hltOr with (ha0 | hlt) | hb0 <;> omega
      have hmod : (p.x + q.x) % a = p.x + q.x := Nat.mod_eq_of_lt hlt
      rw [hmod] at hx
      omega
    · simp only [Direction.generator, Normal.yGenerator, Normal.mul_x,
        Normal.mul_y, Normal.mul_z] at hx hy hz
      have hdiv : (p.x + q.x) / a = 0 := by
        by_contra hn
        have hpos : 1 ≤ (p.x + q.x) / a := Nat.one_le_iff_ne_zero.2 hn
        have hlarge : 2 ≤ ((p.x + q.x) / a) * b := by
          nlinarith [Nat.mul_le_mul hpos hpure.1]
        omega
      have hlt := (Nat.div_eq_zero_iff_lt (by omega)).1 hdiv
      have hmod : (p.x + q.x) % a = p.x + q.x := Nat.mod_eq_of_lt hlt
      rw [hmod] at hx
      omega
    · simp only [Direction.generator, Normal.zGenerator, Normal.mul_x,
        Normal.mul_y, Normal.mul_z] at hx hy hz
      have hmul : ((p.x + q.x) / a) * b = 0 := by omega
      have hdiv : (p.x + q.x) / a = 0 := by
        rcases Nat.mul_eq_zero.mp hmul with hzero | hzero <;> omega
      have hlt := (Nat.div_eq_zero_iff_lt (by omega)).1 hdiv
      have hmod : (p.x + q.x) % a = p.x + q.x := Nat.mod_eq_of_lt hlt
      rw [hmod] at hx
      omega

/-- Multiplication by an arbitrary algebra element cannot create the
coefficient of a live atomic variable from a right factor having neither a
degree-zero term nor that variable coefficient.
@isnad1 id=eq.5h8v.s9.4fc6f71df476 from=translated src=- shape=292a982e vocab=4ae1da4b
-/
theorem coeffAt_mul_eq_zero_of_right (S : Finset (Normal a b c))
    (hS : S.Nonempty) (hdom : IsLiveParameterDomain a b c)
    (e : Direction) (heS : e.generator ∈ standardFinset S)
    (u v : MonomialArtin k S)
    (hv0 : constantCoeff (k := k) S hS v = 0)
    (hve : coeffAt (k := k) S ⟨e.generator, heS⟩ v = 0) :
    coeffAt (k := k) S ⟨e.generator, heS⟩ (u * v) = 0 := by
  classical
  let ei : MonomialIndex S := ⟨e.generator, heS⟩
  have he_ne_one : e.generator ≠ (1 : Normal a b c) := by
    exact variableGenerators_ne_one_of_two_le hdom.1 e
  have hother (p : MonomialIndex S) (hp1 : p.1 ≠ 1)
      (hpe : p.1 ≠ e.generator) (w : MonomialArtin k S) :
      coeffAt (k := k) S ei (X (k := k) S p.1 p.2 * w) = 0 := by
    induction w using MonomialArtin.induction_linear with
    | zero => simp
    | add w₁ w₂ hw₁ hw₂ => rw [mul_add, map_add, hw₁, hw₂, add_zero]
    | single q r =>
        rw [← MonomialArtin.smul_X (k := k) r S q.1 q.2]
        rw [MonomialArtin.mul_smul_comm']
        rw [MonomialArtin.X_mul_X]
        by_cases hpq : p.1 * q.1 ∈ standardFinset S
        · simp only [dite_eq_left hpq, map_smul]
          have hprod : p.1 * q.1 ≠ e.generator := by
            intro hprod
            rcases variableGenerator_is_atom hdom e p.1 q.1 hprod with hp | hq
            · exact hp1 hp
            · apply hpe
              simpa [hq] using hprod
          have hidx : (⟨p.1 * q.1, hpq⟩ : MonomialIndex S) ≠ ei := by
            intro hidx
            apply hprod
            exact congrArg Subtype.val hidx
          have hprod' : e.generator ≠ p.1 * q.1 := fun h => hprod h.symm
          simp only [coeffAt_apply, MonomialArtin.coeff_X]
          simp [ei, hprod']
        · simp [hpq]
  have hbasis (p : MonomialIndex S) :
      coeffAt (k := k) S ei (X (k := k) S p.1 p.2 * v) = 0 := by
    by_cases hp1 : p.1 = 1
    · have hp : p = unitIndex S hS := by
        apply Subtype.ext
        exact hp1
      subst p
      have hX : X (k := k) S (unitIndex S hS).1 (unitIndex S hS).2 = 1 := by
        simpa [unitIndex] using MonomialArtin.X_one (k := k) S hS
      rw [hX, one_mul]
      exact hve
    by_cases hpe : p.1 = e.generator
    · have hp : p = ei := by
        apply Subtype.ext
        exact hpe
      subst p
      rw [coeffAt_X_mul (k := k) S ei (unitIndex S hS) ei]
      · exact hv0
      · simp [unitIndex]
    exact hother p hp1 hpe v
  induction u using MonomialArtin.induction_linear with
  | zero => simp
  | add u w hu hw => rw [add_mul, map_add, hu, hw, add_zero]
  | single p r =>
      rw [← MonomialArtin.smul_X (k := k) r S p.1 p.2]
      rw [MonomialArtin.smul_mul_assoc', map_smul, hbasis]
      simp

end

end P23.Artin
