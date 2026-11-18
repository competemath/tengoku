import Tengoku.WasowAsymptoticsLean.WasowShearingLeading
import Tengoku.WasowAsymptoticsLean.WasowPowerSeries
import Tengoku.Seed.RingTheory.PowerSeries.Expand
import Tengoku.Seed.RingTheory.PowerSeries.Trunc

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms entry_ramifiedSeries` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms ramifiedSeries_clear_powers` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms constantCoeff_ramifiedSeries` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_formal_sheared_series` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms power_times_derivative_X_pow` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms derivative_correction_clear` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms entry_normalizedSeries` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms normalizedSeries_clear_powers` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms correction_exponent_pos` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms constantCoeff_normalizedSeries` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms shiftedExpansion_coeff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms shiftedExpansion_coeff_at` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms shiftedExpansion_coeff_nonzero` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms shiftedExpansion_clear_powers` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms entry_shearedSeries` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms shearedSeries_clear_powers` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms supported_of_weightedDegree` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms weightedDegree_zero_iff` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms constantCoeff_shearedSeries` (it only prints; the queue checks the axioms of every declaration). -/

/-!
Actual formal power substitution and shearing, with cleared powers. The
integer `q` in this file is Wasow's exponent in `x⁻ᑫ Yₓ=A(x⁻¹)Y`; it is one
less than the positive `q` parameter used by `WasowFormalRecurrence`.

For `x=zᵖ`, the variable of the constructed series is `z⁻¹`. Before the
chain-rule factor `p`, the normalized derivative correction is
`diag((a/p)i) X^(p(q+1)-a)`. The final pure power substitution coefficient
is `p` times this series. No choice of Wasow's extra constant scaling of
the independent variable is silently made.
-/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace WasowFormalShearing
open PowerSeries

/-- Expand by a genuine power substitution, then remove `L` initial
coefficients after multiplying by `X^R`.-/
def shiftedExpansion (f : PowerSeries ℂ) (p : ℕ) (hp : p ≠ 0) (L R : ℕ) :
    PowerSeries ℂ :=
  PowerSeries.mk (fun l => PowerSeries.coeff (l+L)
    (PowerSeries.X^R * PowerSeries.expand p hp f))

/--
@isnad1 id=eq.1h5v.s8.84868d9f705c from=translated src=- shape=6343fb0a vocab=915d9d23
-/
theorem shiftedExpansion_coeff (f : PowerSeries ℂ) (p : ℕ) (hp : p ≠ 0)
    (L R l : ℕ) :
    PowerSeries.coeff l (shiftedExpansion f p hp L R) =
      PowerSeries.coeff (l+L) (PowerSeries.X^R * PowerSeries.expand p hp f) :=
  PowerSeries.coeff_mk _ _

/--
@isnad1 id=eq.2h6v.s7.29ddfd3b275e from=translated src=- shape=604c993c vocab=1b2ca774
-/
theorem shiftedExpansion_coeff_at (f : PowerSeries ℂ) (p : ℕ) (hp : p ≠ 0)
    (L R l k : ℕ) (hk : l+L=p*k+R) :
    PowerSeries.coeff l (shiftedExpansion f p hp L R)=PowerSeries.coeff k f := by
  rw [shiftedExpansion_coeff,hk,PowerSeries.coeff_X_pow_mul,PowerSeries.coeff_expand_mul]

/--
@isnad1 id=ex.2h5v.s7.beb26fb9b1ca from=translated src=- shape=0dc05482 vocab=1b2ca774
-/
theorem shiftedExpansion_coeff_nonzero (f : PowerSeries ℂ) (p : ℕ) (hp : p ≠ 0)
    (L R l : ℕ) (hne : PowerSeries.coeff l (shiftedExpansion f p hp L R) ≠ 0) :
    ∃ k, l+L=p*k+R ∧ PowerSeries.coeff k f ≠ 0 := by
  rw [shiftedExpansion_coeff,PowerSeries.coeff_X_pow_mul'] at hne
  split_ifs at hne with hR
  · rw [PowerSeries.coeff_expand] at hne
    split_ifs at hne with hdiv
    · refine ⟨(l+L-R)/p,?_,hne⟩
      have he : p*((l+L-R)/p)=l+L-R := Nat.mul_div_cancel' hdiv
      omega
    · exact False.elim (hne rfl)
  · exact False.elim (hne rfl)

/-- No coefficients are discarded when the actual support obeys the
nonnegative exponent bound. This is the formal clear-powers identity.
@isnad1 id=eq.2h4v.s8.757be71b609b from=translated src=- shape=92799799 vocab=155d52c7
-/
theorem shiftedExpansion_clear_powers (f : PowerSeries ℂ) (p : ℕ) (hp : p ≠ 0)
    (L R : ℕ) (hsupport : ∀ k, PowerSeries.coeff k f ≠ 0 → L ≤ p*k+R) :
    PowerSeries.X^L * shiftedExpansion f p hp L R =
      PowerSeries.X^R * PowerSeries.expand p hp f := by
  apply PowerSeries.ext
  intro m
  rw [PowerSeries.coeff_X_pow_mul']
  split_ifs with hm
  · rw [shiftedExpansion_coeff,Nat.sub_add_cancel hm]
  · symm
    rw [PowerSeries.coeff_X_pow_mul']
    split_ifs with hR
    · rw [PowerSeries.coeff_expand]
      split_ifs with hdiv
      · by_contra hne
        have hs := hsupport ((m-R)/p) hne
        have he : p*((m-R)/p)=m-R := Nat.mul_div_cancel' hdiv
        omega
      · rfl
    · rfl

variable {n : ℕ}

/-- The integral no-negative-power condition after clearing the slope
denominator; both sides are natural exponents, so no truncating subtraction
is used in the hypothesis.-/
def Supported (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ)) (p a : ℕ) : Prop :=
  ∀ k i j, (PowerSeries.coeff k A) i j ≠ 0 → a*(i.val+1) ≤ p*k+a*j.val

def shearedSeries (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ))
    (p : ℕ) (hp : p ≠ 0) (a : ℕ) : PowerSeries (Matrix (Fin n) (Fin n) ℂ) :=
  PowerSeries.mk (fun l => (show Matrix (Fin n) (Fin n) ℂ from fun i j => PowerSeries.coeff l
    (shiftedExpansion (WasowPowerSeries.entry A i j) p hp (a*(i.val+1)) (a*j.val))))

/--
@isnad1 id=eq.1h6v.s6.1a63cbef3497 from=translated src=- shape=96b1aa6f vocab=96cbe488
-/
theorem entry_shearedSeries (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ))
    (p : ℕ) (hp : p ≠ 0) (a : ℕ) (i j : Fin n) :
    WasowPowerSeries.entry (shearedSeries A p hp a) i j =
      shiftedExpansion (WasowPowerSeries.entry A i j) p hp (a*(i.val+1)) (a*j.val) := by
  apply PowerSeries.ext
  intro l
  rw [WasowPowerSeries.coeff_entry]
  exact congrFun (congrFun (PowerSeries.coeff_mk l
    (fun l => (show Matrix (Fin n) (Fin n) ℂ from fun i j => PowerSeries.coeff l
      (shiftedExpansion (WasowPowerSeries.entry A i j) p hp (a*(i.val+1)) (a*j.val))))) i) j

/-- The constructed complete matrix series is the actual entrywise
power-substituted gauge transform after clearing its diagonal powers.
@isnad1 id=eq.2h6v.s8.2533c4b1cd7b from=translated src=- shape=47fcd54b vocab=f9857c3d
-/
theorem shearedSeries_clear_powers (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ))
    (p : ℕ) (hp : p ≠ 0) (a : ℕ) (hA : Supported A p a) (i j : Fin n) :
    PowerSeries.X^(a*(i.val+1)) * WasowPowerSeries.entry (shearedSeries A p hp a) i j =
      PowerSeries.X^(a*j.val) * PowerSeries.expand p hp (WasowPowerSeries.entry A i j) := by
  rw [entry_shearedSeries]
  apply shiftedExpansion_clear_powers
  intro k hk
  exact hA k i j (by simpa only [WasowPowerSeries.coeff_entry] using hk)

/--
@isnad1 id=supporte.2h4v.s8.4841cfe30e81 from=translated src=- shape=cfe1850d vocab=8c9cbf59
-/
theorem supported_of_weightedDegree (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ))
    (p : ℕ) (hp : p ≠ 0) (a : ℕ)
    (hA : ∀ k i j, (PowerSeries.coeff k A) i j ≠ 0 →
      0 ≤ WasowShearingLeading.weightedDegree ((a : ℚ)/p) k i j) : Supported A p a := by
  intro k i j hk
  have he := WasowShearingLeading.weightedDegree_ramified p a k hp i j
  have hnon := mul_nonneg (Nat.cast_nonneg p) (hA k i j hk)
  rw [he] at hnon
  have hh : ((a*(i.val+1) : ℕ) : ℚ) ≤ p*k+a*j.val := by
    push_cast
    nlinarith
  exact_mod_cast hh

/--
@isnad1 id=iff.1h6v.s6.c412241fe14b from=translated src=- shape=92d2d5c2 vocab=b59d75d1
-/
theorem weightedDegree_zero_iff (p : ℕ) (hp : p ≠ 0) (a k : ℕ) (i j : Fin n) :
    WasowShearingLeading.weightedDegree ((a : ℚ)/p) k i j=0 ↔
      a*(i.val+1)=p*k+a*j.val := by
  have he := WasowShearingLeading.weightedDegree_ramified p a k hp i j
  have hp' : (p : ℚ) ≠ 0 := by exact_mod_cast hp
  constructor
  · intro hh
    rw [hh,mul_zero] at he
    have : ((a*(i.val+1) : ℕ) : ℚ) = p*k+a*j.val := by push_cast; nlinarith
    exact_mod_cast this
  · intro hh
    have hh' : ((a*(i.val+1) : ℕ) : ℚ) = p*k+a*j.val := by exact_mod_cast hh
    push_cast at hh'
    apply (mul_eq_zero.mp (show (p : ℚ)*
      WasowShearingLeading.weightedDegree ((a : ℚ)/p) k i j=0 by rw [he]; nlinarith)).resolve_left hp'

/-- The constant coefficient agrees with the already proved actual
zero-weight leading matrix, entry by entry.
@isnad1 id=eq.1h4v.s9.a6a207c7bbd2 from=translated src=- shape=00dad898 vocab=91190efa
-/
theorem constantCoeff_shearedSeries (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ))
    (p : ℕ) (hp : p ≠ 0) (a : ℕ) :
    PowerSeries.constantCoeff (shearedSeries A p hp a) =
      WasowShearingLeading.leadingMatrix (fun k => PowerSeries.coeff k A) ((a : ℚ)/p) := by
  classical
  ext i j
  change PowerSeries.coeff 0 (shiftedExpansion (WasowPowerSeries.entry A i j)
    p hp (a*(i.val+1)) (a*j.val)) = _
  by_cases hex : ∃ k, WasowShearingLeading.weightedDegree ((a : ℚ)/p) k i j=0
  · obtain ⟨k,hk⟩ := hex
    rw [WasowShearingLeading.leadingMatrix_eq_coeff _ _ k i j hk]
    have he := (weightedDegree_zero_iff p hp a k i j).mp hk
    simpa only [WasowPowerSeries.coeff_entry] using
      shiftedExpansion_coeff_at (WasowPowerSeries.entry A i j) p hp
        (a*(i.val+1)) (a*j.val) 0 k (by simpa using he)
  · have hl : WasowShearingLeading.leadingMatrix
        (fun k => PowerSeries.coeff k A) ((a : ℚ)/p) i j=0 := by
      simp only [WasowShearingLeading.leadingMatrix,dite_eq_right hex]
    rw [hl]
    by_contra hn
    obtain ⟨k,hk,_⟩ := shiftedExpansion_coeff_nonzero (WasowPowerSeries.entry A i j)
      p hp (a*(i.val+1)) (a*j.val) 0 hn
    exact hex ⟨k,(weightedDegree_zero_iff p hp a k i j).mpr (by simpa using hk)⟩

/-- The scalar derivative identity of the actual diagonal gauge power.
@isnad1 id=eq.0h2v.s8.2d8655446fcf from=translated src=- shape=bcf3bc40 vocab=a79e95b6
-/
theorem power_times_derivative_X_pow (Q b : ℕ) :
    (PowerSeries.X : PowerSeries ℂ)^(Q+1) *
        PowerSeries.derivative ℂ (PowerSeries.X^b) =
      PowerSeries.C (b : ℂ) * PowerSeries.X^(Q+b) := by
  cases b with
  | zero => simp
  | succ b =>
    rw [PowerSeries.derivative_pow,PowerSeries.derivative_X,mul_one]
    have hc : ((b+1 : ℕ) : PowerSeries ℂ) = PowerSeries.C ((b+1 : ℕ) : ℂ) := by simp
    rw [hc]
    simp only [Nat.add_sub_cancel]
    rw [show Q+(b+1)=Q+1+b by omega,pow_add]
    ring

/--
@isnad1 id=eq.1h5v.s9.b22d1771102a from=translated src=- shape=8b503ab9 vocab=acdcc9cd
-/
theorem derivative_correction_clear (p a q : ℕ) (ha : a ≤ p*(q+1)) (i : Fin n) :
    (PowerSeries.X : PowerSeries ℂ)^(a*(i.val+1)) *
        PowerSeries.monomial (p*(q+1)-a) (((a*i.val : ℕ) : ℂ)/(p : ℂ)) =
      PowerSeries.C ((p : ℂ)⁻¹) * PowerSeries.X^(p*(q+1)+1) *
        PowerSeries.derivative ℂ (PowerSeries.X^(a*i.val)) := by
  rw [mul_assoc, power_times_derivative_X_pow]
  rw [PowerSeries.monomial_eq_C_mul_X_pow]
  have he : a*(i.val+1)+(p*(q+1)-a)=p*(q+1)+a*i.val := by
    rw [Nat.mul_add, Nat.mul_one]
    omega
  rw [← he,pow_add]
  rw [div_eq_mul_inv,map_mul]
  ring

def correctionSeries (p a q : ℕ) : PowerSeries (Matrix (Fin n) (Fin n) ℂ) :=
  PowerSeries.monomial (p*(q+1)-a)
    (Matrix.diagonal (fun i => (((a*i.val : ℕ) : ℂ)/(p : ℂ))))

def normalizedSeries (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ))
    (p : ℕ) (hp : p ≠ 0) (a q : ℕ) : PowerSeries (Matrix (Fin n) (Fin n) ℂ) :=
  shearedSeries A p hp a + correctionSeries p a q

/--
@isnad1 id=eq.1h7v.s7.ed5a78407377 from=translated src=- shape=30e46cb8 vocab=0de8fcd9
-/
theorem entry_normalizedSeries (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ))
    (p : ℕ) (hp : p ≠ 0) (a q : ℕ) (i j : Fin n) :
    WasowPowerSeries.entry (normalizedSeries A p hp a q) i j =
      WasowPowerSeries.entry (shearedSeries A p hp a) i j +
        PowerSeries.monomial (p*(q+1)-a)
          (if i=j then (((a*i.val : ℕ) : ℂ)/(p : ℂ)) else 0) := by
  apply PowerSeries.ext
  intro k
  simp only [WasowPowerSeries.coeff_entry,normalizedSeries,correctionSeries,
    map_add,PowerSeries.coeff_monomial,Matrix.add_apply]
  split_ifs with hk hij
  · subst j; simp
  · rw [Matrix.diagonal_apply_ne _ hij]
  · rfl

/-- The complete formal gauge equation with the genuine diagonal-gauge
derivative. The plus sign comes from using the inverse variable `z⁻¹`.
For the unscaled substitution `x=zᵖ`, multiply the resulting coefficient
matrix by `p` as required by the chain rule.
@isnad1 id=eq.3h7v.s9.071f1a149e27 from=translated src=- shape=3810dabb vocab=f8b3a9ef
-/
theorem normalizedSeries_clear_powers
    (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ)) (p : ℕ) (hp : p ≠ 0)
    (a q : ℕ) (hA : Supported A p a) (ha : a ≤ p*(q+1)) (i j : Fin n) :
    PowerSeries.X^(a*(i.val+1)) * WasowPowerSeries.entry (normalizedSeries A p hp a q) i j =
      PowerSeries.X^(a*j.val) * PowerSeries.expand p hp (WasowPowerSeries.entry A i j) +
        (if i=j then PowerSeries.C ((p : ℂ)⁻¹) * PowerSeries.X^(p*(q+1)+1) *
          PowerSeries.derivative ℂ (PowerSeries.X^(a*i.val)) else 0) := by
  rw [entry_normalizedSeries,mul_add,shearedSeries_clear_powers A p hp a hA]
  by_cases hij : i=j
  · rw [ite_eq_left hij,ite_eq_left hij,derivative_correction_clear p a q ha]
  · simp only [ite_eq_right hij,map_zero,mul_zero,add_zero]

/--
@isnad1 id=lt.2h3v.s6.f269a55c4f8d from=translated src=- shape=26f724c4 vocab=3b7eff14
-/
theorem correction_exponent_pos (p : ℕ) (hp : p ≠ 0) (a q : ℕ)
    (hσ : (a : ℚ)/p < (q+1 : ℕ)) : 0 < p*(q+1)-a := by
  have hp' : (0 : ℚ)<p := by exact_mod_cast Nat.pos_of_ne_zero hp
  have hh := (div_lt_iff₀ hp').mp hσ
  have hn : a < p*(q+1) := by
    have hq : (a : ℚ)<p*((q+1 : ℕ) : ℚ) := by simpa [mul_comm] using hh
    exact_mod_cast hq
  omega

/-- Below the stopping threshold, the derivative correction has positive
order and the full normalized series keeps the proved leading matrix.
@isnad1 id=eq.2h5v.s9.3d086f6855db from=translated src=- shape=60f98484 vocab=85124c3e
-/
theorem constantCoeff_normalizedSeries
    (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ)) (p : ℕ) (hp : p ≠ 0)
    (a q : ℕ) (hσ : (a : ℚ)/p < (q+1 : ℕ)) :
    PowerSeries.constantCoeff (normalizedSeries A p hp a q) =
      WasowShearingLeading.leadingMatrix (fun k => PowerSeries.coeff k A) ((a : ℚ)/p) := by
  have hd : p*(q+1)-a ≠ 0 := Nat.ne_of_gt (correction_exponent_pos p hp a q hσ)
  rw [normalizedSeries,map_add,constantCoeff_shearedSeries]
  suffices PowerSeries.constantCoeff (correctionSeries (n := n) p a q)=0 by rw [this,add_zero]
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp [correctionSeries,PowerSeries.coeff_monomial,Ne.symm hd]

/-- The actual coefficient for the pure substitution `x=z^p`, including
its chain-rule factor. Its leading matrix is `p` times the normalized one.-/
def ramifiedSeries (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ))
    (p : ℕ) (hp : p ≠ 0) (a q : ℕ) : PowerSeries (Matrix (Fin n) (Fin n) ℂ) :=
  (p : ℂ) • normalizedSeries A p hp a q

/--
@isnad1 id=eq.1h7v.s6.e01e1883b2d0 from=translated src=- shape=c017bb59 vocab=05c73b9a
-/
theorem entry_ramifiedSeries (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ))
    (p : ℕ) (hp : p ≠ 0) (a q : ℕ) (i j : Fin n) :
    WasowPowerSeries.entry (ramifiedSeries A p hp a q) i j =
      PowerSeries.C (p : ℂ) * WasowPowerSeries.entry (normalizedSeries A p hp a q) i j := by
  apply PowerSeries.ext
  intro k
  simp only [WasowPowerSeries.coeff_entry,ramifiedSeries,PowerSeries.coeff_smul,
    PowerSeries.coeff_C_mul,Matrix.smul_apply,smul_eq_mul]

/-- With the actual ramification prefactor, the cleared formal gauge
identity has exactly the unscaled derivative of the diagonal gauge.
@isnad1 id=eq.3h7v.s9.e36199537528 from=translated src=- shape=dc532331 vocab=887e9192
-/
theorem ramifiedSeries_clear_powers
    (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ)) (p : ℕ) (hp : p ≠ 0)
    (a q : ℕ) (hA : Supported A p a) (ha : a ≤ p*(q+1)) (i j : Fin n) :
    PowerSeries.X^(a*(i.val+1)) * WasowPowerSeries.entry (ramifiedSeries A p hp a q) i j =
      PowerSeries.C (p : ℂ) * PowerSeries.X^(a*j.val) *
        PowerSeries.expand p hp (WasowPowerSeries.entry A i j) +
        (if i=j then PowerSeries.X^(p*(q+1)+1) *
          PowerSeries.derivative ℂ (PowerSeries.X^(a*i.val)) else 0) := by
  have hp' : (p : ℂ) ≠ 0 := by exact_mod_cast hp
  have hc : PowerSeries.C (p : ℂ) * PowerSeries.C ((p : ℂ)⁻¹) = (1 : PowerSeries ℂ) := by
    rw [← map_mul,mul_inv_cancel₀ hp',map_one]
  rw [entry_ramifiedSeries]
  calc
    _ = PowerSeries.C (p : ℂ) * (PowerSeries.X^(a*(i.val+1)) *
        WasowPowerSeries.entry (normalizedSeries A p hp a q) i j) := by ring
    _ = _ := by
      rw [normalizedSeries_clear_powers A p hp a q hA ha,mul_add]
      by_cases hij : i=j
      · simp only [ite_eq_left hij]
        rw [← mul_assoc (PowerSeries.C (p : ℂ))
          (PowerSeries.C ((p : ℂ)⁻¹) * PowerSeries.X^(p*(q+1)+1)),
          ← mul_assoc (PowerSeries.C (p : ℂ)) (PowerSeries.C ((p : ℂ)⁻¹)),hc,one_mul]
        ring
      · simp only [ite_eq_right hij,mul_zero,add_zero]
        ring

/--
@isnad1 id=eq.2h5v.s9.07021f06e89c from=translated src=- shape=c832cbd7 vocab=297b6906
-/
theorem constantCoeff_ramifiedSeries
    (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ)) (p : ℕ) (hp : p ≠ 0)
    (a q : ℕ) (hσ : (a : ℚ)/p < (q+1 : ℕ)) :
    PowerSeries.constantCoeff (ramifiedSeries A p hp a q) =
      (p : ℂ) • WasowShearingLeading.leadingMatrix
        (fun k => PowerSeries.coeff k A) ((a : ℚ)/p) := by
  rw [ramifiedSeries,PowerSeries.constantCoeff_smul,constantCoeff_normalizedSeries A p hp a q hσ]

/-- Complete non-stopping formal update, constructed from the old full
series and the verified coefficient support bound.
@isnad1 id=ex.3h5v.s10.5304956e495a from=translated src=- shape=ac47d331 vocab=40ff895a
-/
theorem exists_formal_sheared_series
    (A : PowerSeries (Matrix (Fin n) (Fin n) ℂ)) (p : ℕ) (hp : p ≠ 0)
    (a q : ℕ) (hA : Supported A p a) (hσ : (a : ℚ)/p < (q+1 : ℕ)) :
    ∃ B : PowerSeries (Matrix (Fin n) (Fin n) ℂ),
      PowerSeries.constantCoeff B =
        WasowShearingLeading.leadingMatrix (fun k => PowerSeries.coeff k A) ((a : ℚ)/p) ∧
      ∀ i j, PowerSeries.X^(a*(i.val+1)) * WasowPowerSeries.entry B i j =
        PowerSeries.X^(a*j.val) * PowerSeries.expand p hp (WasowPowerSeries.entry A i j) +
          (if i=j then PowerSeries.C ((p : ℂ)⁻¹) * PowerSeries.X^(p*(q+1)+1) *
            PowerSeries.derivative ℂ (PowerSeries.X^(a*i.val)) else 0) := by
  refine ⟨normalizedSeries A p hp a q,constantCoeff_normalizedSeries A p hp a q hσ,?_⟩
  have ha : a ≤ p*(q+1) := by
    have := correction_exponent_pos p hp a q hσ
    omega
  exact normalizedSeries_clear_powers A p hp a q hA ha

end WasowFormalShearing
