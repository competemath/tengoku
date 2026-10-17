import Tengoku.OpenaiMath.OAI.Algebra.AffineCancellation.OrbitRigidity

namespace OAI

noncomputable section

namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R]

/--
@isnad1 id=eq.0h2v.s7.89aef79f68e9 from=translated src=- shape=b383a80a vocab=0585877e
-/
lemma inv_factorial_succ (n : ℕ) :
    ((n + 1 : ℕ) : k) * ((n + 1).factorial : k)⁻¹ = (n.factorial : k)⁻¹ := by
  rw [Nat.factorial_succ, Nat.cast_mul, mul_inv_rev]
  have hn : ((n + 1 : ℕ) : k) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  field_simp

/--
@isnad1 id=eq.1h4v.s8.628e2ee8f360 from=translated src=- shape=fea61fde vocab=89ca65fb
-/
lemma derivative_orbit (D : Derivation k R R) (hD : LocallyNilpotent D) (r : R) :
    (orbit D hD r).derivative = orbit D hD (D r) := by
  ext n
  rw [Polynomial.coeff_derivative, orbit_coeff, orbit_coeff,
    ← Function.iterate_succ_apply]
  rw [mul_comm, ← Nat.cast_succ, ← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul k, smul_smul,
    inv_factorial_succ]

/--
@isnad1 id=and.4h5v.s8.f354af8249c1 from=translated src=- shape=b4cfd088 vocab=a05915b4
-/
lemma kernel_factorially_closed [IsDomain R] (D : Derivation k R R)
    (hD : LocallyNilpotent D) {r s : R} (hr : r ≠ 0) (hs : s ≠ 0)
    (hrs : D (r * s) = 0) : D r = 0 ∧ D s = 0 := by
  have hor : orbit D hD r ≠ 0 := by
    intro h
    have := congrArg (fun p : R[X] => p.coeff 0) h
    simp at this
    exact hr this
  have hos : orbit D hD s ≠ 0 := by
    intro h
    have := congrArg (fun p : R[X] => p.coeff 0) h
    simp at this
    exact hs this
  have hp := (orbit_constant_iff D hD (r*s)).mpr hrs
  rw [orbit_mul] at hp
  have hn := congrArg Polynomial.natDegree hp
  rw [natDegree_mul hor hos, natDegree_C] at hn
  have hnr : (orbit D hD r).natDegree = 0 := by omega
  have hns : (orbit D hD s).natDegree = 0 := by omega
  constructor
  · apply (orbit_constant_iff D hD r).mp
    simpa using eq_C_of_natDegree_eq_zero hnr
  · apply (orbit_constant_iff D hD s).mp
    simpa using eq_C_of_natDegree_eq_zero hns

end ComplexCancellation.LND
namespace ComplexCancellation.LND
open Polynomial
variable {k R : Type*} [Field k] [CharZero k] [CommRing R] [Algebra k R] [IsDomain R]

/--
@isnad1 id=eq.2h4v.s8.a5689df96447 from=translated src=- shape=c40987ac vocab=13639996
-/
lemma fixed_of_dvd (D : Derivation k R R) (hD : LocallyNilpotent D)
    {r : R} (hr : r ∣ D r) : D r = 0 := by
  obtain ⟨s, hs⟩ := hr
  have hdvd : orbit D hD r ∣ (orbit D hD r).derivative := by
    rw [derivative_orbit, hs, orbit_mul]
    exact dvd_mul_right _ _
  have hz := Polynomial.dvd_derivative_iff.mp hdvd
  rw [derivative_orbit] at hz
  apply orbit_injective D hD
  change orbitHom D hD (D r) = orbitHom D hD 0
  rw [map_zero]
  exact hz

end ComplexCancellation.LND

namespace ComplexCancellation.LND
variable {k R : Type*} [Field k] [CommRing R] [Algebra k R]

/--
@isnad1 id=ex.2h5v.s8.ba69ae02d59d from=translated src=- shape=a0cdadf0 vocab=5d83a4d2
-/
lemma nilpotent_add (D : Derivation k R R) {r s : R}
    (hr : ∃ n, (D : R → R)^[n] r = 0) (hs : ∃ n, (D : R → R)^[n] s = 0) :
    ∃ n, (D : R → R)^[n] (r+s) = 0 := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hs
  refine ⟨n+m, ?_⟩
  rw [iterate_add, iterate_eq_zero_of_le D hn (Nat.le_add_right _ _),
    iterate_eq_zero_of_le D hm (Nat.le_add_left _ _), add_zero]

/--
@isnad1 id=ex.2h5v.s8.67654ebeb9dd from=translated src=- shape=a0cdadf0 vocab=214cf83e
-/
lemma nilpotent_mul (D : Derivation k R R) {r s : R}
    (hr : ∃ n, (D : R → R)^[n] r = 0) (hs : ∃ n, (D : R → R)^[n] s = 0) :
    ∃ n, (D : R → R)^[n] (r*s) = 0 := by
  obtain ⟨n, hn⟩ := hr
  obtain ⟨m, hm⟩ := hs
  refine ⟨n+m, ?_⟩
  rw [iterate_leibniz]
  apply Finset.sum_eq_zero
  rintro ⟨i,j⟩ hij
  have hij' : i+j = n+m := Finset.HasAntidiagonal.mem_antidiagonal.mp hij
  by_cases hi : n ≤ i
  · rw [iterate_eq_zero_of_le D hn hi, zero_mul, nsmul_zero]
  · rw [iterate_eq_zero_of_le D hm (by omega : m ≤ j), mul_zero, nsmul_zero]

/--
@isnad1 id=locallyn.1h3v.s9.3011a877c638 from=translated src=- shape=b8e5bf86 vocab=592fbdca
-/
lemma mvPolynomial_locallyNilpotent {σ : Type*}
    (D : Derivation k (MvPolynomial σ k) (MvPolynomial σ k))
    (hX : ∀ i, ∃ n : ℕ, (D : _ → _)^[n] (MvPolynomial.X i) = 0) :
    LocallyNilpotent D := by
  intro r
  induction r using MvPolynomial.induction_on with
  | C c => exact ⟨1, by simp⟩
  | add r s hr hs => exact nilpotent_add D hr hs
  | mul_X r i hr => exact nilpotent_mul D hr (hX i)

end ComplexCancellation.LND

end

end OAI
