import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BigWittLaw

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace BigWittLaw

open MvPolynomial

def genSeries : PowerSeries (MvPolynomial ℕ ℤ) :=
  PowerSeries.mk fun n => Nat.casesOn n 1 fun m => X m

/--
@isnad1 id=eq.0h0v.s8.1964dd1bbef5 from=translated src=- shape=b318a134 vocab=1fc6a7fd
-/
@[simp] theorem coeff_genSeries_zero : PowerSeries.coeff 0 genSeries = 1 := by
  simp [genSeries, PowerSeries.coeff_mk]

/--
@isnad1 id=eq.0h1v.s8.0f2d55c03b08 from=translated src=- shape=17135b81 vocab=14593d17
-/
@[simp] theorem coeff_genSeries_succ (m : ℕ) : PowerSeries.coeff (m + 1) genSeries = X m := by
  simp [genSeries, PowerSeries.coeff_mk]

/--
@isnad1 id=eq.0h0v.s7.242848305618 from=translated src=- shape=d1a7aa3d vocab=bf459df9
-/
@[simp] theorem constantCoeff_genSeries : PowerSeries.constantCoeff genSeries = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_genSeries_zero]

def killProd : ℕ → PowerSeries (MvPolynomial ℕ ℤ)
  | 0 => genSeries
  | k + 1 => killProd k *
      (1 - PowerSeries.C (PowerSeries.coeff (k + 1) (killProd k)) * PowerSeries.X ^ (k + 1))

def wittCoord (k : ℕ) : MvPolynomial ℕ ℤ := PowerSeries.coeff (k + 1) (killProd k)

/--
@isnad1 id=eq.0h0v.s3.d0d4dade447a from=translated src=- shape=38652ea2 vocab=246f9f91
-/
theorem killProd_zero : killProd 0 = genSeries := rfl

/--
@isnad1 id=eq.0h1v.s8.e4ebc527f60b from=translated src=- shape=a1facb7d vocab=899ce6d2
-/
theorem killProd_succ (k : ℕ) :
    killProd (k + 1) = killProd k * (1 - PowerSeries.C (wittCoord k) * PowerSeries.X ^ (k + 1)) := rfl

/--
@isnad1 id=eq.0h1v.s8.d4e6d6a550de from=translated src=- shape=1d692651 vocab=5581810b
-/
theorem wittCoord_eq (k : ℕ) : wittCoord k = PowerSeries.coeff (k + 1) (killProd k) := rfl

/--
@isnad1 id=eq.0h0v.s4.2a6d733745ba from=translated src=- shape=3b9c9462 vocab=628051c8
-/
@[simp] theorem wittCoord_zero : wittCoord 0 = X 0 := by
  rw [wittCoord_eq, killProd_zero, coeff_genSeries_succ]

/--
@isnad1 id=eq.0h1v.s8.8e4d6d2006e4 from=translated src=- shape=8f04b8f9 vocab=182066ae
-/
theorem killProd_eq_mul_prod (k : ℕ) :
    killProd k = genSeries * ∏ i ∈ Finset.range k,
      (1 - PowerSeries.C (wittCoord i) * PowerSeries.X ^ (i + 1)) := by
  induction k with
  | zero => simp [killProd_zero]
  | succ k ih => rw [killProd_succ, ih, Finset.prod_range_succ, mul_assoc]

/--
@isnad1 id=eq.0h1v.s7.fc912fe6adbf from=translated src=- shape=fad71cc0 vocab=877eda80
-/
@[simp] theorem constantCoeff_killProd (k : ℕ) : PowerSeries.constantCoeff (killProd k) = 1 := by
  induction k with
  | zero => exact constantCoeff_genSeries
  | succ k ih =>
    rw [killProd_succ, map_mul, ih, one_mul, map_sub, map_one, map_mul, map_pow,
      PowerSeries.constantCoeff_X, zero_pow (Nat.succ_ne_zero k), mul_zero, sub_zero]

/--
@isnad1 id=eq.0h5v.s9.4ed047049118 from=translated src=- shape=c8d23693 vocab=fe5ad95b
-/
theorem coeff_mul_one_sub_C_mul_X_pow {A : Type*} [CommRing A] (P : PowerSeries A) (c : A)
    (k j : ℕ) :
    PowerSeries.coeff j (P * (1 - PowerSeries.C c * PowerSeries.X ^ (k + 1))) =
      PowerSeries.coeff j P - if k + 1 ≤ j then c * PowerSeries.coeff (j - (k + 1)) P else 0 := by
  rw [mul_sub, mul_one, map_sub]
  congr 1
  split_ifs with h
  · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [show k + 1 + d = d + (k + 1) by omega, ← mul_assoc, mul_comm P, mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow, Nat.add_sub_cancel]
  · rw [not_le] at h
    rw [← mul_assoc, mul_comm P, mul_assoc, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul,
      Finset.sum_eq_zero, mul_zero]
    rintro ⟨i, l⟩ hil
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hil
    rw [PowerSeries.coeff_X_pow, ite_eq_right, mul_zero]
    omega

/--
@isnad1 id=eq.2h2v.s8.42dca4957ce8 from=translated src=- shape=ac7222cf vocab=2edea1a1
-/
theorem coeff_killProd_eq_zero {k j : ℕ} (hj : 1 ≤ j) (hjk : j ≤ k) :
    PowerSeries.coeff j (killProd k) = 0 := by
  induction k generalizing j with
  | zero => omega
  | succ k ih =>
    rw [killProd_succ, coeff_mul_one_sub_C_mul_X_pow]
    rcases Nat.lt_or_ge j (k + 1) with h | h
    · rw [ite_eq_right (by omega), sub_zero]
      exact ih hj (by omega)
    · have hjk' : j = k + 1 := le_antisymm hjk h
      subst hjk'
      rw [ite_eq_left le_rfl, Nat.sub_self, PowerSeries.coeff_zero_eq_constantCoeff_apply,
        constantCoeff_killProd, mul_one, ← wittCoord_eq, sub_self]

abbrev awt : ℕ → ℕ := fun m => m + 1

def IsIsobaric (n : ℕ) (P : PowerSeries (MvPolynomial ℕ ℤ)) : Prop :=
  ∀ j, IsWeightedHomogeneous awt (PowerSeries.coeff j P) (n * j)

/--
@isnad1 id=isweight.1h3v.s8.e776bf23b44b from=translated src=- shape=5c14f557 vocab=d7605bd6
-/
theorem IsIsobaric.coeff {n : ℕ} {P : PowerSeries (MvPolynomial ℕ ℤ)} (h : IsIsobaric n P) (j : ℕ) :
    IsWeightedHomogeneous awt (PowerSeries.coeff j P) (n * j) := h j

/--
@isnad1 id=isisobar.0h1v.s5.633657d79010 from=translated src=- shape=1d1bfee7 vocab=40f91e10
-/
theorem isIsobaric_one (n : ℕ) : IsIsobaric n 1 := by
  intro j
  rw [PowerSeries.coeff_one]
  split_ifs with h
  · subst h; rw [mul_zero]; exact isWeightedHomogeneous_one ℤ awt
  · exact isWeightedHomogeneous_zero ℤ awt _

/--
@isnad1 id=isisobar.2h3v.s6.4c00d0009c6a from=translated src=- shape=fddac7f8 vocab=57d41e6b
-/
theorem IsIsobaric.mul {n : ℕ} {P Q : PowerSeries (MvPolynomial ℕ ℤ)} (hP : IsIsobaric n P)
    (hQ : IsIsobaric n Q) : IsIsobaric n (P * Q) := by
  intro j
  rw [PowerSeries.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun il hil => ?_
  rw [Finset.HasAntidiagonal.mem_antidiagonal] at hil
  have h := (hP il.1).mul (hQ il.2)
  rwa [← mul_add, hil] at h

/--
@isnad1 id=isisobar.2h3v.s6.0cd22ec85e28 from=translated src=- shape=fddac7f8 vocab=030f67cb
-/
theorem IsIsobaric.sub {n : ℕ} {P Q : PowerSeries (MvPolynomial ℕ ℤ)} (hP : IsIsobaric n P)
    (hQ : IsIsobaric n Q) : IsIsobaric n (P - Q) := by
  intro j
  rw [map_sub]
  exact (weightedHomogeneousSubmodule ℤ awt (n * j)).sub_mem (hP j) (hQ j)

/--
@isnad1 id=isisobar.1h4v.s6.9a591de8cc4d from=translated src=- shape=6d6e07cf vocab=50cc0a67
-/
theorem IsIsobaric.prod {n : ℕ} {ι : Type*} (s : Finset ι) (P : ι → PowerSeries (MvPolynomial ℕ ℤ))
    (h : ∀ i ∈ s, IsIsobaric n (P i)) : IsIsobaric n (∏ i ∈ s, P i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.prod_empty]; exact isIsobaric_one n
  | insert i s hi ih =>
    rw [Finset.prod_insert hi]
    exact (h i (Finset.mem_insert_self i s)).mul (ih fun l hl => h l (Finset.mem_insert_of_mem hl))

/--
@isnad1 id=isisobar.1h3v.s6.610e9ebbe20f from=translated src=- shape=7817b98b vocab=3376d339
-/
theorem IsIsobaric.pow {n : ℕ} {P : PowerSeries (MvPolynomial ℕ ℤ)} (hP : IsIsobaric n P) (e : ℕ) :
    IsIsobaric n (P ^ e) := by
  induction e with
  | zero => rw [pow_zero]; exact isIsobaric_one n
  | succ e ih => rw [pow_succ]; exact ih.mul hP

/--
@isnad1 id=isisobar.1h3v.s8.235ef4660743 from=translated src=- shape=f91fb95e vocab=c1ab2877
-/
theorem isIsobaric_C_mul_X_pow {n e : ℕ} {c : MvPolynomial ℕ ℤ} (hc : IsWeightedHomogeneous awt c (n * e)) :
    IsIsobaric n (PowerSeries.C c * PowerSeries.X ^ e) := by
  intro j
  rw [PowerSeries.coeff_C_mul_X_pow]
  split_ifs with h
  · subst h; exact hc
  · exact isWeightedHomogeneous_zero ℤ awt _

/--
@isnad1 id=isisobar.0h0v.s2.94a3ac67618a from=translated src=- shape=cef8a6bf vocab=81e03534
-/
theorem isIsobaric_genSeries : IsIsobaric 1 genSeries := by
  intro j
  cases j with
  | zero => rw [coeff_genSeries_zero, mul_zero]; exact isWeightedHomogeneous_one ℤ awt
  | succ m => rw [coeff_genSeries_succ, one_mul]; exact isWeightedHomogeneous_X ℤ awt m

/--
@isnad1 id=isisobar.0h1v.s3.b0cf6aa948d9 from=translated src=- shape=dd91401e vocab=34e9b494
-/
theorem isIsobaric_killProd (k : ℕ) : IsIsobaric 1 (killProd k) := by
  induction k with
  | zero => exact isIsobaric_genSeries
  | succ k ih =>
    rw [killProd_succ]
    refine ih.mul ((isIsobaric_one 1).sub (isIsobaric_C_mul_X_pow ?_))
    exact ih (k + 1)

/--
@isnad1 id=isweight.0h1v.s4.7312fa9440b0 from=translated src=- shape=319f7b94 vocab=4d8fd12f
-/
theorem isWeightedHomogeneous_wittCoord (k : ℕ) : IsWeightedHomogeneous awt (wittCoord k) (k + 1) := by
  have h := isIsobaric_killProd k (k + 1)
  rwa [one_mul] at h

/--
@isnad1 id=eq.0h1v.s6.81f64dc47c25 from=translated src=- shape=27a86457 vocab=9934e86d
-/
theorem constantCoeff_wittCoord (k : ℕ) : constantCoeff (wittCoord k) = 0 := by
  by_contra h
  have h' : coeff (0 : ℕ →₀ ℕ) (wittCoord k) ≠ 0 := by rwa [← constantCoeff_eq]
  have hw := isWeightedHomogeneous_wittCoord k h'
  simp at hw

def geomSeries {A : Type*} [CommRing A] (c : A) (e : ℕ) : PowerSeries A :=
  PowerSeries.mk fun j => if e ∣ j then c ^ (j / e) else 0

/--
@isnad1 id=eq.0h4v.s7.9bd5bd79aa56 from=translated src=- shape=acf46681 vocab=9fcada71
-/
theorem coeff_geomSeries {A : Type*} [CommRing A] (c : A) (e j : ℕ) :
    PowerSeries.coeff j (geomSeries c e) = if e ∣ j then c ^ (j / e) else 0 :=
  PowerSeries.coeff_mk _ _

/--
@isnad1 id=eq.0h3v.s6.8f491f6b05f8 from=translated src=- shape=838018a9 vocab=950524c0
-/
@[simp] theorem constantCoeff_geomSeries {A : Type*} [CommRing A] (c : A) (e : ℕ) :
    PowerSeries.constantCoeff (geomSeries c e) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_geomSeries, ite_eq_left (dvd_zero e),
    Nat.zero_div, pow_zero]

/--
@isnad1 id=eq.1h3v.s7.dd9a3c908541 from=translated src=- shape=ae5e0b0f vocab=29a9ce86
-/
theorem one_sub_C_mul_X_pow_mul_geomSeries {A : Type*} [CommRing A] (c : A) {e : ℕ} (he : e ≠ 0) :
    (1 - PowerSeries.C c * PowerSeries.X ^ e) * geomSeries c e = 1 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero he
  ext j
  rw [mul_comm, coeff_mul_one_sub_C_mul_X_pow, coeff_geomSeries, PowerSeries.coeff_one]
  by_cases hj : k + 1 ≤ j
  · rw [ite_eq_left hj, coeff_geomSeries]
    have hj0 : j ≠ 0 := by omega
    rw [ite_eq_right hj0]
    by_cases hd : k + 1 ∣ j
    · have hd' : k + 1 ∣ j - (k + 1) := Nat.dvd_sub hd (dvd_refl _)
      rw [ite_eq_left hd, ite_eq_left hd']
      obtain ⟨q, rfl⟩ := hd
      have hq : 1 ≤ q := by
        rcases q with _ | q
        · simp at hj
        · exact Nat.succ_pos q
      rw [show (k + 1) * q - (k + 1) = (k + 1) * (q - 1) by rw [Nat.mul_sub, mul_one],
        Nat.mul_div_cancel_left _ (Nat.succ_pos k), Nat.mul_div_cancel_left _ (Nat.succ_pos k),
        ← pow_succ', Nat.sub_add_cancel hq, sub_self]
    · have hd' : ¬ k + 1 ∣ j - (k + 1) := by
        intro h
        apply hd
        have := Nat.dvd_add h (dvd_refl (k + 1))
        rwa [Nat.sub_add_cancel hj] at this
      rw [ite_eq_right hd, ite_eq_right hd', mul_zero, sub_zero]
  · rw [ite_eq_right hj, sub_zero]
    by_cases hj0 : j = 0
    · subst hj0
      rw [ite_eq_left (dvd_zero _), ite_eq_left rfl, Nat.zero_div, pow_zero]
    · rw [ite_eq_right hj0, ite_eq_right]
      rintro ⟨q, rfl⟩
      rcases q with _ | q
      · exact hj0 (mul_zero _)
      · apply hj
        calc k + 1 = (k + 1) * 1 := (mul_one _).symm
          _ ≤ (k + 1) * (q + 1) := Nat.mul_le_mul_left _ (by omega)

def frobFactor (n k : ℕ) : PowerSeries (MvPolynomial ℕ ℤ) :=
  geomSeries (wittCoord k ^ (n / Nat.gcd (k + 1) n)) ((k + 1) / Nat.gcd (k + 1) n) ^ Nat.gcd (k + 1) n

def frobPoly (n m : ℕ) : MvPolynomial ℕ ℤ :=
  PowerSeries.coeff (m + 1) (∏ k ∈ Finset.range (n * (m + 1)), frobFactor n k)

/--
@isnad1 id=eq.0h2v.s7.29b0f4b73b8c from=translated src=- shape=39d97471 vocab=ab1a4ab6
-/
@[simp] theorem constantCoeff_frobFactor (n k : ℕ) : PowerSeries.constantCoeff (frobFactor n k) = 1 := by
  rw [frobFactor, map_pow, constantCoeff_geomSeries, one_pow]

/--
@isnad1 id=isisobar.1h3v.s5.1623c7c48242 from=translated src=- shape=6a1f09de vocab=b164e281
-/
theorem isIsobaric_geomSeries {n e : ℕ} {c : MvPolynomial ℕ ℤ} (hc : IsWeightedHomogeneous awt c (n * e)) :
    IsIsobaric n (geomSeries c e) := by
  intro j
  rw [coeff_geomSeries]
  split_ifs with h
  · obtain ⟨q, rfl⟩ := h
    rcases Nat.eq_zero_or_pos e with he | he
    · subst he
      rw [zero_mul, Nat.zero_div, pow_zero, mul_zero]
      exact isWeightedHomogeneous_one ℤ awt
    · rw [Nat.mul_div_cancel_left _ he]
      have h := hc.pow q
      rwa [smul_eq_mul, show q * (n * e) = n * (e * q) by ring] at h
  · exact isWeightedHomogeneous_zero ℤ awt _

/--
@isnad1 id=isisobar.0h2v.s3.00981829fb85 from=translated src=- shape=e3ef7f21 vocab=19b49ae3
-/
theorem isIsobaric_frobFactor (n k : ℕ) : IsIsobaric n (frobFactor n k) := by
  refine (isIsobaric_geomSeries ?_).pow _
  have h := (isWeightedHomogeneous_wittCoord k).pow (n / Nat.gcd (k + 1) n)
  rw [smul_eq_mul] at h
  convert h using 1
  set g := Nat.gcd (k + 1) n with hg
  have hd : g ∣ k + 1 := Nat.gcd_dvd_left _ _
  have hd' : g ∣ n := Nat.gcd_dvd_right _ _
  calc n * ((k + 1) / g) = n / g * g * ((k + 1) / g) := by rw [Nat.div_mul_cancel hd']
    _ = n / g * (g * ((k + 1) / g)) := by ring
    _ = n / g * (k + 1) := by rw [Nat.mul_div_cancel' hd]

/--
@isnad1 id=isweight.0h2v.s5.be9fd2fde8dd from=translated src=- shape=b410ca37 vocab=25cc4402
-/
theorem isWeightedHomogeneous_frobPoly (n m : ℕ) :
    IsWeightedHomogeneous awt (frobPoly n m) (n * (m + 1)) :=
  (IsIsobaric.prod _ _ fun k _ => isIsobaric_frobFactor n k) (m + 1)

/--
@isnad1 id=eq.1h2v.s6.b6c18a364530 from=translated src=- shape=172af4a9 vocab=a1b3c870
-/
theorem constantCoeff_frobPoly {n : ℕ} (hn : n ≠ 0) (m : ℕ) : constantCoeff (frobPoly n m) = 0 := by
  by_contra h
  have h' : coeff (0 : ℕ →₀ ℕ) (frobPoly n m) ≠ 0 := by rwa [← constantCoeff_eq]
  have hw := isWeightedHomogeneous_frobPoly n m h'
  simp only [Finsupp.weight_apply, Finsupp.sum_zero_index] at hw
  exact absurd hw.symm (Nat.mul_ne_zero hn (Nat.succ_ne_zero m))

/--
@isnad1 id=eq.0h1v.s5.10e44be02ac1 from=translated src=- shape=73ead03e vocab=a40a4ada
-/
theorem frobPoly_zero_left (m : ℕ) : frobPoly 0 m = 0 := by
  rw [frobPoly, zero_mul, Finset.range_zero, Finset.prod_empty, PowerSeries.coeff_one, ite_eq_right]
  exact Nat.succ_ne_zero m

/--
@isnad1 id=eq.0h1v.s6.fc24d565d1dd from=translated src=- shape=ba7c7d8d vocab=6888d971
-/
theorem genSeries_eq_killProd_mul_prod_geomSeries (K : ℕ) :
    genSeries = killProd K * ∏ k ∈ Finset.range K, geomSeries (wittCoord k) (k + 1) := by
  rw [killProd_eq_mul_prod, mul_assoc, ← Finset.prod_mul_distrib, Finset.prod_eq_one, mul_one]
  intro k _
  exact one_sub_C_mul_X_pow_mul_geomSeries _ (Nat.succ_ne_zero k)

/--
@isnad1 id=eq.1h2v.s9.6db12da8ad4b from=translated src=- shape=4c11c740 vocab=93ec4a17
-/
theorem coeff_prod_geomSeries_wittCoord {K j : ℕ} (hj : j ≤ K) :
    PowerSeries.coeff j (∏ k ∈ Finset.range K, geomSeries (wittCoord k) (k + 1)) =
      PowerSeries.coeff j genSeries := by
  rw [genSeries_eq_killProd_mul_prod_geomSeries K, PowerSeries.coeff_mul,
    Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk, Finset.sum_range_succ', Nat.sub_zero,
    PowerSeries.coeff_zero_eq_constantCoeff_apply, constantCoeff_killProd, one_mul,
    Finset.sum_eq_zero, zero_add]
  intro i hi
  rw [coeff_killProd_eq_zero (Nat.succ_pos i) (by have := Finset.mem_range.mp hi; omega), zero_mul]

/--
@isnad1 id=eq.0h1v.s5.3a25b1650fad from=translated src=- shape=9a6aa7f3 vocab=8f5e75ac
-/
theorem frobFactor_one (k : ℕ) : frobFactor 1 k = geomSeries (wittCoord k) (k + 1) := by
  rw [frobFactor, Nat.gcd_one_right, Nat.div_one, Nat.div_one, pow_one, pow_one]

/--
@isnad1 id=eq.0h1v.s4.8426e876c913 from=translated src=- shape=f61b05c9 vocab=e0e24e36
-/
theorem frobPoly_one (m : ℕ) : frobPoly 1 m = X m := by
  rw [frobPoly, one_mul]
  simp only [frobFactor_one]
  rw [coeff_prod_geomSeries_wittCoord le_rfl, coeff_genSeries_succ]

section OmegaInv

variable {A : Type*} [CommRing A] (t : A)

def evalOmegaInv : PowerSeries (MvPolynomial ℕ ℤ) →+* PowerSeries A :=
  PowerSeries.map (MvPolynomial.aeval fun m : ℕ => t ^ (m + 1)).toRingHom

/--
@isnad1 id=eq.0h4v.s9.5b4fc2cfc264 from=translated src=- shape=aa93c428 vocab=772d7dc3
-/
theorem coeff_evalOmegaInv (P : PowerSeries (MvPolynomial ℕ ℤ)) (j : ℕ) :
    PowerSeries.coeff j (evalOmegaInv t P) =
      MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) (PowerSeries.coeff j P) :=
  PowerSeries.coeff_map _ _ _

/--
@isnad1 id=eq.0h2v.s7.0574816bc1dc from=translated src=- shape=cffd7813 vocab=b8c6bf71
-/
theorem evalOmegaInv_genSeries : evalOmegaInv t genSeries = geomSeries t 1 := by
  ext j
  rw [coeff_evalOmegaInv, coeff_geomSeries, ite_eq_left (one_dvd j), Nat.div_one]
  cases j with
  | zero => rw [coeff_genSeries_zero, map_one, pow_zero]
  | succ m => rw [coeff_genSeries_succ, MvPolynomial.aeval_X]

/--
@isnad1 id=eq.0h4v.s9.3e4cfc95d4d7 from=translated src=- shape=b1dbc5c3 vocab=1935a837
-/
theorem evalOmegaInv_C_mul_X_pow (c : MvPolynomial ℕ ℤ) (e : ℕ) :
    evalOmegaInv t (PowerSeries.C c * PowerSeries.X ^ e) =
      PowerSeries.C (MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) c) * PowerSeries.X ^ e := by
  rw [evalOmegaInv, map_mul, map_pow]
  simp [PowerSeries.map_C, PowerSeries.map_X]

/--
@isnad1 id=eq.0h3v.s7.8f16b52f6060 from=translated src=- shape=386cf791 vocab=3e2e073b
-/
theorem evalOmegaInv_killProd_succ (k : ℕ) : evalOmegaInv t (killProd (k + 1)) = 1 := by
  induction k with
  | zero =>
    rw [killProd_succ, map_mul, killProd_zero, evalOmegaInv_genSeries, map_sub, map_one,
      evalOmegaInv_C_mul_X_pow, wittCoord_zero, MvPolynomial.aeval_X, zero_add, pow_one, mul_comm]
    exact one_sub_C_mul_X_pow_mul_geomSeries t one_ne_zero
  | succ k ih =>
    rw [killProd_succ, map_mul, ih, one_mul, map_sub, map_one, evalOmegaInv_C_mul_X_pow, wittCoord_eq,
      ← coeff_evalOmegaInv, ih, PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero _), map_zero, zero_mul,
      sub_zero]

/--
@isnad1 id=eq.0h3v.s7.a46705a75fd4 from=translated src=- shape=c3c60865 vocab=314e13a7
-/
theorem aeval_omegaInv_wittCoord (k : ℕ) :
    MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) (wittCoord k) = if k = 0 then t else 0 := by
  cases k with
  | zero => rw [wittCoord_zero, MvPolynomial.aeval_X, ite_eq_left rfl, zero_add, pow_one]
  | succ k =>
    rw [ite_eq_right (Nat.succ_ne_zero k), wittCoord_eq, ← coeff_evalOmegaInv, evalOmegaInv_killProd_succ,
      PowerSeries.coeff_one, ite_eq_right (Nat.succ_ne_zero _)]

/--
@isnad1 id=eq.0h4v.s8.16d89c528b4b from=translated src=- shape=795e0c69 vocab=1e3432d9
-/
theorem evalOmegaInv_geomSeries (c : MvPolynomial ℕ ℤ) (e : ℕ) :
    evalOmegaInv t (geomSeries c e) = geomSeries (MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) c) e := by
  ext j
  rw [coeff_evalOmegaInv, coeff_geomSeries, coeff_geomSeries]
  split_ifs
  · rw [map_pow]
  · rw [map_zero]

omit t in
/--
@isnad1 id=eq.1h2v.s5.f950de02a923 from=translated src=- shape=9faa9157 vocab=00e65010
-/
theorem geomSeries_zero {e : ℕ} (he : e ≠ 0) : geomSeries (0 : A) e = 1 := by
  ext j
  rw [coeff_geomSeries, PowerSeries.coeff_one]
  by_cases hj : j = 0
  · subst hj; rw [ite_eq_left (dvd_zero e), ite_eq_left rfl, Nat.zero_div, pow_zero]
  · rw [ite_eq_right hj]
    split_ifs with h
    · rw [zero_pow]
      intro h0
      rw [Nat.div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · exact he h0
      · exact hj (Nat.eq_zero_of_dvd_of_lt h h0)
    · rfl

/--
@isnad1 id=eq.1h4v.s7.81447b022849 from=translated src=- shape=93a624ca vocab=b19294a0
-/
theorem evalOmegaInv_frobFactor {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    evalOmegaInv t (frobFactor n k) = if k = 0 then geomSeries (t ^ n) 1 else 1 := by
  rw [frobFactor, map_pow, evalOmegaInv_geomSeries, map_pow, aeval_omegaInv_wittCoord]
  have hg : 0 < Nat.gcd (k + 1) n := Nat.gcd_pos_of_pos_left _ (Nat.succ_pos k)
  split_ifs with hk
  · subst hk
    rw [zero_add, Nat.gcd_one_left, Nat.div_one, Nat.div_one, pow_one]
  · have h1 : n / Nat.gcd (k + 1) n ≠ 0 :=
      Nat.div_ne_zero_iff.mpr ⟨hg.ne', Nat.gcd_le_right _ (Nat.pos_of_ne_zero hn)⟩
    have h2 : (k + 1) / Nat.gcd (k + 1) n ≠ 0 :=
      Nat.div_ne_zero_iff.mpr ⟨hg.ne', Nat.gcd_le_left _ (Nat.succ_pos k)⟩
    rw [zero_pow h1, geomSeries_zero h2, one_pow]

/--
@isnad1 id=eq.1h4v.s7.32c41b33cedd from=translated src=- shape=2fabe4c3 vocab=78a0c45e
-/
theorem aeval_omegaInv_frobPoly {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) (frobPoly n m) = t ^ (n * (m + 1)) := by
  rw [frobPoly, ← coeff_evalOmegaInv, map_prod]
  simp only [evalOmegaInv_frobFactor t hn]
  have h0 : (0 : ℕ) ∈ Finset.range (n * (m + 1)) :=
    Finset.mem_range.mpr (Nat.mul_pos (Nat.pos_of_ne_zero hn) (Nat.succ_pos m))
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.filter_eq' , ite_eq_left h0,
    Finset.prod_singleton, coeff_geomSeries, ite_eq_left (one_dvd _), Nat.div_one, ← pow_mul]

end OmegaInv

def projPoly (p k : ℕ) : MvPolynomial ℕ ℤ := wittCoord (p ^ k - 1)

/--
@isnad1 id=eq.0h1v.s4.a1fcbad35333 from=translated src=- shape=6b31142c vocab=208def5f
-/
@[simp] theorem projPoly_zero (p : ℕ) : projPoly p 0 = X 0 := by
  rw [projPoly, pow_zero, Nat.sub_self, wittCoord_zero]

/--
@isnad1 id=isweight.1h2v.s5.faf9e5392927 from=translated src=- shape=2bf0f5e2 vocab=926b0605
-/
theorem isWeightedHomogeneous_projPoly {p : ℕ} (hp : 0 < p) (k : ℕ) :
    IsWeightedHomogeneous awt (projPoly p k) (p ^ k) := by
  have h := isWeightedHomogeneous_wittCoord (p ^ k - 1)
  rwa [Nat.sub_add_cancel (Nat.one_le_pow k p hp)] at h

/--
@isnad1 id=eq.0h2v.s6.004ea2821699 from=translated src=- shape=789817bf vocab=d4135248
-/
theorem constantCoeff_projPoly (p k : ℕ) : constantCoeff (projPoly p k) = 0 :=
  constantCoeff_wittCoord _

/--
@isnad1 id=eq.1h4v.s7.9b10fa2f2176 from=translated src=- shape=107b6a2b vocab=ab18635f
-/
theorem aeval_omegaInv_projPoly {A : Type*} [CommRing A] (t : A) {p : ℕ} (hp : 2 ≤ p) (k : ℕ) :
    MvPolynomial.aeval (fun m : ℕ => t ^ (m + 1)) (projPoly p k) = if k = 0 then t else 0 := by
  rw [projPoly, aeval_omegaInv_wittCoord]
  cases k with
  | zero => rw [pow_zero, Nat.sub_self]
  | succ k =>
    rw [ite_eq_right (Nat.succ_ne_zero k), ite_eq_right]
    have : p ^ (k + 1) ≥ 2 := le_trans hp (Nat.le_self_pow (Nat.succ_ne_zero k) p)
    omega

section Families

variable (R : Type u) [CommRing R]

def toFam (P : MvPolynomial ℕ ℤ) : MvPowerSeries ℕ R :=
  ↑(MvPolynomial.map (Int.castRingHom R) P)

/--
@isnad1 id=eq.0h3v.s7.62df87bbc546 from=translated src=- shape=934eaf67 vocab=5d506501
-/
theorem coeff_toFam (P : MvPolynomial ℕ ℤ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (toFam R P) = ((coeff e P : ℤ) : R) := by
  rw [toFam, MvPolynomial.coeff_coe, coeff_map, eq_intCast]

/--
@isnad1 id=eq.1h2v.s7.cee09f882b24 from=translated src=- shape=185df5a8 vocab=d7db3cb3
-/
theorem constantCoeff_toFam {P : MvPolynomial ℕ ℤ} (hP : constantCoeff P = 0) :
    MvPowerSeries.constantCoeff (toFam R P) = 0 := by
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_toFam, ← constantCoeff_eq, hP,
    Int.cast_zero]

/--
@isnad1 id=eq.2h4v.s8.049be84a7b58 from=translated src=- shape=b7e1f939 vocab=71c7ec8d
-/
theorem weight_eq_of_coeff_toFam_ne_zero {P : MvPolynomial ℕ ℤ} {w : ℕ}
    (hP : IsWeightedHomogeneous awt P w) {e : ℕ →₀ ℕ} (h : MvPowerSeries.coeff e (toFam R P) ≠ 0) :
    Finsupp.weight awt e = w := by
  rw [coeff_toFam] at h
  exact hP fun h0 => h (by rw [h0, Int.cast_zero])

def wittCoordFam : ℕ → MvPowerSeries ℕ R := fun k => toFam R (wittCoord k)

def frobFam (n : ℕ) : ℕ → MvPowerSeries ℕ R := fun m => toFam R (frobPoly n m)

def projFam (p : ℕ) : ℕ → MvPowerSeries ℕ R := fun k => toFam R (projPoly p k)

/--
@isnad1 id=eq.0h2v.s4.ad668b6c668e from=translated src=- shape=b870ccd2 vocab=3a5cdfed
-/
@[simp] theorem wittCoordFam_apply (k : ℕ) : wittCoordFam R k = toFam R (wittCoord k) := rfl
/--
@isnad1 id=eq.0h3v.s4.4b4541dd89bb from=translated src=- shape=4be79521 vocab=ca09a84b
-/
@[simp] theorem frobFam_apply (n m : ℕ) : frobFam R n m = toFam R (frobPoly n m) := rfl
/--
@isnad1 id=eq.0h3v.s4.efd5a312e69c from=translated src=- shape=4be79521 vocab=9308ddd7
-/
@[simp] theorem projFam_apply (p k : ℕ) : projFam R p k = toFam R (projPoly p k) := rfl

/--
@isnad1 id=eq.0h2v.s5.72ecbe0efd5b from=translated src=- shape=01ca50bb vocab=01afff25
-/
theorem projFam_zero (p : ℕ) : projFam R p 0 = MvPowerSeries.X 0 := by
  rw [projFam_apply, projPoly_zero, toFam, map_X, MvPolynomial.coe_X]

/--
@isnad1 id=eq.0h1v.s4.804ded43442d from=translated src=- shape=f41ae187 vocab=c64a25f5
-/
theorem wittCoordFam_zero : wittCoordFam R 0 = MvPowerSeries.X 0 := by
  rw [wittCoordFam_apply, wittCoord_zero, toFam, map_X, MvPolynomial.coe_X]

/--
@isnad1 id=eq.0h2v.s6.1216f49330ca from=translated src=- shape=56a78aba vocab=b356007a
-/
theorem constantCoeff_wittCoordFam (k : ℕ) : MvPowerSeries.constantCoeff (wittCoordFam R k) = 0 :=
  constantCoeff_toFam R (constantCoeff_wittCoord k)

/--
@isnad1 id=eq.1h3v.s6.f2d41c3727ad from=translated src=- shape=efcf96df vocab=898754dd
-/
theorem constantCoeff_frobFam {n : ℕ} (hn : n ≠ 0) (m : ℕ) :
    MvPowerSeries.constantCoeff (frobFam R n m) = 0 :=
  constantCoeff_toFam R (constantCoeff_frobPoly hn m)

/--
@isnad1 id=eq.0h3v.s6.31bab8ea9a54 from=translated src=- shape=92b8670f vocab=04401315
-/
theorem constantCoeff_projFam (p k : ℕ) : MvPowerSeries.constantCoeff (projFam R p k) = 0 :=
  constantCoeff_toFam R (constantCoeff_projPoly p k)

/--
@isnad1 id=hassubst.0h1v.s3.9137f22d69fc from=translated src=- shape=5f0010f5 vocab=d0452013
-/
theorem hasSubst_wittCoordFam : MvPowerSeries.HasSubst (wittCoordFam R) := by
  refine ⟨fun k => by rw [constantCoeff_wittCoordFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_le_nat (Finsupp.weight awt e)).subset fun k hk => ?_
  have hw := weight_eq_of_coeff_toFam_ne_zero R (isWeightedHomogeneous_wittCoord k) hk
  show k ≤ Finsupp.weight awt e
  omega

/--
@isnad1 id=hassubst.0h2v.s4.f84a9b229735 from=translated src=- shape=c81d5aa3 vocab=f011bb0b
-/
theorem hasSubst_frobFam (n : ℕ) : MvPowerSeries.HasSubst (frobFam R n) := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : frobFam R 0 = 0 := by
      funext m
      rw [frobFam_apply, frobPoly_zero_left, toFam, map_zero, MvPolynomial.coe_zero]
      rfl
    rw [h0]
    exact MvPowerSeries.HasSubst.zero
  refine ⟨fun m => by rw [constantCoeff_frobFam R hn.ne']; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_le_nat (Finsupp.weight awt e)).subset fun m hm => ?_
  have hw := weight_eq_of_coeff_toFam_ne_zero R (isWeightedHomogeneous_frobPoly n m) hm
  show m ≤ Finsupp.weight awt e
  rw [hw]
  calc m ≤ m + 1 := Nat.le_succ m
    _ = 1 * (m + 1) := (one_mul _).symm
    _ ≤ n * (m + 1) := Nat.mul_le_mul_right _ hn

/--
@isnad1 id=hassubst.1h2v.s4.96588678bac5 from=translated src=- shape=dcf59c46 vocab=5cc4134a
-/
theorem hasSubst_projFam {p : ℕ} (hp : 2 ≤ p) : MvPowerSeries.HasSubst (projFam R p) := by
  refine ⟨fun k => by rw [constantCoeff_projFam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight awt e)).subset fun k hk => ?_
  have hw := weight_eq_of_coeff_toFam_ne_zero R (isWeightedHomogeneous_projPoly (by omega) k) hk
  show k < Finsupp.weight awt e
  rw [hw]
  exact Nat.lt_pow_self (by omega)

end Families

end BigWittLaw

end MvFormalGroup

end
