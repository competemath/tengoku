module

public import Tengoku.Seed.RingTheory.PowerSeries.Expand
public import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.FieldTheory.Finite.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Dieudonné-Dwork criterion for `r`-integrality of power series

The Dieudonné-Dwork criterion characterises when a formal power series with
rational coefficients has `r`-integral coefficients (denominators coprime to a
prime `r`):

> For `F ∈ 1 + T · ℚ[[T]]`, the coefficients of `F` are `r`-integral if and only
> if `F(T)^r / F(T^r) ∈ 1 + r · T · ℤ_(r)[[T]]`.

This is the substantive p-adic-algebra theorem behind the Artin-Hasse
exponential's `r`-integrality (`artinHasseExpSeries_coeff_isRIntegral` in
`ArtinHasse.lean`).

## References

* Alain M. Robert, *A Course in p-adic Analysis* (GTM 198, Springer 2000),
 §7.2 Theorem 1, pp. 188-190.
* Neal Koblitz, *p-adic Numbers, p-adic Analysis, and Zeta-Functions*
 (GTM 58, Springer 1984), §IV.2 Theorem 2, pp. 96-97.

This is a local file; a future cleanup may PR upstream.
-/

@[expose] public section

noncomputable section

namespace KummerCriterion

namespace Furtwaengler

namespace DieudonneDwork

/-- A rational is `r`-integral iff its denominator is coprime to `r`.-/
def IsRIntegralRat (r : ℕ) (q : ℚ) : Prop := (q.den : ℕ).Coprime r

/--
@isnad1 id=isrinteg.0h1v.s3.bd8b96f6a439 from=translated src=- shape=8ba9e24c vocab=2a633411
-/
theorem IsRIntegralRat.zero (r : ℕ) : IsRIntegralRat r 0 := by
  unfold IsRIntegralRat
  simp

/--
@isnad1 id=isrinteg.0h1v.s3.325ee46820cb from=translated src=- shape=8ba9e24c vocab=2a633411
-/
theorem IsRIntegralRat.one (r : ℕ) : IsRIntegralRat r 1 := by
  unfold IsRIntegralRat
  simp

/--
@isnad1 id=isrinteg.2h3v.s4.98f68a7b5fe1 from=translated src=- shape=d203bb48 vocab=006d016c
-/
theorem IsRIntegralRat.add {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    IsRIntegralRat r (q₁ + q₂) := by
  unfold IsRIntegralRat at h₁ h₂ ⊢
  refine Nat.Coprime.coprime_dvd_left (Rat.add_den_dvd q₁ q₂) ?_
  exact h₁.mul_left h₂

/--
@isnad1 id=isrinteg.1h2v.s3.c51de7eefeb3 from=translated src=- shape=d086edac vocab=1efd6160
-/
theorem IsRIntegralRat.neg {r : ℕ} {q : ℚ} (h : IsRIntegralRat r q) :
    IsRIntegralRat r (-q) := by
  unfold IsRIntegralRat at h ⊢
  rw [Rat.neg_den]
  exact h

/--
@isnad1 id=isrinteg.2h3v.s4.4e9e3838ed5e from=translated src=- shape=d203bb48 vocab=888f2d81
-/
theorem IsRIntegralRat.sub {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    IsRIntegralRat r (q₁ - q₂) := by
  rw [sub_eq_add_neg]
  exact h₁.add h₂.neg

/--
@isnad1 id=isrinteg.2h3v.s4.7a8d1f80d05a from=translated src=- shape=d203bb48 vocab=4ee0c680
-/
theorem IsRIntegralRat.mul {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    IsRIntegralRat r (q₁ * q₂) := by
  unfold IsRIntegralRat at h₁ h₂ ⊢
  refine Nat.Coprime.coprime_dvd_left (Rat.mul_den_dvd q₁ q₂) ?_
  exact h₁.mul_left h₂

namespace IsRIntegralRat

/-- Residue of an `r`-integral rational modulo `r`.

The denominator is coprime to `r`, so it is a unit in `ZMod r`; the residue is
`num / den` computed in `ZMod r`.-/
noncomputable def toZMod {r : ℕ} (q : ℚ) (_h : IsRIntegralRat r q) : ZMod r :=
  (q.num : ZMod r) * (q.den : ZMod r)⁻¹

/--
@isnad1 id=eq.0h1v.s5.233b966ffc62 from=translated src=- shape=00199951 vocab=ba6223d1
-/
@[simp]
theorem toZMod_zero (r : ℕ) : toZMod (r := r) 0 (IsRIntegralRat.zero r) = 0 := by
  simp [toZMod]

/--
@isnad1 id=eq.0h1v.s5.963ed71a4715 from=translated src=- shape=00199951 vocab=c123fc04
-/
@[simp]
theorem toZMod_one (r : ℕ) : toZMod (r := r) 1 (IsRIntegralRat.one r) = 1 := by
  simp [toZMod]

/--
@isnad1 id=isunit.1h2v.s5.de34099df10c from=translated src=- shape=28058d0f vocab=7b54dd01
-/
theorem isUnit_den_zmod {r : ℕ} (q : ℚ) (h : IsRIntegralRat r q) :
    IsUnit (q.den : ZMod r) :=
  (ZMod.unitOfCoprime q.den h).isUnit

/--
@isnad1 id=eq.1h2v.s6.a8213c0237d0 from=translated src=- shape=83cf0cfc vocab=e0ad9362
-/
theorem den_mul_toZMod {r : ℕ} (q : ℚ) (h : IsRIntegralRat r q) :
    (q.den : ZMod r) * toZMod q h = (q.num : ZMod r) := by
  unfold toZMod
  calc
    (q.den : ZMod r) * ((q.num : ZMod r) * (q.den : ZMod r)⁻¹)
        = (q.num : ZMod r) * ((q.den : ZMod r) * (q.den : ZMod r)⁻¹) := by ring
    _ = (q.num : ZMod r) := by rw [ZMod.coe_mul_inv_eq_one q.den h, mul_one]

/--
@isnad1 id=eq.2h3v.s6.af789d4ddea5 from=translated src=- shape=cf3c2ca6 vocab=e0ad9362
-/
theorem toZMod_eq_of_den_mul_eq {r : ℕ} {q : ℚ} (h : IsRIntegralRat r q)
    {x : ZMod r} (hx : (q.den : ZMod r) * x = (q.num : ZMod r)) :
    x = toZMod q h :=
  (isUnit_den_zmod q h).mul_left_cancel (by rw [hx, den_mul_toZMod])

/--
@isnad1 id=eq.2h3v.s5.f8c2877ed053 from=translated src=- shape=de188246 vocab=57091523
-/
theorem toZMod_add {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    toZMod (q₁ + q₂) (h₁.add h₂) = toZMod q₁ h₁ + toZMod q₂ h₂ := by
  let d₁ : ZMod r := q₁.den
  let d₂ : ZMod r := q₂.den
  let D : ZMod r := (q₁ + q₂).den
  let n₁ : ZMod r := q₁.num
  let n₂ : ZMod r := q₂.num
  let N : ZMod r := (q₁ + q₂).num
  let x₁ : ZMod r := toZMod q₁ h₁
  let x₂ : ZMod r := toZMod q₂ h₂
  have hden₁ : d₁ * x₁ = n₁ := by
    simpa [d₁, x₁, n₁] using den_mul_toZMod q₁ h₁
  have hden₂ : d₂ * x₂ = n₂ := by
    simpa [d₂, x₂, n₂] using den_mul_toZMod q₂ h₂
  have hcross : N * d₁ * d₂ = (n₁ * d₂ + n₂ * d₁) * D := by
    simpa [N, d₁, d₂, n₁, n₂, D, mul_assoc] using
      (congrArg (fun z : ℤ => (z : ZMod r)) (Rat.add_num_den' q₁ q₂))
  symm
  refine toZMod_eq_of_den_mul_eq (h₁.add h₂) ?_
  change D * (x₁ + x₂) = N
  have hunit : IsUnit (d₁ * d₂) := by
    simpa [d₁, d₂] using IsUnit.mul (isUnit_den_zmod q₁ h₁) (isUnit_den_zmod q₂ h₂)
  exact hunit.mul_left_cancel <| by
    calc
      (d₁ * d₂) * (D * (x₁ + x₂))
          = ((d₁ * x₁) * d₂ + (d₂ * x₂) * d₁) * D := by ring
      _ = (n₁ * d₂ + n₂ * d₁) * D := by rw [hden₁, hden₂]
      _ = N * (d₁ * d₂) := by rw [← hcross]; ring
      _ = (d₁ * d₂) * N := by ring

/--
@isnad1 id=eq.1h2v.s5.f5d8ea588896 from=translated src=- shape=dfaf8b4e vocab=2ab6819a
-/
theorem toZMod_neg {r : ℕ} {q : ℚ} (h : IsRIntegralRat r q) :
    toZMod (-q) h.neg = -toZMod q h := by
  simp [toZMod]

/--
@isnad1 id=eq.2h3v.s6.4d6ae394c2f9 from=translated src=- shape=de188246 vocab=d907660b
-/
theorem toZMod_sub {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    toZMod (q₁ - q₂) (h₁.sub h₂) = toZMod q₁ h₁ - toZMod q₂ h₂ := by
  simpa [sub_eq_add_neg, toZMod_neg h₂] using toZMod_add h₁ h₂.neg

/--
@isnad1 id=eq.2h3v.s5.4c469abed48a from=translated src=- shape=de188246 vocab=a1aad1b9
-/
theorem toZMod_mul {r : ℕ} {q₁ q₂ : ℚ}
    (h₁ : IsRIntegralRat r q₁) (h₂ : IsRIntegralRat r q₂) :
    toZMod (q₁ * q₂) (h₁.mul h₂) = toZMod q₁ h₁ * toZMod q₂ h₂ := by
  let d₁ : ZMod r := q₁.den
  let d₂ : ZMod r := q₂.den
  let D : ZMod r := (q₁ * q₂).den
  let n₁ : ZMod r := q₁.num
  let n₂ : ZMod r := q₂.num
  let N : ZMod r := (q₁ * q₂).num
  let x₁ : ZMod r := toZMod q₁ h₁
  let x₂ : ZMod r := toZMod q₂ h₂
  have hden₁ : d₁ * x₁ = n₁ := by
    simpa [d₁, x₁, n₁] using den_mul_toZMod q₁ h₁
  have hden₂ : d₂ * x₂ = n₂ := by
    simpa [d₂, x₂, n₂] using den_mul_toZMod q₂ h₂
  have hcross : N * d₁ * d₂ = (n₁ * n₂) * D := by
    simpa [N, d₁, d₂, n₁, n₂, D, mul_assoc] using
      (congrArg (fun z : ℤ => (z : ZMod r)) (Rat.mul_num_den' q₁ q₂))
  symm
  refine toZMod_eq_of_den_mul_eq (h₁.mul h₂) ?_
  change D * (x₁ * x₂) = N
  have hunit : IsUnit (d₁ * d₂) := by
    simpa [d₁, d₂] using IsUnit.mul (isUnit_den_zmod q₁ h₁) (isUnit_den_zmod q₂ h₂)
  exact hunit.mul_left_cancel <| by
    calc
      (d₁ * d₂) * (D * (x₁ * x₂))
          = ((d₁ * x₁) * (d₂ * x₂)) * D := by ring
      _ = (n₁ * n₂) * D := by rw [hden₁, hden₂]
      _ = N * (d₁ * d₂) := by rw [← hcross]; ring
      _ = (d₁ * d₂) * N := by ring

/--
@isnad1 id=eq.2h4v.s7.1823c29b1d89 from=translated src=- shape=41f98d74 vocab=b62497ac
-/
theorem toZMod_finset_sum {r : ℕ} {ι : Type*} (s : Finset ι)
    (f : ι → ℚ) (hf : ∀ i ∈ s, IsRIntegralRat r (f i))
    (hsum : IsRIntegralRat r (Finset.sum s f)) :
    toZMod (Finset.sum s f) hsum =
      Finset.sum s (fun i => ((f i).num : ZMod r) * ((f i).den : ZMod r)⁻¹) := by
  classical
  revert hf hsum
  refine Finset.induction_on s ?empty ?insert
  · intro _ _
    simp [toZMod]
  · intro a s ha ih hf hsum
    have hfa : IsRIntegralRat r (f a) := hf a (by simp [ha])
    have hfs : ∀ i ∈ s, IsRIntegralRat r (f i) := fun i hi =>
      hf i (Finset.mem_insert_of_mem hi)
    have hsum_s : IsRIntegralRat r (Finset.sum s f) :=
      Finset.sum_induction _ _ (fun _ _ ha hb => ha.add hb) (IsRIntegralRat.zero r) hfs
    calc
      toZMod (Finset.sum (insert a s) f) hsum
          = toZMod (f a + Finset.sum s f) (hfa.add hsum_s) := by
            simp [toZMod, Finset.sum_insert ha]
      _ = toZMod (f a) hfa + toZMod (Finset.sum s f) hsum_s := by
            rw [toZMod_add hfa hsum_s]
      _ = Finset.sum (insert a s)
          (fun i => ((f i).num : ZMod r) * ((f i).den : ZMod r)⁻¹) := by
            rw [ih hfs hsum_s, Finset.sum_insert ha]
            rfl

/--
@isnad1 id=ex.2h2v.s5.3a77850637ba from=translated src=- shape=6a9da611 vocab=196da2f6
-/
theorem exists_eq_natCast_mul_of_toZMod_eq_zero {r : ℕ} {q : ℚ}
    (h : IsRIntegralRat r q) (hz : toZMod q h = 0) :
    ∃ q' : ℚ, IsRIntegralRat r q' ∧ q = (r : ℚ) * q' := by
  have hnum_zmod : (q.num : ZMod r) = 0 := by
    rw [← den_mul_toZMod q h, hz, mul_zero]
  have hnum_dvd : (r : ℤ) ∣ q.num := by
    simpa using (ZMod.intCast_zmod_eq_zero_iff_dvd q.num r).mp hnum_zmod
  rcases hnum_dvd with ⟨k, hk⟩
  refine ⟨Rat.divInt k (q.den : ℤ), ?_, ?_⟩
  · unfold IsRIntegralRat
    refine Nat.Coprime.coprime_dvd_left ?_ h
    have hden_dvd_int : (((Rat.divInt k (q.den : ℤ)).den : ℕ) : ℤ) ∣ (q.den : ℤ) :=
      Rat.den_dvd k (q.den : ℤ)
    exact Int.natCast_dvd_natCast.mp hden_dvd_int
  · calc
      q = Rat.divInt q.num (q.den : ℤ) := (Rat.num_divInt_den q).symm
      _ = Rat.divInt ((r : ℤ) * k) (q.den : ℤ) := by rw [hk]
      _ = (r : ℚ) * Rat.divInt k (q.den : ℤ) := by
        rw [Rat.divInt_eq_div, Rat.divInt_eq_div]
        norm_num
        ring

end IsRIntegralRat

/-- The subring of rationals whose denominators are coprime to `r`.-/
def rIntegralRatSubring (r : ℕ) : Subring ℚ where
  carrier := {q | IsRIntegralRat r q}
  zero_mem' := IsRIntegralRat.zero r
  one_mem' := IsRIntegralRat.one r
  add_mem' := fun h₁ h₂ => h₁.add h₂
  mul_mem' := fun h₁ h₂ => h₁.mul h₂
  neg_mem' := fun h => h.neg

/-- The residue homomorphism from `r`-integral rationals to `ZMod r`.-/
noncomputable def rIntegralToZMod (r : ℕ) : rIntegralRatSubring r →+* ZMod r where
  toFun q := IsRIntegralRat.toZMod (q : ℚ)
    (show IsRIntegralRat r (q : ℚ) from q.property)
  map_zero' := by
    change IsRIntegralRat.toZMod (r := r) 0 _ = 0
    simp
  map_one' := by
    change IsRIntegralRat.toZMod (r := r) 1 _ = 1
    simp
  map_add' q₁ q₂ := by
    let h₁ : IsRIntegralRat r (q₁ : ℚ) := q₁.property
    let h₂ : IsRIntegralRat r (q₂ : ℚ) := q₂.property
    change IsRIntegralRat.toZMod ((q₁ : ℚ) + (q₂ : ℚ)) _ =
      IsRIntegralRat.toZMod (q₁ : ℚ) h₁ +
        IsRIntegralRat.toZMod (q₂ : ℚ) h₂
    simpa [h₁, h₂] using IsRIntegralRat.toZMod_add h₁ h₂
  map_mul' q₁ q₂ := by
    let h₁ : IsRIntegralRat r (q₁ : ℚ) := q₁.property
    let h₂ : IsRIntegralRat r (q₂ : ℚ) := q₂.property
    change IsRIntegralRat.toZMod ((q₁ : ℚ) * (q₂ : ℚ)) _ =
      IsRIntegralRat.toZMod (q₁ : ℚ) h₁ *
        IsRIntegralRat.toZMod (q₂ : ℚ) h₂
    simpa [h₁, h₂] using IsRIntegralRat.toZMod_mul h₁ h₂

/--
@isnad1 id=eq.0h2v.s8.a31b6283e883 from=translated src=- shape=8a880597 vocab=eba8633f
-/
@[simp]
theorem rIntegralToZMod_apply (r : ℕ) (q : rIntegralRatSubring r) :
    rIntegralToZMod r q =
      IsRIntegralRat.toZMod (q : ℚ)
        (show IsRIntegralRat r (q : ℚ) from q.property) :=
  rfl

/--
@isnad1 id=eq.0h2v.s8.c1cef4f896e2 from=translated src=- shape=80b21770 vocab=6fcacbe6
-/
theorem powerSeries_expand_zmod {p : ℕ} [Fact p.Prime] (F : PowerSeries (ZMod p)) :
    PowerSeries.expand p ((Fact.out : Nat.Prime p).ne_zero) F = F ^ p := by
  have h :=
    MvPowerSeries.map_frobenius_expand
      (p := p) (hp := ((Fact.out : Nat.Prime p).ne_zero))
      (f := (F : MvPowerSeries Unit (ZMod p)))
  simpa [PowerSeries.expand, PowerSeries.map, ZMod.frobenius_zmod p] using h

/-- A formal power series in `ℚ[[T]]` is `r`-integral if every coefficient is.-/
def IsRIntegralPS (r : ℕ) (F : PowerSeries ℚ) : Prop :=
  ∀ n : ℕ, IsRIntegralRat r ((PowerSeries.coeff (R := ℚ) n) F)

/--
@isnad1 id=isrinteg.0h1v.s3.0ab74d93f465 from=translated src=- shape=83a34da1 vocab=7f3dd717
-/
theorem IsRIntegralPS.one (r : ℕ) : IsRIntegralPS r 1 := fun n => by
  rw [PowerSeries.coeff_one]
  by_cases h : n = 0
  · simp [h, IsRIntegralRat.one]
  · simp [h, IsRIntegralRat.zero]

/--
@isnad1 id=isrinteg.2h3v.s5.99f6f282c55e from=translated src=- shape=c66a59ad vocab=35a87a54
-/
theorem IsRIntegralPS.add {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    IsRIntegralPS r (F + G) := fun n => by
  rw [map_add]
  exact (hF n).add (hG n)

/--
@isnad1 id=isrinteg.1h2v.s5.cc362cb18d54 from=translated src=- shape=085e0dcf vocab=00b54455
-/
theorem IsRIntegralPS.neg {r : ℕ} {F : PowerSeries ℚ} (hF : IsRIntegralPS r F) :
    IsRIntegralPS r (-F) := fun n => by
  rw [map_neg]
  exact (hF n).neg

/--
@isnad1 id=isrinteg.2h3v.s5.5fa0fcc201c1 from=translated src=- shape=c66a59ad vocab=a9d19de8
-/
theorem IsRIntegralPS.sub {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    IsRIntegralPS r (F - G) := fun n => by
  rw [map_sub]
  exact (hF n).sub (hG n)

/--
@isnad1 id=isrinteg.2h3v.s5.ba0207b36abf from=translated src=- shape=c66a59ad vocab=e7ae39af
-/
theorem IsRIntegralPS.mul {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    IsRIntegralPS r (F * G) := fun n => by
  rw [PowerSeries.coeff_mul]
  exact Finset.sum_induction _ _ (fun _ _ ha hb => ha.add hb) (IsRIntegralRat.zero r)
    fun ⟨i, j⟩ _ => (hF i).mul (hG j)

/--
@isnad1 id=isrinteg.1h3v.s5.665ebb37b443 from=translated src=- shape=f986cd54 vocab=36ce3f3d
-/
theorem IsRIntegralPS.pow {r : ℕ} {F : PowerSeries ℚ} (hF : IsRIntegralPS r F)
    (k : ℕ) : IsRIntegralPS r (F ^ k) := by
  induction k with
  | zero => simpa using IsRIntegralPS.one r
  | succ k ih => rw [pow_succ]; exact ih.mul hF

/--
@isnad1 id=isrinteg.2h3v.s5.b4b3fa7cbab4 from=translated src=- shape=819b657e vocab=3e781c54
-/
theorem IsRIntegralPS.subst_X_pow {r k : ℕ} (hk : k ≠ 0) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) :
    IsRIntegralPS r (PowerSeries.subst (PowerSeries.X ^ k) F) := fun n => by
  rw [PowerSeries.coeff_subst_X_pow (R := ℚ) (S := ℚ) hk F n]
  by_cases hkn : k ∣ n
  · simp [hkn, hF (n / k)]
  · simp [hkn, IsRIntegralRat.zero]

/--
@isnad1 id=isrinteg.1h2v.s5.ae7178155240 from=translated src=- shape=d48654bc vocab=9ab7ae89
-/
theorem IsRIntegralPS.C {r : ℕ} {q : ℚ} (hq : IsRIntegralRat r q) :
    IsRIntegralPS r (PowerSeries.C q) := fun n => by
  rw [PowerSeries.coeff_C]
  by_cases hn : n = 0
  · simp [hn, hq]
  · simp [hn, IsRIntegralRat.zero]

/--
@isnad1 id=isrinteg.0h1v.s2.bf9dd024f4df from=translated src=- shape=4ee14ae4 vocab=e1866c46
-/
theorem IsRIntegralPS.X (r : ℕ) :
    IsRIntegralPS r (PowerSeries.X : PowerSeries ℚ) := fun n => by
  rw [PowerSeries.coeff_X]
  by_cases hn : n = 1
  · simp [hn, IsRIntegralRat.one]
  · simp [hn, IsRIntegralRat.zero]

/--
@isnad1 id=isrinteg.1h3v.s6.02e06f89212a from=translated src=- shape=76545abe vocab=7dc36499
-/
theorem IsRIntegralPS.C_mul_X_pow {r : ℕ} {q : ℚ} (hq : IsRIntegralRat r q)
    (n : ℕ) : IsRIntegralPS r (PowerSeries.C q * PowerSeries.X ^ n) :=
  (IsRIntegralPS.C hq).mul ((IsRIntegralPS.X r).pow n)

/--
@isnad1 id=isrinteg.1h4v.s5.d8a67dd5c6d4 from=translated src=- shape=4aeb2aac vocab=b35a81c6
-/
theorem IsRIntegralPS.finset_sum {r : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → PowerSeries ℚ) (hF : ∀ i ∈ s, IsRIntegralPS r (F i)) :
    IsRIntegralPS r (∑ i ∈ s, F i) := fun n => by
  classical
  rw [map_sum]
  exact Finset.sum_induction _ _ (fun _ _ ha hb => ha.add hb) (IsRIntegralRat.zero r)
    fun i hi => hF i hi n

/--
@isnad1 id=isrinteg.3h3v.s6.d382cdd26141 from=translated src=- shape=de0242c5 vocab=b890bf93
-/
theorem IsRIntegralPS.subst {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G)
    (hG0 : PowerSeries.constantCoeff G = 0) :
    IsRIntegralPS r (PowerSeries.subst G F) := fun n => by
  classical
  let hsubst : PowerSeries.HasSubst G :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hG0
  rw [PowerSeries.coeff_subst' hsubst F n]
  let term : ℕ → ℚ := fun d =>
    (PowerSeries.coeff (R := ℚ) d) F •
      (PowerSeries.coeff (R := ℚ) n) (G ^ d)
  have hterm : ∀ d : ℕ, IsRIntegralRat r (term d) := by
    intro d
    simpa [term, smul_eq_mul] using (hF d).mul ((hG.pow d) n)
  have hfinite := PowerSeries.coeff_subst_finite' hsubst F n
  rw [finsum_eq_sum _ hfinite]
  exact Finset.sum_induction _ _ (fun _ _ ha hb => ha.add hb) (IsRIntegralRat.zero r)
    fun d _ => hterm d

/--
@isnad1 id=isrinteg.3h2v.s8.e7f62a862457 from=translated src=- shape=35efe14c vocab=71510cfc
-/
theorem IsRIntegralPS.substInv_of_constantCoeff_zero_coeff_one
    {r : ℕ} {P : PowerSeries ℚ}
    [Invertible ((PowerSeries.coeff (R := ℚ) 1) P)]
    (hP : IsRIntegralPS r P)
    (_hP0 : PowerSeries.constantCoeff P = 0)
    (hP1 : (PowerSeries.coeff (R := ℚ) 1) P = 1) :
    IsRIntegralPS r (PowerSeries.substInv P) := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | _ | m
      · simp [PowerSeries.substInv, PowerSeries.substInvFun, IsRIntegralRat.zero]
      · simp [PowerSeries.substInv, PowerSeries.substInvFun, hP1, IsRIntegralRat.one]
      · let B : PowerSeries ℚ :=
          ∑ i : Fin (m + 2),
            PowerSeries.C (PowerSeries.substInvFun P i.1) * PowerSeries.X ^ i.1
        have hB : IsRIntegralPS r B := by
          dsimp [B]
          refine IsRIntegralPS.finset_sum (Finset.univ : Finset (Fin (m + 2)))
            (fun i => PowerSeries.C (PowerSeries.substInvFun P i.1) *
              PowerSeries.X ^ i.1) ?_
          intro i _
          have hi : i.1 < m + 2 := i.2
          have hcoeff : IsRIntegralRat r (PowerSeries.substInvFun P i.1) := by
            simpa [PowerSeries.substInv] using ih i.1 hi
          exact IsRIntegralPS.C_mul_X_pow hcoeff i.1
        have hB0 : PowerSeries.constantCoeff B = 0 := by
          rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply B]
          dsimp [B]
          simp only [map_sum, PowerSeries.coeff_C_mul_X_pow]
          apply Finset.sum_eq_zero
          intro i _
          rcases i with ⟨i, hi⟩
          cases i with
          | zero => simp [PowerSeries.substInvFun]
          | succ i => simp
        have hPB : IsRIntegralPS r (PowerSeries.subst B P) :=
          hP.subst hB hB0
        simpa [PowerSeries.substInv, PowerSeries.substInvFun, hP1, B] using
          (hPB (m + 2)).neg

namespace IsRMultipleIntegralPS

/--
@isnad1 id=ex.3h4v.s8.44a08e7e3c37 from=translated src=- shape=8acdbd51 vocab=78634250
-/
theorem coeff_mul_left_multiple_pos_right_integral_lt {r n : ℕ} {F G : PowerSeries ℚ}
    (hF0 : (PowerSeries.coeff (R := ℚ) 0) F = 0)
    (hFpos : ∀ i : ℕ, 1 ≤ i →
      ∃ q : ℚ, IsRIntegralRat r q ∧
        (PowerSeries.coeff (R := ℚ) i) F = (r : ℚ) * q)
    (hGlt : ∀ j : ℕ, j < n →
      IsRIntegralRat r ((PowerSeries.coeff (R := ℚ) j) G)) :
    ∃ q : ℚ, IsRIntegralRat r q ∧
      (PowerSeries.coeff (R := ℚ) n) (F * G) = (r : ℚ) * q := by
  classical
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal n
  let qTerm : ℕ × ℕ → ℚ := fun p =>
    if hp0 : p.1 = 0 then 0
    else
      (hFpos p.1 (Nat.succ_le_of_lt (Nat.pos_of_ne_zero hp0))).choose *
        (PowerSeries.coeff (R := ℚ) p.2) G
  refine ⟨Finset.sum s qTerm, ?_, ?_⟩
  · apply Finset.sum_induction
    · intro _ _ ha hb
      exact ha.add hb
    · exact IsRIntegralRat.zero r
    · intro p hp
      by_cases hp0 : p.1 = 0
      · rw [dite_eq_left hp0]
        exact IsRIntegralRat.zero r
      · have hp1pos : 0 < p.1 := Nat.pos_of_ne_zero hp0
        have hp2lt : p.2 < n := by
          have hsum : p.1 + p.2 = n := by
            simpa [s] using Finset.mem_antidiagonal.mp hp
          rw [← hsum]
          exact Nat.lt_add_of_pos_left hp1pos
        rw [dite_eq_right hp0]
        exact ((hFpos p.1 (Nat.succ_le_of_lt hp1pos)).choose_spec.1).mul
          (hGlt p.2 hp2lt)
  · calc
      (PowerSeries.coeff (R := ℚ) n) (F * G)
          = Finset.sum s (fun p =>
              (PowerSeries.coeff (R := ℚ) p.1) F *
                (PowerSeries.coeff (R := ℚ) p.2) G) := by
            simp [s, PowerSeries.coeff_mul]
      _ = Finset.sum s (fun p => (r : ℚ) * qTerm p) := by
            apply Finset.sum_congr rfl
            intro p hp
            by_cases hp0 : p.1 = 0
            · dsimp [qTerm]
              rw [dite_eq_left hp0]
              simp [hp0, hF0]
            · have hp1pos : 0 < p.1 := Nat.pos_of_ne_zero hp0
              have hcoeff :=
                (hFpos p.1 (Nat.succ_le_of_lt hp1pos)).choose_spec.2
              dsimp [qTerm]
              rw [dite_eq_right hp0]
              calc
                (PowerSeries.coeff (R := ℚ) p.1) F *
                    (PowerSeries.coeff (R := ℚ) p.2) G
                    = ((r : ℚ) *
                        (hFpos p.1 (Nat.succ_le_of_lt hp1pos)).choose) *
                        (PowerSeries.coeff (R := ℚ) p.2) G :=
                      congrArg
                        (fun x : ℚ => x * (PowerSeries.coeff (R := ℚ) p.2) G)
                        hcoeff
                _ = (r : ℚ) *
                      ((hFpos p.1 (Nat.succ_le_of_lt hp1pos)).choose *
                        (PowerSeries.coeff (R := ℚ) p.2) G) := by
                      ring
      _ = (r : ℚ) * Finset.sum s qTerm := by
            rw [Finset.mul_sum]

end IsRMultipleIntegralPS

namespace IsRIntegralPS

/-- The power series over the localized coefficient ring `ℤ_(r)` represented
by an `r`-integral rational power series.-/
noncomputable def toSubringPS {r : ℕ} {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) : PowerSeries (rIntegralRatSubring r) :=
  PowerSeries.mk fun n =>
    (⟨(PowerSeries.coeff (R := ℚ) n) F, hF n⟩ : rIntegralRatSubring r)

/--
@isnad1 id=eq.1h3v.s11.e2c5fe1f0da8 from=translated src=- shape=4a0d7414 vocab=fe2e2f12
-/
@[simp]
theorem coeff_toSubringPS {r : ℕ} {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (n : ℕ) :
    (PowerSeries.coeff (R := rIntegralRatSubring r) n) hF.toSubringPS =
      (⟨(PowerSeries.coeff (R := ℚ) n) F, hF n⟩ : rIntegralRatSubring r) := by
  simp [toSubringPS]

/--
@isnad1 id=eq.1h2v.s9.09d6ae3fc647 from=translated src=- shape=215aaf03 vocab=94ef0e64
-/
@[simp]
theorem map_toSubringPS_subtype {r : ℕ} {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) :
    PowerSeries.map (rIntegralRatSubring r).subtype hF.toSubringPS = F := by
  ext n
  simp

/--
@isnad1 id=eq.2h2v.s9.531fcfa6a72a from=translated src=- shape=f14f8cea vocab=8f3ebd92
-/
theorem constantCoeff_toSubringPS_eq_zero {r : ℕ} {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hF0 : PowerSeries.constantCoeff F = 0) :
    PowerSeries.constantCoeff hF.toSubringPS = 0 := by
  apply Subtype.ext
  change (PowerSeries.coeff (R := ℚ) 0) F = 0
  simpa [PowerSeries.coeff_zero_eq_constantCoeff] using hF0

/--
@isnad1 id=eq.3h3v.s8.59b73dd58c7a from=translated src=- shape=48174a56 vocab=83030542
-/
theorem toSubringPS_subst {r : ℕ} {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G)
    (hG0 : PowerSeries.constantCoeff G = 0) :
    (hF.subst hG hG0).toSubringPS =
      PowerSeries.subst hG.toSubringPS hF.toSubringPS := by
  let ι : rIntegralRatSubring r →+* ℚ := (rIntegralRatSubring r).subtype
  have hG0_sub : PowerSeries.constantCoeff hG.toSubringPS = 0 :=
    hG.constantCoeff_toSubringPS_eq_zero hG0
  let hsubst : PowerSeries.HasSubst hG.toSubringPS :=
    PowerSeries.HasSubst.of_constantCoeff_zero' hG0_sub
  apply PowerSeries.map_injective ι (rIntegralRatSubring r).subtype_injective
  calc
    PowerSeries.map ι (hF.subst hG hG0).toSubringPS
        = PowerSeries.subst G F := by
          simp [ι]
    _ = PowerSeries.map ι (PowerSeries.subst hG.toSubringPS hF.toSubringPS) := by
          calc
            PowerSeries.subst G F =
                PowerSeries.subst (PowerSeries.map ι hG.toSubringPS)
                  (PowerSeries.map ι hF.toSubringPS) := by
              simp [ι]
            _ = PowerSeries.map ι (PowerSeries.subst hG.toSubringPS hF.toSubringPS) := by
              simpa using! (PowerSeries.map_subst (h := ι) hsubst hF.toSubringPS).symm

/-- Coefficientwise reduction modulo `r` of an `r`-integral rational power
series.-/
noncomputable def toZModPS {r : ℕ} {F : PowerSeries ℚ} (hF : IsRIntegralPS r F) :
    PowerSeries (ZMod r) :=
  PowerSeries.mk fun n =>
    IsRIntegralRat.toZMod ((PowerSeries.coeff (R := ℚ) n) F) (hF n)

/--
@isnad1 id=eq.1h3v.s8.797d7fdcd558 from=translated src=- shape=0d8a5528 vocab=544e7c5c
-/
@[simp]
theorem coeff_toZModPS {r : ℕ} {F : PowerSeries ℚ} (hF : IsRIntegralPS r F)
    (n : ℕ) :
    (PowerSeries.coeff (R := ZMod r) n) hF.toZModPS =
      IsRIntegralRat.toZMod ((PowerSeries.coeff (R := ℚ) n) F) (hF n) := by
  simp [toZModPS]

/-- Coefficientwise map of an `r`-integral rational power series along any
ring hom out of the localized coefficient ring `ℤ_(r)`.-/
noncomputable def mapTo {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) : PowerSeries A :=
  PowerSeries.mk fun n =>
    φ (⟨(PowerSeries.coeff (R := ℚ) n) F, hF n⟩ : rIntegralRatSubring r)

/--
@isnad1 id=eq.1h4v.s9.96d3acda9173 from=translated src=- shape=45d72f5e vocab=fc4cc6ab
-/
theorem mapTo_eq_map_toSubringPS {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) :
    hF.mapTo φ = PowerSeries.map φ hF.toSubringPS := by
  ext n
  simp [mapTo, toSubringPS]

/--
@isnad1 id=eq.1h5v.s9.358d9995e814 from=translated src=- shape=ff058402 vocab=b6b961e2
-/
@[simp]
theorem coeff_mapTo {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (n : ℕ) :
    (PowerSeries.coeff (R := A) n) (hF.mapTo φ) =
      φ (⟨(PowerSeries.coeff (R := ℚ) n) F, hF n⟩ : rIntegralRatSubring r) := by
  simp [mapTo]

/--
@isnad1 id=eq.1h6v.s8.fb215a34e9ae from=translated src=- shape=c55f5d33 vocab=4e80f929
-/
theorem map_mapTo {r : ℕ} {A B : Type*} [CommSemiring A] [CommSemiring B]
    (φ : rIntegralRatSubring r →+* A) (ψ : A →+* B) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) :
    PowerSeries.map ψ (hF.mapTo φ) = hF.mapTo (ψ.comp φ) := by
  ext n
  simp [mapTo]

/--
@isnad1 id=eq.2h4v.s7.7b8e35b29ba6 from=translated src=- shape=aeac9f56 vocab=e62c2c97
-/
theorem mapTo_congr_proof {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) {F : PowerSeries ℚ}
    (hF hF' : IsRIntegralPS r F) : hF.mapTo φ = hF'.mapTo φ := by
  ext n
  simp [mapTo]

/--
@isnad1 id=eq.3h5v.s7.b5d6685a43f2 from=translated src=- shape=dc934308 vocab=e62c2c97
-/
theorem mapTo_eq_of_eq {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) (h : F = G) :
    hF.mapTo φ = hG.mapTo φ := by
  subst h
  exact mapTo_congr_proof φ hF hG

/--
@isnad1 id=eq.0h3v.s7.06310a67f537 from=translated src=- shape=fd72fc3b vocab=c437dbbb
-/
@[simp]
theorem mapTo_one {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) :
    (IsRIntegralPS.one r).mapTo φ = (1 : PowerSeries A) := by
  ext n
  by_cases hn : n = 0
  · calc
      (PowerSeries.coeff (R := A) n) ((IsRIntegralPS.one r).mapTo φ)
          = φ (1 : rIntegralRatSubring r) := by
            rw [coeff_mapTo]
            apply congrArg φ
            ext
            simp only [PowerSeries.coeff_one, hn, ↓reduceIte]
            rfl
      _ = 1 := by simp
      _ = (PowerSeries.coeff (R := A) n) (1 : PowerSeries A) := by
            simp only [PowerSeries.coeff_one, hn, ↓reduceIte]
  · calc
      (PowerSeries.coeff (R := A) n) ((IsRIntegralPS.one r).mapTo φ)
          = φ (0 : rIntegralRatSubring r) := by
            rw [coeff_mapTo]
            apply congrArg φ
            ext
            simp only [PowerSeries.coeff_one, hn, ↓reduceIte]
            rfl
      _ = 0 := by simp
      _ = (PowerSeries.coeff (R := A) n) (1 : PowerSeries A) := by
            simp only [PowerSeries.coeff_one, hn, ↓reduceIte]

/--
@isnad1 id=eq.0h3v.s7.73d3d3d1dbfc from=translated src=- shape=00b753b2 vocab=e94fd7a5
-/
@[simp]
theorem mapTo_X {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) :
    (IsRIntegralPS.X r).mapTo φ = (PowerSeries.X : PowerSeries A) := by
  ext n
  rw [coeff_mapTo]
  by_cases hn : n = 1
  · calc
      φ (⟨(PowerSeries.coeff (R := ℚ) n) (PowerSeries.X : PowerSeries ℚ),
            (IsRIntegralPS.X r) n⟩ : rIntegralRatSubring r)
          = φ (1 : rIntegralRatSubring r) := by
            apply congrArg φ
            ext
            simp only [PowerSeries.coeff_X, hn, ↓reduceIte]
            rfl
      _ = 1 := by simp
      _ = (PowerSeries.coeff (R := A) n) (PowerSeries.X : PowerSeries A) := by
            simp only [PowerSeries.coeff_X, hn, ↓reduceIte]
  · calc
      φ (⟨(PowerSeries.coeff (R := ℚ) n) (PowerSeries.X : PowerSeries ℚ),
            (IsRIntegralPS.X r) n⟩ : rIntegralRatSubring r)
          = φ (0 : rIntegralRatSubring r) := by
            apply congrArg φ
            ext
            simp only [PowerSeries.coeff_X, hn, ↓reduceIte]
            rfl
      _ = 0 := by simp
      _ = (PowerSeries.coeff (R := A) n) (PowerSeries.X : PowerSeries A) := by
            simp only [PowerSeries.coeff_X, hn, ↓reduceIte]

/--
@isnad1 id=eq.2h5v.s7.e269122226f9 from=translated src=- shape=ff2afdcc vocab=ee835529
-/
theorem mapTo_add {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    (hF.add hG).mapTo φ = hF.mapTo φ + hG.mapTo φ := by
  ext n
  calc
    (PowerSeries.coeff (R := A) n) ((hF.add hG).mapTo φ)
        = φ (⟨(PowerSeries.coeff (R := ℚ) n) (F + G), (hF.add hG) n⟩ :
            rIntegralRatSubring r) := by
          simp [mapTo]
    _ = φ ((⟨(PowerSeries.coeff (R := ℚ) n) F, hF n⟩ :
            rIntegralRatSubring r) +
          ⟨(PowerSeries.coeff (R := ℚ) n) G, hG n⟩) := by
          apply congrArg φ
          ext
          simp
    _ = φ (⟨(PowerSeries.coeff (R := ℚ) n) F, hF n⟩ :
            rIntegralRatSubring r) +
          φ (⟨(PowerSeries.coeff (R := ℚ) n) G, hG n⟩ :
            rIntegralRatSubring r) := by
          rw [map_add]
    _ = (PowerSeries.coeff (R := A) n) (hF.mapTo φ + hG.mapTo φ) := by
          simp [mapTo]

/--
@isnad1 id=eq.1h4v.s7.0c887f971c9f from=translated src=- shape=b162e377 vocab=2d46e90b
-/
theorem mapTo_neg {r : ℕ} {A : Type*} [CommRing A]
    (φ : rIntegralRatSubring r →+* A) {F : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) :
    hF.neg.mapTo φ = -hF.mapTo φ := by
  ext n
  calc
    (PowerSeries.coeff (R := A) n) (hF.neg.mapTo φ)
        = φ (⟨(PowerSeries.coeff (R := ℚ) n) (-F), hF.neg n⟩ :
            rIntegralRatSubring r) := by
          simp [mapTo]
    _ = φ (-(⟨(PowerSeries.coeff (R := ℚ) n) F, hF n⟩ :
            rIntegralRatSubring r)) := by
          apply congrArg φ
          ext
          simp
    _ = -φ (⟨(PowerSeries.coeff (R := ℚ) n) F, hF n⟩ :
            rIntegralRatSubring r) := by
          rw [map_neg]
    _ = (PowerSeries.coeff (R := A) n) (-hF.mapTo φ) := by
          simp [mapTo]

/--
@isnad1 id=eq.2h5v.s7.8cba5aa025c3 from=translated src=- shape=ff2afdcc vocab=0d595afa
-/
theorem mapTo_sub {r : ℕ} {A : Type*} [CommRing A]
    (φ : rIntegralRatSubring r →+* A) {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    (hF.sub hG).mapTo φ = hF.mapTo φ - hG.mapTo φ := by
  calc
    (hF.sub hG).mapTo φ
        = (hF.add hG.neg).mapTo φ :=
            mapTo_eq_of_eq φ (hF.sub hG) (hF.add hG.neg)
              (by rw [sub_eq_add_neg])
    _ = hF.mapTo φ + hG.neg.mapTo φ := mapTo_add φ hF hG.neg
    _ = hF.mapTo φ - hG.mapTo φ := by
          rw [mapTo_neg φ hG, sub_eq_add_neg]

/--
@isnad1 id=eq.2h5v.s7.0c051450cbbd from=translated src=- shape=ff2afdcc vocab=4702f854
-/
theorem mapTo_mul {r : ℕ} {A : Type*} [CommSemiring A]
    (φ : rIntegralRatSubring r →+* A) {F G : PowerSeries ℚ}
    (hF : IsRIntegralPS r F) (hG : IsRIntegralPS r G) :
    (hF.mul hG).mapTo φ = hF.mapTo φ * hG.mapTo φ := by
  classical
  ext n
  let s : Finset (ℕ × ℕ) := Finset.antidiagonal n
  let term : ℕ × ℕ → rIntegralRatSubring r := fun p =>
    (⟨(PowerSeries.coeff (R := ℚ) p.1) F, hF p.1⟩ : rIntegralRatSubring r) *
      (⟨(PowerSeries.coeff (R := ℚ) p.2) G, hG p.2⟩ : rIntegralRatSubring r)
  have hsum :
      (⟨(PowerSeries.coeff (R := ℚ) n) (F * G), (hF.mul hG) n⟩ :
          rIntegralRatSubring r) = ∑ p ∈ s, term p := by
    ext
    simp [s, term, PowerSeries.coeff_mul]
  calc
    (PowerSeries.coeff (R := A) n) ((hF.mul hG).mapTo φ)
        = φ (⟨(PowerSeries.coeff (R := ℚ) n) (F * G), (hF.mul hG) n⟩ :
            rIntegralRatSubring r) := by
          simp [mapTo]
    _ = φ (∑ p ∈ s, term p) := by rw [hsum]
    _ = ∑ p ∈ s, φ (term p) := by simp [map_sum]
    _ = ∑ p ∈ s,
          φ (⟨(PowerSeries.coeff (R := ℚ) p.1) F, hF p.1⟩ :
              rIntegralRatSubring r) *
            φ (⟨(PowerSeries.coeff (R := ℚ) p.2) G, hG p.2⟩ :
              rIntegralRatSubring r) := by
          refine Finset.sum_congr rfl ?_
          intro p _hp
          simp [term, map_mul]
    _ = (PowerSeries.coeff (R := A) n) (hF.mapTo φ * hG.mapTo φ) := by
          simp [PowerSeries.coeff_mul, s, mapTo]

end IsRIntegralPS
end DieudonneDwork

end Furtwaengler

end KummerCriterion

end
