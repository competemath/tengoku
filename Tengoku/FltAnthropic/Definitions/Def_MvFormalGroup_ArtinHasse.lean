import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

universe u

open PowerSeries

namespace MvFormalGroup

namespace ArtinHasse

variable (p : ℕ) [hp : Fact p.Prime]

def moebExponent (n : ℕ) : ℤ_[p] :=
  if p ∣ n then 0 else -(ArithmeticFunction.moebius n : ℤ_[p]) * Ring.inverse (n : ℤ_[p])

def moebFactor (n : ℕ) : ℤ_[p]⟦X⟧ :=
  if n = 0 then 1 else (binomialSeries ℤ_[p] (moebExponent p n)).subst (-(X : ℤ_[p]⟦X⟧) ^ n)

def moebProd (k : ℕ) : ℤ_[p]⟦X⟧ :=
  ∏ n ∈ (Finset.Ioc 0 k).filter (fun n => ¬ p ∣ n), moebFactor p n

def series : ℤ_[p]⟦X⟧ :=
  PowerSeries.mk fun k => coeff k (moebProd p k)

/--
@isnad1 id=hassubst.1h2v.s7.1cf8a9edb1c4 from=translated src=- shape=2b844c44 vocab=f82bdea2
-/
theorem hasSubst_neg_X_pow {n : ℕ} (hn : n ≠ 0) : HasSubst (-(X : ℤ_[p]⟦X⟧) ^ n) :=
  HasSubst.of_constantCoeff_zero' (by simp [hn])

/--
@isnad1 id=eq.0h2v.s7.5605a7a959d5 from=translated src=- shape=d7af38f2 vocab=82844efc
-/
theorem constantCoeff_moebFactor (n : ℕ) : constantCoeff (moebFactor p n) = 1 := by
  unfold moebFactor
  split_ifs with hn
  · exact map_one _
  · rw [← coeff_zero_eq_constantCoeff_apply, coeff_subst' (hasSubst_neg_X_pow p hn),
      finsum_eq_single _ 0 fun d hd => ?_]
    · simp
    · rw [coeff_zero_eq_constantCoeff_apply, map_pow, map_neg, map_pow, constantCoeff_X, zero_pow hn,
        neg_zero, zero_pow hd, smul_zero]

/--
@isnad1 id=eq.0h2v.s7.b9066a765472 from=translated src=- shape=d7af38f2 vocab=f9258104
-/
theorem constantCoeff_moebProd (k : ℕ) : constantCoeff (moebProd p k) = 1 := by
  rw [moebProd, map_prod]
  exact Finset.prod_eq_one fun n _ => constantCoeff_moebFactor p n

/--
@isnad1 id=eq.0h1v.s7.be5c4a551732 from=translated src=- shape=21b235e6 vocab=c3de2821
-/
theorem constantCoeff_series : constantCoeff (series p) = 1 := by
  rw [series, PowerSeries.constantCoeff_mk, coeff_zero_eq_constantCoeff_apply, constantCoeff_moebProd]

/--
@isnad1 id=eq.0h1v.s8.4e02953ad98a from=translated src=- shape=d13791a0 vocab=740ad725
-/
theorem coeff_one_series : coeff 1 (series p) = 1 := by
  rw [series, coeff_mk, moebProd]
  have hset : (Finset.Ioc 0 1).filter (fun n => ¬ p ∣ n) = {1} := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Ioc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h0, h1⟩, -⟩; omega
    · rintro rfl; exact ⟨⟨zero_lt_one, le_rfl⟩, hp.out.not_dvd_one⟩
  have hneg : ∀ d : ℕ, (-(X : ℤ_[p]⟦X⟧)) ^ d = ((-1 : ℤ_[p]) ^ d) • (X : ℤ_[p]⟦X⟧) ^ d := fun d => by
    rw [← neg_one_smul ℤ_[p] (X : ℤ_[p]⟦X⟧), smul_pow]
  rw [hset, Finset.prod_singleton, moebFactor, ite_eq_right one_ne_zero, pow_one,
    coeff_subst' (HasSubst.of_constantCoeff_zero' (by simp)), finsum_eq_single _ 1 fun d hd => ?_]
  · have hexp : moebExponent p 1 = -1 := by
      rw [moebExponent, ite_eq_right hp.out.not_dvd_one, ArithmeticFunction.moebius_apply_one, Int.cast_one,
        Nat.cast_one, Ring.inverse_one, mul_one]
    rw [binomialSeries_coeff, hexp, Ring.choose_one_right, hneg 1, map_smul, pow_one, pow_one,
      coeff_one_X]
    simp
  · rw [hneg d, map_smul, coeff_X_pow, ite_eq_right (Ne.symm hd), smul_zero, smul_zero]

variable {A : Type*} [CommRing A] [Algebra ℤ_[p] A]

def scaled (q : ℕ) (z : A) : A⟦X⟧ :=
  PowerSeries.mk fun k => if q ∣ k then algebraMap ℤ_[p] A (coeff (k / q) (series p)) * z ^ (k / q) else 0

/--
@isnad1 id=eq.0h5v.s9.990ae6c9e31d from=translated src=- shape=852362ec vocab=21673d04
-/
theorem coeff_scaled (q : ℕ) (z : A) (k : ℕ) :
    coeff k (scaled p q z) =
      if q ∣ k then algebraMap ℤ_[p] A (coeff (k / q) (series p)) * z ^ (k / q) else 0 :=
  coeff_mk _ _

/--
@isnad1 id=eq.0h4v.s6.81bf0c7dae69 from=translated src=- shape=55e40dd3 vocab=ed662cc7
-/
theorem constantCoeff_scaled (q : ℕ) (z : A) : constantCoeff (scaled p q z) = 1 := by
  rw [scaled, PowerSeries.constantCoeff_mk, ite_eq_left (dvd_zero q), Nat.zero_div,
    coeff_zero_eq_constantCoeff_apply, constantCoeff_series, map_one, pow_zero, mul_one]

/--
@isnad1 id=eq.0h6v.s8.2735c0c16c8b from=translated src=- shape=c45d2d6c vocab=1a21011b
-/
theorem map_scaled {B : Type*} [CommRing B] [Algebra ℤ_[p] B] (φ : A →ₐ[ℤ_[p]] B) (q : ℕ) (z : A) :
    PowerSeries.map (φ : A →+* B) (scaled p q z) = scaled p q (φ z) := by
  ext k
  rw [coeff_map, coeff_scaled, coeff_scaled]
  split_ifs
  · rw [RingHom.coe_coe, map_mul, map_pow, AlgHom.commutes]
  · exact map_zero _

def prodSeries (z : ℕ → A) (N : ℕ) : A⟦X⟧ :=
  ∏ m ∈ Finset.range N, scaled p (p ^ m) (z m)

/--
@isnad1 id=eq.0h4v.s6.bba1cdc4ecd4 from=translated src=- shape=f204e13d vocab=31fa32d8
-/
theorem constantCoeff_prodSeries (z : ℕ → A) (N : ℕ) : constantCoeff (prodSeries p z N) = 1 := by
  rw [prodSeries, map_prod]
  exact Finset.prod_eq_one fun m _ => constantCoeff_scaled p _ _

/--
@isnad1 id=eq.0h6v.s8.fb750a0f9edd from=translated src=- shape=dfe226c8 vocab=5b9cd969
-/
theorem map_prodSeries {B : Type*} [CommRing B] [Algebra ℤ_[p] B] (φ : A →ₐ[ℤ_[p]] B) (z : ℕ → A)
    (N : ℕ) : PowerSeries.map (φ : A →+* B) (prodSeries p z N) = prodSeries p (fun m => φ (z m)) N := by
  rw [prodSeries, prodSeries, map_prod]
  exact Finset.prod_congr rfl fun m _ => map_scaled p φ _ _

def coord (n : ℕ) : MvPolynomial ℕ ℤ_[p] :=
  coeff (n + 1) (prodSeries p (fun m => (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p])) (n + 1))

/--
@isnad1 id=eq.0h4v.s8.9bc41144919c from=translated src=- shape=81158fdc vocab=d82baf7d
-/
theorem aeval_coord (z : ℕ → A) (n : ℕ) :
    MvPolynomial.aeval z (coord p n) = coeff (n + 1) (prodSeries p z (n + 1)) := by
  rw [coord]
  change ((MvPolynomial.aeval z : MvPolynomial ℕ ℤ_[p] →ₐ[ℤ_[p]] A) : MvPolynomial ℕ ℤ_[p] →+* A)
      (coeff (n + 1) (prodSeries p (fun m => (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p])) (n + 1))) = _
  rw [← coeff_map, map_prodSeries]
  simp

/--
@isnad1 id=isweight.0h3v.s10.124d07c50e5c from=translated src=- shape=3b9bfd7c vocab=7b01d301
-/
theorem isWeightedHomogeneous_coeff_scaled_X (m k : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun i : ℕ => p ^ i)
      (coeff k (scaled p (p ^ m) (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p]))) k := by
  rw [coeff_scaled]
  split_ifs with hdvd
  · rw [MvPolynomial.algebraMap_eq]
    have h := ((MvPolynomial.isWeightedHomogeneous_X ℤ_[p] (fun i : ℕ => p ^ i) m).pow (k / p ^ m)).C_mul
      (coeff (k / p ^ m) (series p))
    have hw : (k / p ^ m) • (fun i : ℕ => p ^ i) m = k := by
      show (k / p ^ m) * p ^ m = k
      exact Nat.div_mul_cancel hdvd
    rwa [hw] at h
  · exact MvPolynomial.isWeightedHomogeneous_zero _ _ _

/--
@isnad1 id=isweight.0h2v.s5.f4964d1ee890 from=translated src=- shape=ad027fbc vocab=f96e3906
-/
theorem isWeightedHomogeneous_coord (n : ℕ) :
    MvPolynomial.IsWeightedHomogeneous (fun i : ℕ => p ^ i) (coord p n) (n + 1) := by
  classical
  rw [coord, prodSeries, coeff_prod]
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ fun l hl => ?_
  have hsum : (Finset.range (n + 1)).sum l = n + 1 := (Finset.mem_finsuppAntidiag.mp hl).1
  have h := MvPolynomial.IsWeightedHomogeneous.prod (Finset.range (n + 1))
    (fun m => coeff (l m) (scaled p (p ^ m) (MvPolynomial.X m : MvPolynomial ℕ ℤ_[p]))) (fun m => l m)
    (w := fun i : ℕ => p ^ i) fun m _ => isWeightedHomogeneous_coeff_scaled_X p m (l m)
  rwa [hsum] at h

/--
@isnad1 id=eq.0h1v.s5.48974a2582f6 from=translated src=- shape=70bb6684 vocab=8331b09b
-/
theorem coord_zero : coord p 0 = MvPolynomial.X 0 := by
  rw [coord, prodSeries, zero_add, Finset.prod_range_one, pow_zero, coeff_scaled, ite_eq_left (one_dvd _),
    Nat.div_one, coeff_one_series, map_one, one_mul, pow_one]

variable (R : Type u) [CommRing R] [CharP R p]

def toCharP : ℤ_[p] →+* R := (ZMod.castHom (dvd_refl p) R).comp (PadicInt.toZMod (p := p))

def fam (n : ℕ) : MvPowerSeries ℕ R :=
  ↑(MvPolynomial.map (toCharP p R) (coord p n))

/--
@isnad1 id=eq.0h4v.s8.f146865b13db from=translated src=- shape=d53a4155 vocab=5839af48
-/
theorem coeff_fam (n : ℕ) (e : ℕ →₀ ℕ) :
    MvPowerSeries.coeff e (fam p R n) = toCharP p R (MvPolynomial.coeff e (coord p n)) := by
  rw [fam, MvPolynomial.coeff_coe, MvPolynomial.coeff_map]

/--
@isnad1 id=eq.1h4v.s8.ef29874210a6 from=translated src=- shape=510b65b8 vocab=1453e2dd
-/
theorem weight_eq_of_coeff_fam_ne_zero {n : ℕ} {e : ℕ →₀ ℕ} (h : MvPowerSeries.coeff e (fam p R n) ≠ 0) :
    Finsupp.weight (fun i : ℕ => p ^ i) e = n + 1 := by
  rw [coeff_fam] at h
  have h' : MvPolynomial.coeff e (coord p n) ≠ 0 := fun h0 => h (by rw [h0, map_zero])
  exact isWeightedHomogeneous_coord p n h'

/--
@isnad1 id=eq.0h3v.s6.39181247f5aa from=translated src=- shape=5b05c80d vocab=b916add2
-/
theorem constantCoeff_fam (n : ℕ) : MvPowerSeries.constantCoeff (fam p R n) = 0 := by
  by_contra h
  have h' : MvPowerSeries.coeff (0 : ℕ →₀ ℕ) (fam p R n) ≠ 0 := by
    rwa [MvPowerSeries.coeff_zero_eq_constantCoeff]
  have hw := weight_eq_of_coeff_fam_ne_zero p R h'
  simp at hw

/--
@isnad1 id=hassubst.0h2v.s5.ff45421ddbb6 from=translated src=- shape=dc9c6959 vocab=f22d7cd5
-/
theorem hasSubst_fam : MvPowerSeries.HasSubst (fam p R) := by
  refine ⟨fun n => by rw [constantCoeff_fam]; exact IsNilpotent.zero, fun e => ?_⟩
  refine (Set.finite_lt_nat (Finsupp.weight (fun i : ℕ => p ^ i) e)).subset ?_
  intro n hn
  have hw := weight_eq_of_coeff_fam_ne_zero p R hn
  show n < Finsupp.weight (fun i : ℕ => p ^ i) e
  omega

/--
@isnad1 id=eq.0h2v.s5.0c646561969f from=translated src=- shape=80dd80b0 vocab=fa111793
-/
theorem fam_zero : fam p R 0 = MvPowerSeries.X 0 := by
  rw [fam, coord_zero, MvPolynomial.map_X, MvPolynomial.coe_X]

/--
@isnad1 id=eq.0h3v.s8.3a0292275765 from=translated src=- shape=430e0310 vocab=872035fa
-/
theorem coeff_single_zero_fam (n : ℕ) :
    MvPowerSeries.coeff (Finsupp.single 0 1) (fam p R n) = if n = 0 then 1 else 0 := by
  classical
  split_ifs with hn
  · subst hn
    rw [fam_zero, MvPowerSeries.coeff_X, ite_eq_left rfl]
  · by_contra h
    have hw := weight_eq_of_coeff_fam_ne_zero p R (Ne.symm h ∘ Eq.symm)
    rw [Finsupp.weight_single, pow_zero, smul_eq_mul, mul_one] at hw
    exact hn (by omega)

end ArtinHasse

end MvFormalGroup

end
