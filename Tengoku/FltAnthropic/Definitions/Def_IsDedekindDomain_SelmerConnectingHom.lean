import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace IsDedekindDomain.selmerGroup

open IsDedekindDomain
open scoped nonZeroDivisors

variable {R : Type} [CommRing R] [IsDedekindDomain R] {K : Type} [Field K] [Algebra R K] [IsFractionRing R K]
  (v : HeightOneSpectrum R)

/--
@isnad1 id=eq.0h4v.s7.0b55b788998e from=translated src=- shape=439cb3a4 vocab=5318463d
-/
theorem toAdd_valuationOfNeZero_eq_neg_count (x : Kˣ) :
    Multiplicative.toAdd (v.valuationOfNeZero x) = -FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K)) := by
  classical
  set r : R := (IsLocalization.sec R⁰ (x : K)).1 with hrdef
  set s : R⁰ := (IsLocalization.sec R⁰ (x : K)).2 with hsdef
  have hx : IsLocalization.mk' K r s = (x : K) := IsLocalization.mk'_sec K (x : K)
  have hr : r ≠ 0 := by
    intro h
    rw [h, IsLocalization.mk'_zero] at hx
    exact x.ne_zero hx.symm
  have hs : (s : R) ≠ 0 := nonZeroDivisors.ne_zero s.2

  set a : ℤ := ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ) with ha
  set b : ℤ := ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {(s : R)} : Ideal R)).factors : ℤ) with hb
  have h1 : (v.valuationOfNeZero x : WithZero (Multiplicative ℤ)) = WithZero.exp (-a - -b) := by
    rw [HeightOneSpectrum.valuationOfNeZero_eq, ← hx, HeightOneSpectrum.valuation_of_mk', HeightOneSpectrum.intValuation_if_neg _ hr,
      HeightOneSpectrum.intValuation_if_neg _ hs, WithZero.exp_sub]
  have h1' : v.valuationOfNeZero x = Multiplicative.ofAdd (-a - -b) := WithZero.coe_inj.1 h1

  have hspan : FractionalIdeal.spanSingleton R⁰ (x : K) * ((Ideal.span {(s : R)} : Ideal R) : FractionalIdeal R⁰ K) =
      ((Ideal.span {r} : Ideal R) : FractionalIdeal R⁰ K) := by
    rw [← hx]
    have := (FractionalIdeal.mk'_mul_coeIdeal_eq_coeIdeal K (I := Ideal.span {(s : R)}) (J := Ideal.span {r}) (x := r) s.2).2 (mul_comm _ _)
    simpa using this
  have hx0 : FractionalIdeal.spanSingleton R⁰ (x : K) ≠ 0 := FractionalIdeal.spanSingleton_ne_zero_iff.2 x.ne_zero
  have hs0 : ((Ideal.span {(s : R)} : Ideal R) : FractionalIdeal R⁰ K) ≠ 0 := by
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.span_singleton_eq_bot]; exact hs
  have hcount := congrArg (FractionalIdeal.count K v) hspan
  rw [FractionalIdeal.count_mul K v hx0 hs0,
    FractionalIdeal.count_coe K v (by rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hs),
    FractionalIdeal.count_coe K v (by rw [Ideal.zero_eq_bot, Ne, Ideal.span_singleton_eq_bot]; exact hr)] at hcount
  rw [h1', toAdd_ofAdd, ← ha, ← hb] at *
  omega

/--
@isnad1 id=iff.0h5v.s8.841e76fffbfd from=translated src=- shape=c7633c2e vocab=6a4f8f53
-/
theorem dvd_toAdd_valuationOfNeZero_iff (n : ℕ) (x : Kˣ) :
    (n : ℤ) ∣ Multiplicative.toAdd (v.valuationOfNeZero x) ↔ (n : ℤ) ∣ FractionalIdeal.count K v (FractionalIdeal.spanSingleton R⁰ (x : K)) := by
  rw [toAdd_valuationOfNeZero_eq_neg_count, dvd_neg]

end IsDedekindDomain.selmerGroup

noncomputable section

namespace IsDedekindDomain.selmerGroup

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ)

def primeClass (v : HeightOneSpectrum R) : ClassGroup R :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.2 (by simpa using v.ne_bot)⟩

abbrev sClasses : Subgroup (ClassGroup R) := Subgroup.closure (primeClass '' S)

abbrev ClassGroupModS : Type := ClassGroup R ⧸ sClasses S

/--
@isnad1 id=eq.0h3v.s9.7d130ed6f08d from=translated src=- shape=1c736a9b vocab=d9eb89c8
-/
theorem primeClass_eq_mk (v : HeightOneSpectrum R) :
    primeClass v = ClassGroup.mk K (Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.2 v.ne_bot)) := by
  rw [primeClass, ← ClassGroup.mk_mk0 K]
  congr 1

def radExp (x : Kˣ) (v : HeightOneSpectrum R) : ℤ :=
  if v ∈ S then 0 else count K v (spanSingleton R⁰ (x : K)) / n

/--
@isnad1 id=eventual.0h5v.s6.5fa71a6b89d8 from=translated src=- shape=b1d861b5 vocab=f4a085a1
-/
theorem radExp_finite (x : Kˣ) : ∀ᶠ v : HeightOneSpectrum R in Filter.cofinite, radExp K S n x v = 0 :=
  (finite_factors (spanSingleton R⁰ (x : K))).mono fun v hv => by simp [radExp, hv]

def rad (x : Kˣ) : FractionalIdeal R⁰ K := ∏ᶠ v : HeightOneSpectrum R, (v.asIdeal : FractionalIdeal R⁰ K) ^ radExp K S n x v

/--
@isnad1 id=eq.0h6v.s6.3f17b9af6236 from=translated src=- shape=fe53d059 vocab=b0b0f817
-/
theorem count_rad (x : Kˣ) (v : HeightOneSpectrum R) : count K v (rad K S n x) = radExp K S n x v :=
  count_finprod K v _ (radExp_finite K S n x)

/--
@isnad1 id=ne.0h5v.s7.0f20ef869506 from=translated src=- shape=666e6a42 vocab=51c74824
-/
theorem rad_ne_zero (x : Kˣ) : rad K S n x ≠ 0 := by
  rw [rad, finprod_def]
  split_ifs
  · exact Finset.prod_ne_zero_iff.2 fun v _ => zpow_ne_zero _ (coeIdeal_ne_zero.2 v.ne_bot)
  · exact one_ne_zero

theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0) (h : ∀ v, count K v I = count K v J) : I = J := by
  rw [← finprod_heightOneSpectrum_factorization' K hI, ← finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

def radClass (x : Kˣ) : ClassGroupModS S := QuotientGroup.mk (ClassGroup.mk K (Units.mk0 (rad K S n x) (rad_ne_zero K S n x)))

def IsSel (x : Kˣ) : Prop := ∀ v ∉ S, (n : ℤ) ∣ count K v (spanSingleton R⁰ (x : K))

variable {K S n}

/--
@isnad1 id=issel.2h6v.s7.9ffa78ba10fc from=translated src=- shape=525e6266 vocab=86bd8744
-/
theorem IsSel.mul {x y : Kˣ} (hx : IsSel K S n x) (hy : IsSel K S n y) : IsSel K S n (x * y) := fun v hv => by
  rw [Units.val_mul, ← spanSingleton_mul_spanSingleton, count_mul K v (spanSingleton_ne_zero_iff.2 x.ne_zero) (spanSingleton_ne_zero_iff.2 y.ne_zero)]
  exact dvd_add (hx v hv) (hy v hv)

/--
@isnad1 id=issel.0h5v.s7.1df4fc570bc4 from=translated src=- shape=4ad883e8 vocab=fb0af766
-/
theorem IsSel.pow (z : Kˣ) : IsSel K S n (z ^ n) := fun v _ => by
  rw [Units.val_pow_eq_pow_val, ← spanSingleton_pow, count_pow]
  exact dvd_mul_right _ _

variable (K S n)

/--
@isnad1 id=eq.2h7v.s7.7f02728f8223 from=translated src=- shape=0c809e12 vocab=bae605c0
-/
theorem radExp_mul {x y : Kˣ} (hx : IsSel K S n x) (_hy : IsSel K S n y) (v : HeightOneSpectrum R) :
    radExp K S n (x * y) v = radExp K S n x v + radExp K S n y v := by
  unfold radExp
  split_ifs with hv
  · simp
  · rw [Units.val_mul, ← spanSingleton_mul_spanSingleton, count_mul K v (spanSingleton_ne_zero_iff.2 x.ne_zero) (spanSingleton_ne_zero_iff.2 y.ne_zero)]
    exact Int.add_ediv_of_dvd_left (hx v hv)

/--
@isnad1 id=eq.2h6v.s8.10f9d4e831e4 from=translated src=- shape=1a5e428a vocab=a583e1cd
-/
theorem rad_mul {x y : Kˣ} (hx : IsSel K S n x) (hy : IsSel K S n y) : rad K S n (x * y) = rad K S n x * rad K S n y := by
  apply eq_of_count_eq K (rad_ne_zero K S n _) (mul_ne_zero (rad_ne_zero K S n x) (rad_ne_zero K S n y))
  intro v
  rw [count_mul K v (rad_ne_zero K S n x) (rad_ne_zero K S n y), count_rad, count_rad, count_rad, radExp_mul K S n hx hy]

/--
@isnad1 id=eq.2h6v.s8.fe41b8f068e1 from=translated src=- shape=c7c36e87 vocab=3ff802dc
-/
theorem radClass_mul {x y : Kˣ} (hx : IsSel K S n x) (hy : IsSel K S n y) : radClass K S n (x * y) = radClass K S n x * radClass K S n y := by
  unfold radClass
  rw [← QuotientGroup.mk_mul, ← map_mul]
  congr 2
  exact Units.ext (by simp [rad_mul K S n hx hy])

end IsDedekindDomain.selmerGroup

end

noncomputable section

namespace IsDedekindDomain.selmerGroup

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ)

/--
@isnad1 id=eq.0h3v.s9.41684345d98e from=translated src=- shape=f7d3c8c5 vocab=c22bd07a
-/
theorem mk_spanSingleton (z : Kˣ) :
    ClassGroup.mk K (Units.mk0 (spanSingleton R⁰ (z : K)) (spanSingleton_ne_zero_iff.2 z.ne_zero)) = 1 :=
  ClassGroup.mk_eq_one_iff.2 ⟨⟨(z : K), by simp [coe_spanSingleton]⟩⟩

def primeUnit (v : HeightOneSpectrum R) : (FractionalIdeal R⁰ K)ˣ := Units.mk0 (v.asIdeal : FractionalIdeal R⁰ K) (coeIdeal_ne_zero.2 v.ne_bot)

/--
@isnad1 id=eq.0h3v.s9.4fa9e4119bb9 from=translated src=- shape=a31587da vocab=e5ea6149
-/
theorem mk_primeUnit (v : HeightOneSpectrum R) : ClassGroup.mk K (primeUnit K v) = primeClass v := (primeClass_eq_mk K v).symm

/--
@isnad1 id=hasfinit.1h3v.s9.a44590a76325 from=translated src=- shape=f22864c4 vocab=ab3eb932
-/
theorem hasFiniteMulSupport_primeUnit_zpow (e : HeightOneSpectrum R → ℤ) (he : ∀ᶠ v in Filter.cofinite, e v = 0) :
    Function.HasFiniteMulSupport fun v => primeUnit K v ^ e v := by
  apply he.subset
  intro v hv
  simp only [Function.mem_mulSupport] at hv
  intro h
  exact hv (by rw [h, zpow_zero])

/--
@isnad1 id=eq.0h3v.s10.0dea3f520f01 from=translated src=- shape=f5484f1a vocab=cfd45c80
-/
theorem coe_finprod_primeUnit_zpow (e : HeightOneSpectrum R → ℤ) :
    ((∏ᶠ v, primeUnit K v ^ e v : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) = ∏ᶠ v, (v.asIdeal : FractionalIdeal R⁰ K) ^ e v := by
  rw [← Units.coeHom_apply, MonoidHom.map_finprod_of_injective (Units.coeHom (FractionalIdeal R⁰ K)) Units.val_injective]
  exact finprod_congr fun v => by rw [map_zpow, Units.coeHom_apply]; rfl

theorem eq_finprod_primeUnit (I : (FractionalIdeal R⁰ K)ˣ) (e : HeightOneSpectrum R → ℤ) (he : ∀ v, e v = count K v (Units.val I)) :
    I = (∏ᶠ v : HeightOneSpectrum R, (primeUnit K v ^ e v : (FractionalIdeal R⁰ K)ˣ) : (FractionalIdeal R⁰ K)ˣ) := by
  apply Units.ext
  rw [coe_finprod_primeUnit_zpow]
  rw [show e = fun v => count K v (Units.val I) from funext he]
  exact (finprod_heightOneSpectrum_factorization' K I.ne_zero).symm

/--
@isnad1 id=mem.1h4v.s9.9ec6fc0bbff2 from=translated src=- shape=08e13105 vocab=83a1cfa0
-/
theorem mk_mem_sClasses (I : (FractionalIdeal R⁰ K)ˣ) (hI : ∀ v ∉ S, count K v (I : FractionalIdeal R⁰ K) = 0) :
    ClassGroup.mk K I ∈ sClasses S := by
  have hfin := hasFiniteMulSupport_primeUnit_zpow K (fun v => count K v (Units.val I)) (finite_factors _)
  rw [eq_finprod_primeUnit K I (fun v => count K v (Units.val I)) (fun v => rfl), MonoidHom.map_finprod _ hfin]
  refine finprod_induction (· ∈ sClasses S) (Subgroup.one_mem _) (fun _ _ => Subgroup.mul_mem _) fun v => ?_
  by_cases hv : v ∈ S
  · rw [map_zpow, mk_primeUnit]
    exact Subgroup.zpow_mem _ (Subgroup.subset_closure (Set.mem_image_of_mem primeClass hv)) _
  · change ClassGroup.mk K (primeUnit K v ^ count K v (Units.val I)) ∈ sClasses S
    rw [hI v hv, zpow_zero, map_one]
    exact Subgroup.one_mem _

def radU (x : Kˣ) : (FractionalIdeal R⁰ K)ˣ := Units.mk0 (rad K S n x) (rad_ne_zero K S n x)

/--
@isnad1 id=eq.0h5v.s9.212630055a2e from=translated src=- shape=64b84c98 vocab=65e3f778
-/
theorem radClass_eq (x : Kˣ) : radClass K S n x = QuotientGroup.mk (ClassGroup.mk K (radU K S n x)) := rfl

variable [Fact (0 < n)]

/--
@isnad1 id=eq.0h5v.s7.c75fd78a970c from=translated src=- shape=a5bfdca0 vocab=a863d1b4
-/
theorem radClass_pow (z : Kˣ) : radClass K S n (z ^ n) = 1 := by
  have hn : (n : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : 0 < n).ne'

  let J : (FractionalIdeal R⁰ K)ˣ := ∏ᶠ v, primeUnit K v ^ (if v ∈ S then count K v (spanSingleton R⁰ (z : K)) else 0)
  have hJsupp : ∀ᶠ v in Filter.cofinite, (if v ∈ S then count K v (spanSingleton R⁰ (z : K)) else 0) = 0 :=
    (finite_factors (spanSingleton R⁰ (z : K))).mono fun v hv => by simp [hv]
  have hJcount : ∀ v, count K v (J : FractionalIdeal R⁰ K) = if v ∈ S then count K v (spanSingleton R⁰ (z : K)) else 0 := fun v => by
    rw [coe_finprod_primeUnit_zpow, count_finprod K v _ hJsupp]
  have hprod : radU K S n (z ^ n) * J = Units.mk0 (spanSingleton R⁰ (z : K)) (spanSingleton_ne_zero_iff.2 z.ne_zero) := by
    apply Units.ext
    apply eq_of_count_eq K (mul_ne_zero (rad_ne_zero K S n _) J.ne_zero) (spanSingleton_ne_zero_iff.2 z.ne_zero)
    intro v
    change count K v (rad K S n (z ^ n) * (J : FractionalIdeal R⁰ K)) = _
    rw [count_mul K v (rad_ne_zero K S n _) J.ne_zero, count_rad, hJcount, radExp]
    split_ifs with hv
    · simp
    · rw [Units.val_pow_eq_pow_val, ← spanSingleton_pow, count_pow, add_zero, mul_comm, Int.mul_ediv_cancel _ hn]
  have hJmem : ClassGroup.mk K J ∈ sClasses S := mk_mem_sClasses K S J fun v hv => by rw [hJcount, ite_eq_right hv]
  rw [radClass_eq, QuotientGroup.eq_one_iff]
  have : ClassGroup.mk K (radU K S n (z ^ n)) = (ClassGroup.mk K J)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one, ← map_mul, hprod, mk_spanSingleton]
  rw [this]
  exact Subgroup.inv_mem _ hJmem

omit [Fact (0 < n)] in

/--
@isnad1 id=eq.0h5v.s12.bf3618ebc209 from=translated src=- shape=74748c90 vocab=16fc4805
-/
theorem valuationOfNeZeroMod_mk (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) =
      AddEquiv.toMultiplicative (Int.quotientZMultiplesNatEquivZMod n)
        (QuotientGroup.mk (s := AddSubgroup.toSubgroup (AddSubgroup.zmultiples (n : ℤ))) (v.valuationOfNeZero x)) := rfl

end IsDedekindDomain.selmerGroup

end

noncomputable section

namespace IsDedekindDomain.selmerGroup

open IsDedekindDomain FractionalIdeal
open scoped nonZeroDivisors Classical

variable {R : Type} [CommRing R] [IsDedekindDomain R] (K : Type) [Field K] [Algebra R K] [IsFractionRing R K]
  (S : Set (HeightOneSpectrum R)) (n : ℕ) [Fact (0 < n)]

abbrev Qn : Type := Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range

abbrev Sel : Subgroup (Qn K n) := selmerGroup (R := R) (K := K) (S := S) (n := n)

omit [Fact (0 < n)] in
/--
@isnad1 id=issel.0h4v.s6.8a10a3274762 from=translated src=- shape=3f0fa421 vocab=29d87acb
-/
theorem IsSel.one : IsSel K S n 1 := by simpa using IsSel.pow (K := K) (S := S) (n := n) 1

omit [Fact (0 < n)] in
/--
@isnad1 id=issel.1h6v.s7.38fed609ed1f from=translated src=- shape=f7979564 vocab=fb0af766
-/
theorem IsSel.npow {x : Kˣ} (hx : IsSel K S n x) (k : ℕ) : IsSel K S n (x ^ k) := by
  induction k with
  | zero => simpa using IsSel.one K S n
  | succ k ih => rw [pow_succ]; exact ih.mul hx

/--
@isnad1 id=eq.1h6v.s7.18fb9532248a from=translated src=- shape=3b51bc4c vocab=50d46111
-/
theorem radClass_npow {x : Kˣ} (hx : IsSel K S n x) (k : ℕ) : radClass K S n (x ^ k) = radClass K S n x ^ k := by
  induction k with
  | zero =>
    rw [pow_zero, pow_zero]
    have := radClass_pow K S n (1 : Kˣ)
    rwa [one_pow] at this
  | succ k ih => rw [pow_succ, pow_succ, radClass_mul K S n (hx.npow K S n k) hx, ih]

/--
@isnad1 id=eq.3h6v.s8.d7d854318a7f from=translated src=- shape=e3380ccc vocab=2a8cb373
-/
theorem radClass_eq_of_mk_eq {x y : Kˣ} (hx : IsSel K S n x) (_hy : IsSel K S n y) (h : (QuotientGroup.mk x : Qn K n) = QuotientGroup.mk y) :
    radClass K S n x = radClass K S n y := by
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 (QuotientGroup.eq.1 h)
  have : y = x * z ^ n := by rw [← powMonoidHom_apply, hz, mul_inv_cancel_left]
  rw [this, radClass_mul K S n hx (IsSel.pow z), radClass_pow, mul_one]

def rep (x : ↥(Sel K S n)) : Kˣ := Quotient.out (x.1 : Qn K n)

omit [Fact (0 < n)] in
/--
@isnad1 id=eq.0h5v.s9.803cf5ca1ea7 from=translated src=- shape=56a64c85 vocab=9d43a331
-/
theorem mk_rep (x : ↥(Sel K S n)) : (QuotientGroup.mk (rep K S n x) : Qn K n) = x.1 := Quotient.out_eq _

end IsDedekindDomain.selmerGroup

end
