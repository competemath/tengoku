import Tengoku.Seed.RingTheory.DedekindDomain.SelmerGroup
import Tengoku.Seed.RingTheory.ClassGroup
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization
import Tengoku.Seed.GroupTheory.FiniteAbelian.Basic
import Tengoku.Seed.GroupTheory.Torsion
import Tengoku.Seed.GroupTheory.QuotientGroup.Finite

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units

open IsDedekindDomain

universe u v

set_option autoImplicit false

open IsDedekindDomain.HeightOneSpectrum FractionalIdeal
open scoped nonZeroDivisors

namespace WtTF
namespace SelmerFin

variable {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K]
  [Algebra R K] [IsFractionRing R K]

theorem eq_of_count_eq {I J : FractionalIdeal R⁰ K} (hI : I ≠ 0) (hJ : J ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, count K v I = count K v J) : I = J := by
  rw [← finprod_heightOneSpectrum_factorization' K hI,
    ← finprod_heightOneSpectrum_factorization' K hJ]
  exact finprod_congr fun v => by rw [h v]

/--
@isnad1 id=eq.2h5v.s10.1c1cc92cd2fe from=translated src=- shape=4a65d4de vocab=b7e25d27
-/
theorem pow_injective {n : ℕ} (hn : n ≠ 0) {I J : (FractionalIdeal R⁰ K)ˣ}
    (h : I ^ n = J ^ n) : I = J := by
  refine Units.ext (eq_of_count_eq I.ne_zero J.ne_zero fun v => ?_)
  have hc := congrArg (fun U : (FractionalIdeal R⁰ K)ˣ => count K v ↑U) h
  simp only [Units.val_pow_eq_pow_val, count_pow] at hc
  exact mul_left_cancel₀ (Int.natCast_ne_zero.mpr hn) hc

/--
@isnad1 id=ex.2h4v.s8.869e0b76bb59 from=translated src=- shape=c4dd4fa7 vocab=6c2c02c7
-/
theorem exists_pow_eq {n : ℕ} {I : FractionalIdeal R⁰ K} (hI : I ≠ 0)
    (h : ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ count K v I) :
    ∃ J : FractionalIdeal R⁰ K, J ≠ 0 ∧ J ^ n = I := by
  classical
  have hfin : {v : HeightOneSpectrum R | ¬count K v I / (n : ℤ) = 0}.Finite := by
    refine Set.Finite.subset (Filter.eventually_cofinite.mp (finite_factors I)) ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv ⊢
    exact fun h0 => hv (by rw [h0, Int.zero_ediv])
  set exps : HeightOneSpectrum R →₀ ℤ :=
    ⟨hfin.toFinset, fun v => count K v I / (n : ℤ), fun v => by
      rw [Set.Finite.mem_toFinset]; exact Iff.rfl⟩ with hexps
  have hJ0 : (exps.prod fun v e => (v.asIdeal : FractionalIdeal R⁰ K) ^ e) ≠ 0 := by
    rw [Finsupp.prod]
    exact Finset.prod_ne_zero_iff.mpr fun v _ => zpow_ne_zero _ (coeIdeal_ne_zero.mpr v.ne_bot)
  refine ⟨_, hJ0, eq_of_count_eq (pow_ne_zero n hJ0) hI fun v => ?_⟩
  rw [count_pow, count_finsuppProd]
  show (n : ℤ) * (count K v I / (n : ℤ)) = count K v I
  exact Int.mul_ediv_cancel' (h v)

/--
@isnad1 id=eq.0h4v.s7.4afbf4ac20f8 from=translated src=- shape=86ed0936 vocab=5318463d
-/
theorem toAdd_valuationOfNeZero (v : HeightOneSpectrum R) (x : Kˣ) :
    Multiplicative.toAdd (v.valuationOfNeZero x) =
      -count K v (spanSingleton R⁰ (x : K)) := by
  classical
  have hd0 : (algebraMap R K) ((IsLocalization.sec R⁰ (x : K)).2 : R) ≠ 0 := fun h0 =>
    nonZeroDivisors.coe_ne_zero _
      ((map_eq_zero_iff _ (FaithfulSMul.algebraMap_injective R K)).mp h0)
  have hspan : spanSingleton R⁰ (x : K) =
      spanSingleton R⁰ ((algebraMap R K) ((IsLocalization.sec R⁰ (x : K)).2 : R))⁻¹ *
        ↑(Ideal.span {(IsLocalization.sec R⁰ (x : K)).1} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton]
    have hx : ((algebraMap R K) ((IsLocalization.sec R⁰ (x : K)).2 : R))⁻¹ *
        (algebraMap R K) (IsLocalization.sec R⁰ (x : K)).1 = (x : K) := by
      rw [← IsLocalization.sec_spec R⁰ (x : K), mul_comm (x : K), ← mul_assoc,
        inv_mul_cancel₀ hd0, one_mul]
    rw [hx]
  rw [count_well_defined K v (spanSingleton_ne_zero_iff.mpr x.ne_zero) hspan]
  have hval : v.valuationOfNeZero x = v.valuationOfNeZeroToFun x := rfl
  rw [hval]
  unfold HeightOneSpectrum.valuationOfNeZeroToFun
  rw [toAdd_ofAdd]
  ring

/--
@isnad1 id=iff.0h5v.s11.34ada3d08eb8 from=translated src=- shape=ce52bf12 vocab=9609b1b4
-/
theorem valuationOfNeZeroMod_eq_one_iff {n : ℕ} (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuationOfNeZeroMod n (QuotientGroup.mk x) = 1 ↔
      (n : ℤ) ∣ count K v (spanSingleton R⁰ (x : K)) := by
  rw [← dvd_neg, ← toAdd_valuationOfNeZero v x, ← Int.mem_zmultiples_iff,
    ← Multiplicative.mem_toSubgroup, ← QuotientGroup.eq_one_iff]
  unfold HeightOneSpectrum.valuationOfNeZeroMod
  erw [MonoidHom.comp_apply, QuotientGroup.map_mk]
  exact map_eq_one_iff _ (MulEquiv.injective _)

def Dvble (n : ℕ) (x : Kˣ) : Prop :=
  ∀ v : HeightOneSpectrum R, (n : ℤ) ∣ count K v (spanSingleton R⁰ (x : K))

/--
@isnad1 id=dvble.2h5v.s7.6615ee28f4d5 from=translated src=- shape=35ce19d4 vocab=9f91640c
-/
theorem Dvble.mul {n : ℕ} {x y : Kˣ} (hx : Dvble (R := R) n x) (hy : Dvble (R := R) n y) :
    Dvble (R := R) n (x * y) := fun v => by
  have hs : spanSingleton R⁰ ((x * y : Kˣ) : K) =
      spanSingleton R⁰ (x : K) * spanSingleton R⁰ (y : K) := by
    rw [Units.val_mul, spanSingleton_mul_spanSingleton]
  rw [hs, count_mul K v (spanSingleton_ne_zero_iff.mpr x.ne_zero)
    (spanSingleton_ne_zero_iff.mpr y.ne_zero)]
  exact dvd_add (hx v) (hy v)

/--
@isnad1 id=dvble.0h4v.s7.877ae799bfc2 from=translated src=- shape=6ac5fa5b vocab=2ee8ed23
-/
theorem Dvble.pow {n : ℕ} (y : Kˣ) : Dvble (R := R) n (y ^ n) := fun v => by
  have hs : spanSingleton R⁰ ((y ^ n : Kˣ) : K) = spanSingleton R⁰ (y : K) ^ n := by
    rw [Units.val_pow_eq_pow_val, spanSingleton_pow]
  rw [hs, count_pow]
  exact dvd_mul_right _ _

/--
@isnad1 id=dvble.1h5v.s7.2b30175b3f43 from=translated src=- shape=0ac9cb33 vocab=5ff734c9
-/
theorem Dvble.of_mul_pow {n : ℕ} {x y : Kˣ} (h : Dvble (R := R) n (x * y ^ n)) :
    Dvble (R := R) n x := by
  have h2 := h.mul (Dvble.pow (R := R) (n := n) y⁻¹)
  have hxy : x * y ^ n * y⁻¹ ^ n = x := by
    rw [mul_assoc, ← mul_pow, mul_inv_cancel, one_pow, mul_one]
  rwa [hxy] at h2

noncomputable def rootUnit {n : ℕ} (x : Kˣ) (h : Dvble (R := R) n x) :
    (FractionalIdeal R⁰ K)ˣ :=
  Units.mk0 (exists_pow_eq (spanSingleton_ne_zero_iff.mpr x.ne_zero) h).choose
    (exists_pow_eq (spanSingleton_ne_zero_iff.mpr x.ne_zero) h).choose_spec.1

/--
@isnad1 id=eq.1h4v.s10.1b132de578d8 from=translated src=- shape=dcbb2183 vocab=afe66b07
-/
theorem rootUnit_pow {n : ℕ} (x : Kˣ) (h : Dvble (R := R) n x) :
    rootUnit x h ^ n = toPrincipalIdeal R K x := by
  refine Units.ext ?_
  rw [Units.val_pow_eq_pow_val, coe_toPrincipalIdeal]
  show (exists_pow_eq (spanSingleton_ne_zero_iff.mpr x.ne_zero) h).choose ^ n = _
  exact (exists_pow_eq (spanSingleton_ne_zero_iff.mpr x.ne_zero) h).choose_spec.2

/--
@isnad1 id=eq.4h5v.s9.8a62c56aab0c from=translated src=- shape=6d4ecab2 vocab=ce0df847
-/
theorem rootUnit_mul {n : ℕ} (hn : n ≠ 0) (x y : Kˣ) (hx : Dvble (R := R) n x)
    (hy : Dvble (R := R) n y) (hxy : Dvble (R := R) n (x * y)) :
    rootUnit (x * y) hxy = rootUnit x hx * rootUnit y hy := by
  refine pow_injective hn ?_
  rw [mul_pow, rootUnit_pow, rootUnit_pow, rootUnit_pow, ← map_mul]

open Classical in

noncomputable def classOf (n : ℕ) (x : Kˣ) : ClassGroup R :=
  if h : Dvble (R := R) n x then ClassGroup.mk K (rootUnit x h) else 1

/--
@isnad1 id=eq.1h4v.s9.afdb05737ce3 from=translated src=- shape=d328e7d7 vocab=056250a4
-/
theorem classOf_of_dvble {n : ℕ} (x : Kˣ) (h : Dvble (R := R) n x) :
    classOf (R := R) (K := K) n x = ClassGroup.mk K (rootUnit x h) :=
  dite_eq_left h

/--
@isnad1 id=eq.3h5v.s7.c0e9594c8171 from=translated src=- shape=800033e3 vocab=41df77fd
-/
theorem classOf_mul {n : ℕ} (hn : n ≠ 0) {x y : Kˣ} (hx : Dvble (R := R) n x)
    (hy : Dvble (R := R) n y) :
    classOf (R := R) (K := K) n (x * y) = classOf n x * classOf n y := by
  rw [classOf_of_dvble x hx, classOf_of_dvble y hy,
    classOf_of_dvble (x * y) (hx.mul hy), rootUnit_mul hn x y hx hy (hx.mul hy), map_mul]

/--
@isnad1 id=eq.1h4v.s7.639d5d865d5d from=translated src=- shape=7054b660 vocab=0c531272
-/
theorem classOf_pow_eq_one {n : ℕ} (hn : n ≠ 0) (y : Kˣ) :
    classOf (R := R) (K := K) n (y ^ n) = 1 := by
  rw [classOf_of_dvble _ (Dvble.pow y)]
  have hroot : rootUnit (y ^ n) (Dvble.pow y) = toPrincipalIdeal R K y := by
    refine pow_injective hn ?_
    rw [rootUnit_pow, ← map_pow]
  rw [hroot, ClassGroup.mk_eq_one_iff]
  exact ⟨⟨(y : K), by rw [coe_toPrincipalIdeal, coe_spanSingleton]⟩⟩

/--
@isnad1 id=eq.1h5v.s7.a8226038b21c from=translated src=- shape=067f2e17 vocab=ec8a2970
-/
theorem classOf_mul_pow {n : ℕ} (hn : n ≠ 0) (x y : Kˣ) :
    classOf (R := R) (K := K) n (x * y ^ n) = classOf n x := by
  by_cases hx : Dvble (R := R) n x
  · rw [classOf_mul hn hx (Dvble.pow y), classOf_pow_eq_one hn y, mul_one]
  · unfold classOf
    rw [dite_eq_right (fun h => hx h.of_mul_pow), dite_eq_right hx]

noncomputable def classOfMod {n : ℕ} (hn : n ≠ 0) :
    (Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) → ClassGroup R := fun q =>
  Quotient.liftOn' q (classOf n) fun a b hab => by
    rw [QuotientGroup.leftRel_apply] at hab
    obtain ⟨c, hc⟩ := hab
    have hc' : c ^ n = a⁻¹ * b := hc
    have hb : b = a * c ^ n := by rw [hc', mul_inv_cancel_left]
    rw [hb]
    exact (classOf_mul_pow hn a c).symm

/--
@isnad1 id=eq.1h4v.s7.08bb5bde927b from=translated src=- shape=d36d7ce7 vocab=ac75aa7a
-/
theorem classOfMod_mk {n : ℕ} (hn : n ≠ 0) (x : Kˣ) :
    classOfMod (R := R) (K := K) hn (QuotientGroup.mk x) = classOf n x :=
  rfl

/--
@isnad1 id=dvble.1h4v.s10.0a277549c506 from=translated src=- shape=a091df63 vocab=d24e75e7
-/
theorem dvble_of_mem {n : ℕ} {x : Kˣ}
    (hx : (QuotientGroup.mk x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) ∈
      selmerGroup (R := R) (K := K) (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) :
    Dvble (R := R) n x :=
  fun v => (valuationOfNeZeroMod_eq_one_iff v x).mp (hx v (Set.notMem_empty v))

noncomputable def selmerToClass {n : ℕ} (hn : n ≠ 0) :
    selmerGroup (R := R) (K := K) (S := (∅ : Set (HeightOneSpectrum R))) (n := n) →*
      ClassGroup R :=
  MonoidHom.mk' (fun x => classOfMod hn (x : Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range))
    (by
      rintro ⟨q, hq⟩ ⟨r, hr⟩
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective r
      show classOf (R := R) (K := K) n (x * y) = classOf n x * classOf n y
      exact classOf_mul hn (dvble_of_mem hq) (dvble_of_mem hr))

omit [IsDedekindDomain R] in

/--
@isnad1 id=ex.1h4v.s7.9a1e84cb9d6a from=translated src=- shape=a62908be vocab=11445df8
-/
theorem exists_unit_of_spanSingleton_eq {a b : K}
    (h : spanSingleton R⁰ a = spanSingleton R⁰ b) :
    ∃ u : Rˣ, b = algebraMap R K ((u : Rˣ) : R) * a := by
  have hb : b ∈ spanSingleton R⁰ a := by rw [h]; exact mem_spanSingleton_self R⁰ b
  have ha : a ∈ spanSingleton R⁰ b := by rw [← h]; exact mem_spanSingleton_self R⁰ a
  obtain ⟨r, hr⟩ := (mem_spanSingleton R⁰).mp hb
  obtain ⟨s, hs⟩ := (mem_spanSingleton R⁰).mp ha
  by_cases hb0 : b = 0
  · refine ⟨1, ?_⟩
    rw [hb0] at hs ⊢
    rw [smul_zero] at hs
    rw [← hs, mul_zero]
  · have hrsb : algebraMap R K (r * s) * b = b := by
      rw [← Algebra.smul_def, mul_smul, hs, hr]
    have hrs1 : r * s = 1 := by
      refine FaithfulSMul.algebraMap_injective R K ?_
      rw [map_one]
      exact mul_right_cancel₀ hb0 (by rw [hrsb, one_mul])
    refine ⟨⟨r, s, hrs1, by rwa [mul_comm] at hrs1⟩, ?_⟩
    rw [← Algebra.smul_def]
    exact hr.symm

/--
@isnad1 id=le.1h3v.s13.a79c9b1e4cc1 from=translated src=- shape=02a9e9e6 vocab=caf5dd68
-/
theorem selmerToClass_ker_le {n : ℕ} (hn : n ≠ 0) :
    (selmerToClass (R := R) (K := K) hn).ker ≤
      (selmerGroup.fromUnit (R := R) (K := K) (n := n)).range := by
  rintro ⟨q, hq⟩ hker
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
  rw [MonoidHom.mem_ker] at hker
  have hdv : Dvble (R := R) n x := dvble_of_mem hq
  have h1 : classOf (R := R) (K := K) n x = 1 := by
    have happ : selmerToClass (R := R) (K := K) hn ⟨QuotientGroup.mk x, hq⟩ =
        classOf n x := classOfMod_mk hn x
    rw [← happ]
    exact hker
  rw [classOf_of_dvble x hdv, ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨c, hc⟩ := h1.principal
  have hcoe : (rootUnit x hdv : FractionalIdeal R⁰ K) = spanSingleton R⁰ c := by
    apply coeToSubmodule_injective
    show ((rootUnit x hdv : FractionalIdeal R⁰ K) : Submodule R K) =
      ((spanSingleton R⁰ c : FractionalIdeal R⁰ K) : Submodule R K)
    rw [coe_spanSingleton]
    exact hc
  have hc0 : c ≠ 0 := by
    intro h0
    apply Units.ne_zero (rootUnit x hdv)
    rw [hcoe]
    exact spanSingleton_eq_zero_iff.mpr h0
  have hcuP : toPrincipalIdeal R K (Units.mk0 c hc0) = rootUnit x hdv :=
    toPrincipalIdeal_eq_iff.mpr (by rw [hcoe, Units.val_mk0])
  have hxc : spanSingleton R⁰ ((Units.mk0 c hc0 ^ n : Kˣ) : K) = spanSingleton R⁰ (x : K) := by
    have hpow := rootUnit_pow x hdv
    rw [← hcuP, ← map_pow] at hpow
    have hiff := toPrincipalIdeal_eq_iff.mp hpow
    rwa [coe_toPrincipalIdeal] at hiff
  obtain ⟨u, hu⟩ := exists_unit_of_spanSingleton_eq hxc
  rw [MonoidHom.mem_range]
  refine ⟨u, Subtype.ext ?_⟩
  show QuotientGroup.mk (Units.map (algebraMap R K).toMonoidHom u) = QuotientGroup.mk x
  have hxu : x = Units.map (algebraMap R K).toMonoidHom u * Units.mk0 c hc0 ^ n := by
    refine Units.ext ?_
    rw [Units.val_mul, Units.coe_map]
    exact hu
  have hmk1 : (QuotientGroup.mk (Units.mk0 c hc0 ^ n) :
      Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr (MonoidHom.mem_range.mpr ⟨Units.mk0 c hc0, rfl⟩)
  rw [hxu, QuotientGroup.mk_mul, hmk1]
  exact (mul_one (QuotientGroup.mk (Units.map (algebraMap R K).toMonoidHom u) :
    Kˣ ⧸ (powMonoidHom n : Kˣ →* Kˣ).range)).symm

/--
@isnad1 id=finite.1h3v.s6.e0e7f3d605f1 from=translated src=- shape=f6381f7f vocab=a18b7418
-/
theorem finite_of_finite_ker_codom {G H : Type*} [Group G] [Group H] (f : G →* H)
    [Finite H] (hker : Finite f.ker) : Finite G := by
  haveI := hker
  haveI : Finite (G ⧸ f.ker) :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange f).symm.toEquiv
  exact Finite.of_subgroup_quotient f.ker

omit [IsDedekindDomain R] in

/--
@isnad1 id=finite.1h2v.s7.9c673695c8d6 from=translated src=- shape=a3295fe4 vocab=8c220d23
-/
theorem finite_unitsModPow (n : ℕ) (hn : n ≠ 0) [Monoid.FG Rˣ] :
    Finite (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range) := by
  haveI : Group.FG Rˣ := Group.fg_iff_monoid_fg.mpr ‹_›
  haveI : Group.FG (Rˣ ⧸ (powMonoidHom n : Rˣ →* Rˣ).range) :=
    Group.fg_of_surjective (QuotientGroup.mk'_surjective _)
  exact CommGroup.finite_of_fg_isMulTorsion _
    (CommGroup.isMulTorsion_quotient_range_powMonoidHom Rˣ hn)

/--
@isnad1 id=finite.1h3v.s10.a7dadf08cf13 from=translated src=- shape=6246c9b8 vocab=1f67e19a
-/
theorem finite_selmerEmpty (n : ℕ) (hn : n ≠ 0) [Finite (ClassGroup R)] [Monoid.FG Rˣ] :
    Finite (selmerGroup (R := R) (K := K) (S := (∅ : Set (HeightOneSpectrum R))) (n := n)) := by
  refine finite_of_finite_ker_codom (selmerToClass (R := R) (K := K) hn) ?_
  haveI : Fact (0 < n) := ⟨Nat.pos_of_ne_zero hn⟩
  haveI h1 : Finite (Rˣ ⧸ (selmerGroup.fromUnit (R := R) (K := K) (n := n)).ker) := by
    rw [selmerGroup.fromUnit_ker]
    exact finite_unitsModPow n hn
  haveI hfr : Finite (selmerGroup.fromUnit (R := R) (K := K) (n := n)).range :=
    Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange _).toEquiv
  exact Finite.of_injective _ (Subgroup.inclusion_injective (selmerToClass_ker_le hn))

end WtTF.SelmerFin

/--
@isnad1 id=finite.0h4v.s10.b36360d3229b from=translated src=- shape=8605e03d vocab=ad8faa5e
-/
theorem solution
    {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K] {S : Set (HeightOneSpectrum R)} {n : ℕ} [hn : Fact (0 < n)]
    [Finite (ClassGroup R)] [Monoid.FG Rˣ] [Finite S] :
    Finite (selmerGroup (R := R) (K := K) (S := S) (n := n)) := by
  haveI : NeZero n := ⟨hn.out.ne'⟩
  haveI h0 := WtTF.SelmerFin.finite_selmerEmpty (R := R) (K := K) n hn.out.ne'
  refine WtTF.SelmerFin.finite_of_finite_ker_codom
    (selmerGroup.valuation (R := R) (K := K) (S := S) (n := n)) ?_
  rw [selmerGroup.valuation_ker_eq]
  exact Finite.of_equiv _
    (Subgroup.subgroupOfEquivOfLe (selmerGroup.monotone (Set.empty_subset S))).symm.toEquiv
