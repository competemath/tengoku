import Tengoku.Seed.RingTheory.DedekindDomain.SInteger
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization
import Tengoku.Seed.NumberTheory.NumberField.Units.DirichletTheorem
import Tengoku.Seed.NumberTheory.NumberField.ClassNumber

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms solution` (it only prints; the queue checks the axioms of every declaration). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_M4aHerbrand_finrank_sUnit_eq_univ.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 4 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_M4aHerbrand_finrank_sUnit_eq_univ

set_option autoImplicit false

open IsDedekindDomain NumberField

namespace M4aHerbrandSolH2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal WithZero

open scoped nonZeroDivisors

noncomputable section

variable {R : Type*} [CommRing R] [IsDedekindDomain R]
  {K : Type*} [Field K] [Algebra R K] [IsFractionRing R K]

omit [IsDedekindDomain R] in
/--
@isnad1 id=ne.0h3v.s7.80d8e2c2f3b7 from=translated src=- shape=46839215 vocab=4d952a5e
-/
theorem spanSingleton_units_ne_zero (x : Kˣ) : spanSingleton R⁰ (x : K) ≠ 0 :=
  spanSingleton_ne_zero_iff.mpr x.ne_zero

/--
@isnad1 id=eq.0h5v.s7.e911fd4b700a from=translated src=- shape=7ae6ba6a vocab=19408192
-/
theorem count_spanSingleton_units_mul (v : HeightOneSpectrum R) (x y : Kˣ) :
    count K v (spanSingleton R⁰ ((x * y : Kˣ) : K)) =
      count K v (spanSingleton R⁰ (x : K)) + count K v (spanSingleton R⁰ (y : K)) := by
  rw [Units.val_mul, ← spanSingleton_mul_spanSingleton]
  exact count_mul K v (spanSingleton_units_ne_zero x) (spanSingleton_units_ne_zero y)

/--
@isnad1 id=eq.1h5v.s9.b46ae4a438f0 from=translated src=- shape=8243dca3 vocab=c39b4aeb
-/
theorem count_spanSingleton_mk' (v : HeightOneSpectrum R) {r : R} (hr : r ≠ 0) (s : R⁰) :
    count K v (spanSingleton R⁰ (IsLocalization.mk' K r s)) =
      ((Associates.mk v.asIdeal).count (Associates.mk (Ideal.span {r} : Ideal R)).factors : ℤ)
        - ((Associates.mk v.asIdeal).count
            (Associates.mk (Ideal.span {(s : R)} : Ideal R)).factors : ℤ) := by
  have hmk : IsLocalization.mk' K r s ≠ 0 := by
    rw [IsFractionRing.mk'_eq_div]
    exact div_ne_zero (by rwa [Ne, IsFractionRing.to_map_eq_zero_iff])
      (by rw [Ne, IsFractionRing.to_map_eq_zero_iff]; exact nonZeroDivisors.coe_ne_zero s)
  have hrep : spanSingleton R⁰ (IsLocalization.mk' K r s) =
      spanSingleton R⁰ ((algebraMap R K) (s : R))⁻¹ * ↑(Ideal.span {r} : Ideal R) := by
    rw [coeIdeal_span_singleton, spanSingleton_mul_spanSingleton, inv_mul_eq_div,
      ← IsFractionRing.mk'_eq_div]
  exact count_well_defined K v (spanSingleton_ne_zero_iff.mpr hmk) hrep

/--
@isnad1 id=iff.0h4v.s7.86f3433281df from=translated src=- shape=ac69a918 vocab=0786c86c
-/
theorem valuation_eq_one_iff_count_eq_zero (v : HeightOneSpectrum R) (x : Kˣ) :
    v.valuation K (x : K) = 1 ↔ count K v (spanSingleton R⁰ (x : K)) = 0 := by
  obtain ⟨⟨r, s⟩, hx⟩ := IsLocalization.mk'_surjective (M := R⁰) (S := K) (x : K)
  change IsLocalization.mk' K r s = (x : K) at hx
  have hr : r ≠ 0 := by
    rintro rfl
    rw [IsLocalization.mk'_zero] at hx
    exact x.ne_zero hx.symm
  rw [← hx, valuation_of_mk', count_spanSingleton_mk' v hr s,
    intValuation_if_neg v hr, intValuation_if_neg v (nonZeroDivisors.coe_ne_zero s),
    ← exp_sub, show (1 : ℤᵐ⁰) = exp 0 by rw [exp_zero], exp_inj]
  omega

/--
@isnad1 id=iff.0h4v.s7.4c270a156a1a from=translated src=- shape=8036f8bd vocab=d91d8229
-/
theorem mem_unit_iff_count {T : Set (HeightOneSpectrum R)} {x : Kˣ} :
    x ∈ T.unit K ↔ ∀ v ∉ T, count K v (spanSingleton R⁰ (x : K)) = 0 := by
  have hmem : x ∈ T.unit K ↔
      ∀ v : HeightOneSpectrum R, v ∉ T → v.valuation K (x : K) = 1 := Iff.rfl
  rw [hmem]
  exact forall_congr' fun v => forall_congr' fun _ => valuation_eq_one_iff_count_eq_zero v x

def sUnitCountHom (T : Set (HeightOneSpectrum R)) :
    Additive ↥(T.unit K) →+ (↥T → ℤ) where
  toFun x v := count K (v : HeightOneSpectrum R)
    (spanSingleton R⁰ (((x.toMul : ↥(T.unit K)) : Kˣ) : K))
  map_zero' := by
    funext v
    show count K (v : HeightOneSpectrum R) (spanSingleton R⁰ ((1 : Kˣ) : K)) = 0
    rw [Units.val_one, spanSingleton_one, count_one]
  map_add' x y := by
    funext v
    show count K (v : HeightOneSpectrum R)
        (spanSingleton R⁰ (((x.toMul * y.toMul : ↥(T.unit K)) : Kˣ) : K)) = _
    have hco : ((x.toMul * y.toMul : ↥(T.unit K)) : Kˣ)
        = ((x.toMul : ↥(T.unit K)) : Kˣ) * ((y.toMul : ↥(T.unit K)) : Kˣ) := rfl
    rw [hco, count_spanSingleton_units_mul]
    rfl

/--
@isnad1 id=eq.0h5v.s11.3ca45bbc463b from=translated src=- shape=b5ef92b0 vocab=a7e40e70
-/
@[scoped simp] theorem sUnitCountHom_apply (T : Set (HeightOneSpectrum R))
    (x : ↥(T.unit K)) (v : ↥T) :
    sUnitCountHom T (Additive.ofMul x) v
      = count K (v : HeightOneSpectrum R) (spanSingleton R⁰ ((x : Kˣ) : K)) :=
  rfl

/--
@isnad1 id=eq.0h5v.s11.7e4c74198aee from=translated src=- shape=c6c71cb0 vocab=1af39b54
-/
theorem sUnitCountHom_apply' (T : Set (HeightOneSpectrum R))
    (x : Additive ↥(T.unit K)) (v : ↥T) :
    sUnitCountHom T x v
      = count K (v : HeightOneSpectrum R)
          (spanSingleton R⁰ (((x.toMul : ↥(T.unit K)) : Kˣ) : K)) :=
  rfl

/--
@isnad1 id=eq.0h4v.s7.17308d20f4bb from=translated src=- shape=bf6b3194 vocab=38ebb326
-/
theorem valuation_algebraMap_units_eq_one (v : HeightOneSpectrum R) (u : Rˣ) :
    v.valuation K (algebraMap R K (u : R)) = 1 := by
  have h1 : v.valuation K (algebraMap R K (u : R)) ≤ 1 := by
    rw [valuation_of_algebraMap]; exact v.intValuation_le_one _
  have h2 : v.valuation K (algebraMap R K ((u⁻¹ : Rˣ) : R)) ≤ 1 := by
    rw [valuation_of_algebraMap]; exact v.intValuation_le_one _
  have h3 : v.valuation K (algebraMap R K (u : R))
      * v.valuation K (algebraMap R K ((u⁻¹ : Rˣ) : R)) = 1 := by
    rw [← map_mul (v.valuation K), ← map_mul (algebraMap R K), Units.mul_inv, map_one, map_one]
  exact eq_one_of_one_le_mul_left h1 h2 h3.ge

def ringUnitsUnitHom (T : Set (HeightOneSpectrum R)) : Rˣ →* ↥(T.unit K) where
  toFun u := ⟨Units.map (algebraMap R K : R →* K) u, fun v _ => by
    show v.valuation K ((Units.map (algebraMap R K : R →* K) u : Kˣ) : K) = 1
    exact valuation_algebraMap_units_eq_one v u⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' a b := Subtype.ext (map_mul _ a b)

/--
@isnad1 id=injectiv.0h3v.s10.5428faa5c40d from=translated src=- shape=a64506e9 vocab=ea290a95
-/
theorem ringUnitsUnitHom_injective (T : Set (HeightOneSpectrum R)) :
    Function.Injective (ringUnitsUnitHom (K := K) (R := R) T) := fun _ _ h =>
  Units.map_injective (f := (algebraMap R K : R →* K))
    (IsFractionRing.injective R K) (Subtype.ext_iff.mp h)

/--
@isnad1 id=ex.1h3v.s8.cdf8053cf648 from=translated src=- shape=8bd5547d vocab=495e377f
-/
theorem exists_ringUnits_eq_of_forall_valuation_eq_one {x : Kˣ}
    (h : ∀ v : HeightOneSpectrum R, v.valuation K (x : K) = 1) :
    ∃ u : Rˣ, Units.map (algebraMap R K : R →* K) u = x := by
  obtain ⟨r, hr⟩ := mem_integers_of_valuation_le_one (R := R) K (x : K) fun v => (h v).le
  obtain ⟨s, hs⟩ := mem_integers_of_valuation_le_one (R := R) K ((x⁻¹ : Kˣ) : K) fun v =>
    le_of_eq (by rw [Units.val_inv_eq_inv_val, map_inv₀, h v, inv_one])
  have hrs : r * s = 1 := by
    apply IsFractionRing.injective R K
    rw [map_mul, map_one, hr, hs, Units.val_inv_eq_inv_val, mul_inv_cancel₀ x.ne_zero]
  exact ⟨⟨r, s, hrs, by rwa [mul_comm] at hrs⟩, Units.ext hr⟩

noncomputable def ringUnitsAddEquivCountHomKer (T : Set (HeightOneSpectrum R)) :
    Additive Rˣ ≃+ ↥(sUnitCountHom (K := K) (R := R) T).ker := by
  refine AddEquiv.ofBijective
    (AddMonoidHom.codRestrict
      (MonoidHom.toAdditive (ringUnitsUnitHom (K := K) T)) _ ?_)
    ⟨?_, ?_⟩
  ·
    intro u
    show sUnitCountHom T (Additive.ofMul (ringUnitsUnitHom (K := K) T u.toMul)) = 0
    funext v
    rw [sUnitCountHom_apply, Pi.zero_apply]
    refine (valuation_eq_one_iff_count_eq_zero (v : HeightOneSpectrum R) _).mp ?_
    show (v : HeightOneSpectrum R).valuation K
        ((Units.map (algebraMap R K : R →* K) u.toMul : Kˣ) : K) = 1
    exact valuation_algebraMap_units_eq_one _ _
  ·
    intro a b h
    have h' := Subtype.ext_iff.mp h
    exact Additive.toMul.injective
      (ringUnitsUnitHom_injective (K := K) T (Additive.toMul.injective h'))
  ·
    rintro ⟨x, hx⟩
    set xm : ↥(T.unit K) := x.toMul with hxm
    have hall : ∀ v : HeightOneSpectrum R,
        count K v (spanSingleton R⁰ ((xm : Kˣ) : K)) = 0 := by
      intro v
      by_cases hvT : v ∈ T
      · have := congrFun hx ⟨v, hvT⟩
        rwa [sUnitCountHom_apply', Pi.zero_apply] at this
      · exact mem_unit_iff_count.mp xm.2 v hvT
    have hval : ∀ v : HeightOneSpectrum R, v.valuation K ((xm : Kˣ) : K) = 1 := fun v =>
      (valuation_eq_one_iff_count_eq_zero v _).mpr (hall v)
    obtain ⟨u, hu⟩ := exists_ringUnits_eq_of_forall_valuation_eq_one hval
    refine ⟨Additive.ofMul u, Subtype.ext ?_⟩
    show Additive.ofMul (ringUnitsUnitHom (K := K) T u) = x
    apply Additive.toMul.injective
    exact Subtype.ext hu

/--
@isnad1 id=finite.1h3v.s9.e0c618b6f8c1 from=translated src=- shape=262802cd vocab=ea64b58e
-/
theorem moduleFinite_additive_unit (T : Set (HeightOneSpectrum R)) [Finite T]
    (hRu : Module.Finite ℤ (Additive Rˣ)) :
    Module.Finite ℤ (Additive ↥(T.unit K)) := by
  rw [Module.finite_def]
  refine Submodule.fg_of_fg_map_of_fg_inf_ker
    (sUnitCountHom (K := K) (R := R) T).toIntLinearMap ?_ ?_
  · haveI : Fintype ↥T := Fintype.ofFinite ↥T
    have : Module.Finite ℤ (↥T → ℤ) := inferInstance
    exact IsNoetherian.noetherian _
  · rw [top_inf_eq, ← Module.Finite.iff_fg]
    exact Module.Finite.equiv
      (ringUnitsAddEquivCountHomKer (K := K) (R := R) T).toIntLinearEquiv

end

end M4aHerbrandSolH2
open scoped _root_.P2MW.S_M4aHerbrand_finrank_sUnit_eq_univ.M4aHerbrandSolH2

section NumberFieldInstance

open NumberField

noncomputable scoped instance (K : Type*) [Field K] [NumberField K]
    (T : Set (IsDedekindDomain.HeightOneSpectrum (RingOfIntegers K))) [Finite T] :
    Module.Finite ℤ (Additive ↥(T.unit K)) :=
  M4aHerbrandSolH2.moduleFinite_additive_unit T inferInstance

end NumberFieldInstance
open scoped _root_.P2MW.S_M4aHerbrand_finrank_sUnit_eq_univ.M4aHerbrandSolH2

namespace M4aHerbrandSolH2

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum FractionalIdeal NumberField Module

open scoped nonZeroDivisors

noncomputable section

/--
@isnad1 id=eq.0h1v.s4.023de4ce2fe9 from=translated src=- shape=49fcc145 vocab=0b80a6ab
-/
theorem finrank_eq_zero_of_finite (G : Type*) [AddCommGroup G] [Finite G] :
    finrank ℤ G = 0 := by
  apply finrank_eq_zero_of_rank_eq_zero
  rw [rank_eq_zero_iff]
  exact fun x => ⟨Nat.card G, Nat.cast_ne_zero.mpr Nat.card_pos.ne',
    by simp [card_nsmul_eq_zero']⟩

variable (K : Type*) [Field K] [NumberField K]

/--
@isnad1 id=eq.0h1v.s7.108e977a17df from=translated src=- shape=fbbc9c0d vocab=486acaf5
-/
theorem finrank_additive_ringOfIntegers_units :
    finrank ℤ (Additive (RingOfIntegers K)ˣ) = NumberField.Units.rank K := by
  set N : Submodule ℤ (Additive (RingOfIntegers K)ˣ) :=
    AddSubgroup.toIntSubmodule (Subgroup.toAddSubgroup (NumberField.Units.torsion K)) with hN
  have hsplit := Submodule.finrank_quotient_add_finrank N
  have hN0 : finrank ℤ (↥N) = 0 := by
    have : Finite (↥N) := (inferInstance : Finite (NumberField.Units.torsion K))
    exact finrank_eq_zero_of_finite _
  have hquot : finrank ℤ (Additive (RingOfIntegers K)ˣ ⧸ N) = NumberField.Units.rank K := by
    have := NumberField.Units.finrank_modTorsion K
    convert this using 2
    rfl
    rfl
    rfl
  rw [← hsplit, hN0, add_zero]
  exact hquot

/--
@isnad1 id=le.0h2v.s9.6028cfada8f2 from=translated src=- shape=9d8dff4c vocab=b38c4e58
-/
theorem finrank_unit_le (T : Set (HeightOneSpectrum (RingOfIntegers K))) [Finite T] :
    finrank ℤ (Additive ↥(T.unit K)) ≤ Nat.card T + NumberField.Units.rank K := by
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  set f := (sUnitCountHom (R := RingOfIntegers K) (K := K) T).toIntLinearMap with hf
  have hsplit := Submodule.finrank_quotient_add_finrank (R := ℤ) (LinearMap.ker f)
  have hquot : finrank ℤ (Additive ↥(T.unit K) ⧸ LinearMap.ker f) ≤ Nat.card T := by
    calc finrank ℤ (Additive ↥(T.unit K) ⧸ LinearMap.ker f)
        = finrank ℤ ↥(LinearMap.range f) := LinearEquiv.finrank_eq f.quotKerEquivRange
      _ ≤ finrank ℤ (↥T → ℤ) := Submodule.finrank_le _
      _ = Nat.card T := by rw [Module.finrank_pi, Nat.card_eq_fintype_card]
  have hker : finrank ℤ ↥(LinearMap.ker f) = NumberField.Units.rank K := by
    have e : Additive (RingOfIntegers K)ˣ ≃+ ↥(LinearMap.ker f) :=
      ringUnitsAddEquivCountHomKer T
    rw [← LinearEquiv.finrank_eq e.toIntLinearEquiv]
    exact finrank_additive_ringOfIntegers_units K
  rw [← hsplit, hker]
  exact Nat.add_le_add_right hquot _

/--
@isnad1 id=isprinci.0h2v.s7.caf047dc7af9 from=translated src=- shape=3c446786 vocab=433d10c8
-/
theorem isPrincipal_asIdeal_pow_classNumber (v : HeightOneSpectrum (RingOfIntegers K)) :
    (v.asIdeal ^ classNumber K : Ideal (RingOfIntegers K)).IsPrincipal := by
  have hv : v.asIdeal ∈ (Ideal (RingOfIntegers K))⁰ :=
    mem_nonZeroDivisors_of_ne_zero (by simpa using v.ne_bot)
  have hpow : v.asIdeal ^ classNumber K ∈ (Ideal (RingOfIntegers K))⁰ := pow_mem hv _
  have h1 : ClassGroup.mk0 (⟨v.asIdeal ^ classNumber K, hpow⟩ : (Ideal (RingOfIntegers K))⁰)
      = 1 := by
    have hrw : (⟨v.asIdeal ^ classNumber K, hpow⟩ : (Ideal (RingOfIntegers K))⁰)
        = (⟨v.asIdeal, hv⟩ : (Ideal (RingOfIntegers K))⁰) ^ classNumber K := rfl
    rw [hrw, map_pow]
    exact pow_card_eq_one
  exact (ClassGroup.mk0_eq_one_iff hpow).mp h1

open scoped Classical in
/--
@isnad1 id=ex.0h3v.s11.0c6b1c3de4d6 from=translated src=- shape=c7918782 vocab=682ccad3
-/
theorem exists_sUnitCountHom_eq_classNumber_smul_single
    (T : Set (HeightOneSpectrum (RingOfIntegers K))) (v : ↥T) :
    ∃ x : Additive ↥(T.unit K),
      sUnitCountHom (R := RingOfIntegers K) (K := K) T x
        = (classNumber K : ℤ) • Pi.single v 1 := by
  classical
  obtain ⟨g, hg⟩ :=
    (isPrincipal_asIdeal_pow_classNumber K (v : HeightOneSpectrum (RingOfIntegers K))).principal
  have hg0 : g ≠ 0 := by
    rintro rfl
    have hpow0 : (v : HeightOneSpectrum (RingOfIntegers K)).asIdeal ^ classNumber K ≠ 0 :=
      pow_ne_zero _ (by simpa using (v : HeightOneSpectrum (RingOfIntegers K)).ne_bot)
    rw [hg] at hpow0
    simp at hpow0
  have hK0 : algebraMap (RingOfIntegers K) K g ≠ 0 := by
    rwa [Ne, IsFractionRing.to_map_eq_zero_iff]
  set xu : Kˣ := Units.mk0 _ hK0 with hxu
  have hspan : spanSingleton (RingOfIntegers K)⁰ ((xu : Kˣ) : K)
      = ((v : HeightOneSpectrum (RingOfIntegers K)).asIdeal
          : FractionalIdeal (RingOfIntegers K)⁰ K) ^ classNumber K := by
    show spanSingleton (RingOfIntegers K)⁰ (algebraMap (RingOfIntegers K) K g) = _
    rw [← coeIdeal_span_singleton, show Ideal.span {g}
        = (v : HeightOneSpectrum (RingOfIntegers K)).asIdeal ^ classNumber K from hg.symm,
      coeIdeal_pow]
  have hprofile : ∀ w : HeightOneSpectrum (RingOfIntegers K),
      count K w (spanSingleton (RingOfIntegers K)⁰ ((xu : Kˣ) : K))
        = if w = (v : HeightOneSpectrum (RingOfIntegers K)) then (classNumber K : ℤ) else 0 := by
    intro w
    rw [hspan]
    by_cases hwv : w = (v : HeightOneSpectrum (RingOfIntegers K))
    · subst hwv
      rw [ite_eq_left rfl, count_pow_self]
    · rw [ite_eq_right hwv, count_pow, count_maximal_coprime K w (Ne.symm hwv), mul_zero]
  have hmem : xu ∈ T.unit K := by
    refine mem_unit_iff_count.mpr fun w hw => ?_
    rw [hprofile w, ite_eq_right]
    rintro rfl
    exact hw v.2
  refine ⟨Additive.ofMul (⟨xu, hmem⟩ : ↥(T.unit K)), ?_⟩
  funext w
  rw [sUnitCountHom_apply, hprofile (w : HeightOneSpectrum (RingOfIntegers K))]
  by_cases hwv : w = v
  · subst hwv
    rw [ite_eq_left rfl]
    simp
  · rw [ite_eq_right (fun h => hwv (Subtype.ext h))]
    have : Pi.single (M := fun _ : ↥T => ℤ) v 1 w = 0 := by
      rw [Pi.single_apply, ite_eq_right hwv]
    simp [this]

open scoped Classical in
/--
@isnad1 id=mem.0h3v.s10.f51293841e2f from=translated src=- shape=bb166ce9 vocab=3e06cbbb
-/
theorem classNumber_smul_mem_range_sUnitCountHom
    (T : Set (HeightOneSpectrum (RingOfIntegers K))) [Finite T] (y : ↥T → ℤ) :
    (classNumber K : ℤ) • y ∈ LinearMap.range
      (sUnitCountHom (R := RingOfIntegers K) (K := K) T).toIntLinearMap := by
  classical
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  have hsum : (classNumber K : ℤ) • y
      = ∑ v : ↥T, y v • ((classNumber K : ℤ) • Pi.single v 1) := by
    funext w
    simp only [Pi.smul_apply, smul_eq_mul, Finset.sum_apply, Pi.single_apply, mul_ite,
      mul_one, mul_zero]
    rw [Finset.sum_ite_eq]
    simp [Finset.mem_univ, mul_comm]
  rw [hsum]
  refine Submodule.sum_mem _ fun v _ => Submodule.smul_mem _ _ ?_
  obtain ⟨x, hx⟩ := exists_sUnitCountHom_eq_classNumber_smul_single K T v
  exact ⟨x, hx⟩

/--
@isnad1 id=eq.0h2v.s9.3f303865699c from=translated src=- shape=9d8dff4c vocab=0a813abf
-/
theorem finrank_unit_eq (T : Set (HeightOneSpectrum (RingOfIntegers K))) [Finite T] :
    finrank ℤ (Additive ↥(T.unit K)) = Nat.card T + NumberField.Units.rank K := by
  haveI : Fintype ↥T := Fintype.ofFinite ↥T
  refine le_antisymm (finrank_unit_le K T) ?_
  set f := (sUnitCountHom (R := RingOfIntegers K) (K := K) T).toIntLinearMap with hf
  have hker : finrank ℤ ↥(LinearMap.ker f) = NumberField.Units.rank K := by
    have e : Additive (RingOfIntegers K)ˣ ≃+ ↥(LinearMap.ker f) :=
      ringUnitsAddEquivCountHomKer T
    rw [← LinearEquiv.finrank_eq e.toIntLinearEquiv]
    exact finrank_additive_ringOfIntegers_units K
  have hrange_ge : Nat.card T ≤ finrank ℤ ↥(LinearMap.range f) := by
    let g : (↥T → ℤ) →ₗ[ℤ] ↥(LinearMap.range f) :=
      LinearMap.codRestrict (LinearMap.range f) ((classNumber K : ℤ) • LinearMap.id)
        fun y => classNumber_smul_mem_range_sUnitCountHom K T y
    have hg_inj : Function.Injective g := fun a b hab => by
      have h := congrArg Subtype.val hab
      simp only [g, LinearMap.codRestrict_apply, LinearMap.smul_apply, LinearMap.id_apply] at h
      ext w
      have hw : a w = b w ∨ (classNumber K : ℤ) = 0 := by
        have h' := congrFun h w
        simp only [Pi.smul_apply, smul_eq_mul] at h'
        rcases mul_eq_mul_left_iff.mp h' with h'' | h''
        · exact Or.inl h''
        · exact Or.inr h''
      refine hw.resolve_right ?_
      exact_mod_cast (classNumber_pos K).ne'
    haveI : Module.Finite ℤ ↥(LinearMap.range f) := by
      rw [Module.Finite.iff_fg]; exact IsNoetherian.noetherian _
    calc Nat.card T = finrank ℤ (↥T → ℤ) := by
          rw [Module.finrank_pi, Nat.card_eq_fintype_card]
      _ ≤ finrank ℤ ↥(LinearMap.range f) := LinearMap.finrank_le_finrank_of_injective hg_inj
  have hsplit := Submodule.finrank_quotient_add_finrank (R := ℤ) (LinearMap.ker f)
  rw [← hsplit, hker]
  refine Nat.add_le_add_right ?_ _
  exact le_of_le_of_eq hrange_ge (LinearEquiv.finrank_eq f.quotKerEquivRange).symm

end
open scoped _root_.P2MW.S_M4aHerbrand_finrank_sUnit_eq_univ.M4aHerbrandSolH2

end M4aHerbrandSolH2
open scoped _root_.P2MW.S_M4aHerbrand_finrank_sUnit_eq_univ.M4aHerbrandSolH2

/--
@isnad1 id=and.0h2v.s10.48c6e0832b8a from=translated src=- shape=aff95c81 vocab=9c4bf9b0
-/
theorem solution (K : Type*) [Field K] [NumberField K]
    (S : Set (HeightOneSpectrum (𝓞 K))) [Finite S] :
    Module.Finite ℤ (Additive (S.unit K)) ∧
    Module.finrank ℤ (Additive (S.unit K)) = Nat.card S + NumberField.Units.rank K :=
  ⟨inferInstance, M4aHerbrandSolH2.finrank_unit_eq (K := K) S⟩

