import Tengoku.Seed.RingTheory.DedekindDomain.IntegralClosure
import Tengoku.Seed.RingTheory.DedekindDomain.AdicValuation
import Tengoku.Seed.RingTheory.Localization.Integral
import Tengoku.Seed.RingTheory.Valuation.Integral
import Tengoku.Seed.RingTheory.Polynomial.ScaleRoots
import Tengoku.Seed.Algebra.Polynomial.Lifts
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Algebra
import Tengoku.Seed.RingTheory.Adjoin.Polynomial.Basic
import Tengoku.Seed.RingTheory.Algebraic.Basic
import Tengoku.Seed.FieldTheory.Perfect
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open Polynomial IsDedekindDomain IntermediateField

universe u

namespace AlgebraicCurve

namespace CurveModel

variable (K : Type u) [Field K] {L : Type u} [Field L] [Algebra K L]

def aevalAdjoin (s : L) : K[X] →ₐ[K] Algebra.adjoin K ({s} : Set L) :=
  (aeval (R := K) s).codRestrict (Algebra.adjoin K ({s} : Set L))
    (fun p => by simp [Algebra.adjoin_singleton_eq_range_aeval])

/--
@isnad1 id=surjecti.0h3v.s9.fcc536ec57ed from=translated src=- shape=e3d8589c vocab=ba46d28b
-/
theorem aevalAdjoin_surjective (s : L) : Function.Surjective (aevalAdjoin K s) := by
  rintro ⟨x, hx⟩
  rw [Algebra.adjoin_singleton_eq_range_aeval] at hx
  obtain ⟨p, rfl⟩ := hx
  exact ⟨p, rfl⟩

/--
@isnad1 id=isprinci.0h3v.s7.4b94ac723650 from=translated src=- shape=7df9212d vocab=38afe108
-/
scoped instance isPrincipalIdealRing_adjoin_singleton (s : L) :
    IsPrincipalIdealRing (Algebra.adjoin K ({s} : Set L)) :=
  IsPrincipalIdealRing.of_surjective (aevalAdjoin K s).toRingHom (aevalAdjoin_surjective K s)

/--
@isnad1 id=isdedeki.0h3v.s6.a35b69be433a from=translated src=- shape=7df9212d vocab=dc968f6d
-/
scoped instance isDedekindDomain_adjoin_singleton (s : L) :
    IsDedekindDomain (Algebra.adjoin K ({s} : Set L)) :=
  inferInstance

def chartRing (S : Set L) : Subalgebra K L where
  carrier := {x | IsIntegral (Algebra.adjoin K S) x}
  mul_mem' ha hb := ha.mul hb
  one_mem' := isIntegral_one
  add_mem' ha hb := ha.add hb
  zero_mem' := isIntegral_zero
  algebraMap_mem' a := by
    have : IsIntegral (Algebra.adjoin K S)
        (algebraMap (Algebra.adjoin K S) L (algebraMap K (Algebra.adjoin K S) a)) :=
      isIntegral_algebraMap
    simpa [← IsScalarTower.algebraMap_apply] using this

/--
@isnad1 id=iff.0h4v.s7.d4789505e523 from=translated src=- shape=2a1f6577 vocab=8dea8568
-/
theorem mem_chartRing_iff {S : Set L} {x : L} :
    x ∈ chartRing K S ↔ IsIntegral (Algebra.adjoin K S) x := Iff.rfl

/--
@isnad1 id=le.0h3v.s6.e503a355c1eb from=translated src=- shape=6af35b01 vocab=61e41784
-/
theorem adjoin_le_chartRing (S : Set L) : Algebra.adjoin K S ≤ chartRing K S := by
  intro x hx
  rw [mem_chartRing_iff]
  have : IsIntegral (Algebra.adjoin K S) (algebraMap (Algebra.adjoin K S) L ⟨x, hx⟩) :=
    isIntegral_algebraMap
  exact this

/--
@isnad1 id=le.0h3v.s6.221c75f027d8 from=translated src=- shape=ab7c81c0 vocab=50c63a8d
-/
theorem subset_chartRing (S : Set L) : S ⊆ (chartRing K S : Set L) := fun _ hx =>
  adjoin_le_chartRing K S (Algebra.subset_adjoin hx)

/--
@isnad1 id=le.1h4v.s6.5fcfc789f08f from=translated src=- shape=413dfcd2 vocab=1221c17d
-/
theorem chartRing_mono {S S' : Set L} (h : S ⊆ S') : chartRing K S ≤ chartRing K S' := by
  intro x hx
  rw [mem_chartRing_iff] at hx ⊢
  have := hx.map_of_comp_eq (Subalgebra.inclusion (Algebra.adjoin_mono h)).toRingHom
    (RingHom.id L) (by ext a; rfl)
  simpa using this

abbrev chartIncl {S S' : Set L} (h : S ⊆ S') : chartRing K S →ₐ[K] chartRing K S' :=
  Subalgebra.inclusion (chartRing_mono K h)

/--
@isnad1 id=eq.1h5v.s9.faa6b3ca8ef6 from=translated src=- shape=b1660e97 vocab=522ac8b9
-/
theorem coe_chartIncl {S S' : Set L} (h : S ⊆ S') (x : chartRing K S) :
    (chartIncl K h x : L) = x :=

  Subalgebra.coe_inclusion _ x

/--
@isnad1 id=injectiv.1h4v.s9.38b732cdfac7 from=translated src=- shape=492782de vocab=9b6c3074
-/
theorem chartIncl_injective {S S' : Set L} (h : S ⊆ S') :
    Function.Injective (chartIncl K h) :=
  Subalgebra.inclusion_injective _

instance algebraAdjoin (S : Set L) : Algebra (Algebra.adjoin K S) (chartRing K S) :=
  (Subalgebra.inclusion (adjoin_le_chartRing K S)).toRingHom.toAlgebra

/--
@isnad1 id=isscalar.0h3v.s8.b2d9ea37b2ad from=translated src=- shape=32208047 vocab=0e9344c8
-/
instance isScalarTower_adjoin (S : Set L) :
    IsScalarTower (Algebra.adjoin K S) (chartRing K S) L :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/--
@isnad1 id=isscalar.0h3v.s9.ebaa08b5a256 from=translated src=- shape=0f9f6260 vocab=0e9344c8
-/
instance isScalarTower_base_adjoin (S : Set L) :
    IsScalarTower K (Algebra.adjoin K S) (chartRing K S) :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

/--
@isnad1 id=isintegr.0h3v.s8.aab81ca17825 from=translated src=- shape=32208047 vocab=34eca129
-/
instance isIntegralClosure (S : Set L) : IsIntegralClosure (chartRing K S) (Algebra.adjoin K S) L where
  algebraMap_injective := Subtype.val_injective
  isIntegral_iff {x} := ⟨fun hx => ⟨⟨x, hx⟩, rfl⟩, by rintro ⟨y, rfl⟩; exact y.2⟩

section OneGenerator

variable (s : L) [FiniteDimensional K⟮s⟯ L] [CharZero K]

/--
@isnad1 id=charzero.0h3v.s8.c0b0c9962c7a from=translated src=- shape=c6b2e26d vocab=adaa039d
-/
scoped instance charZero_adjoin_simple : CharZero K⟮s⟯ :=
  charZero_of_injective_algebraMap (algebraMap K K⟮s⟯).injective

/--
@isnad1 id=issepara.0h3v.s8.e8e7c99f2c40 from=translated src=- shape=898fd861 vocab=cede4fbd
-/
scoped instance isSeparable_adjoin_simple : Algebra.IsSeparable K⟮s⟯ L :=
  Algebra.IsAlgebraic.isSeparable_of_perfectField

open scoped IntermediateField.algebraAdjoinAdjoin in
/--
@isnad1 id=isdedeki.0h3v.s8.c93fa713e30f from=translated src=- shape=bed84b05 vocab=87ce4ddf
-/
instance isDedekindDomain_chartRing : IsDedekindDomain (chartRing K ({s} : Set L)) :=
  IsIntegralClosure.isDedekindDomain (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

open scoped IntermediateField.algebraAdjoinAdjoin in
/--
@isnad1 id=finite.0h3v.s9.a4e7325d3361 from=translated src=- shape=77e6ab80 vocab=6e53c48a
-/
instance finite_chartRing :
    Module.Finite (Algebra.adjoin K ({s} : Set L)) (chartRing K ({s} : Set L)) :=
  IsIntegralClosure.finite (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

open scoped IntermediateField.algebraAdjoinAdjoin in
/--
@isnad1 id=isfracti.0h3v.s8.115d783a335f from=translated src=- shape=6d846f7e vocab=62b03b93
-/
instance isFractionRing_chartRing : IsFractionRing (chartRing K ({s} : Set L)) L :=
  IsIntegralClosure.isFractionRing_of_finite_extension (Algebra.adjoin K ({s} : Set L)) K⟮s⟯ L _

/--
@isnad1 id=finitety.0h3v.s8.a31085bfd53d from=translated src=- shape=b27e0806 vocab=e11038d1
-/
instance finiteType_chartRing : Algebra.FiniteType K (chartRing K ({s} : Set L)) :=
  (Algebra.FiniteType.adjoin_of_finite (R := K) (Set.finite_singleton s)).trans
    (inferInstance : Algebra.FiniteType (Algebra.adjoin K ({s} : Set L)) (chartRing K ({s} : Set L)))

/--
@isnad1 id=isnoethe.0h3v.s8.e9d9a37fc477 from=translated src=- shape=bed84b05 vocab=b567c4cb
-/
instance isNoetherianRing_chartRing : IsNoetherianRing (chartRing K ({s} : Set L)) :=
  inferInstance

end OneGenerator

section Valuation

variable {K}

/--
@isnad1 id=mem.3h5v.s7.73863eee389b from=translated src=- shape=4d9e8556 vocab=a3766cdc
-/
theorem adjoin_le_valuationSubring (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) {S : Set L} (hS : S ⊆ O) {y : L}
    (hy : y ∈ Algebra.adjoin K S) : y ∈ O := by
  induction hy using Algebra.adjoin_induction with
  | mem y hy => exact hS hy
  | algebraMap a => exact hK a
  | add y z _ _ hy hz => exact add_mem hy hz
  | mul y z _ _ hy hz => exact mul_mem hy hz

def _root_.ValuationSubring.toSubalgebraOfBase (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) : Subalgebra K L :=
  { O.toSubring with algebraMap_mem' := hK }

/--
@isnad1 id=integers.1h3v.s7.26b5a9da19c4 from=translated src=- shape=073ae85d vocab=83b7ae87
-/
theorem _root_.ValuationSubring.integers_toSubalgebraOfBase (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) : O.valuation.Integers (O.toSubalgebraOfBase hK) where
  hom_inj := Subtype.val_injective
  map_le_one a := (O.valuation_le_one_iff _).mpr a.2
  exists_of_le_one r hr := ⟨⟨r, O.mem_of_valuation_le_one r hr⟩, rfl⟩

/--
@isnad1 id=mem.3h5v.s7.f9e790d86c5a from=translated src=- shape=4d9e8556 vocab=3e36a32c
-/
theorem chartRing_le_valuationSubring (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) {S : Set L} (hS : S ⊆ O) {x : L}
    (hx : x ∈ chartRing K S) : x ∈ O := by
  have hle : Algebra.adjoin K S ≤ O.toSubalgebraOfBase hK :=
    fun y hy => adjoin_le_valuationSubring O hK hS hy
  have hxO : IsIntegral (O.toSubalgebraOfBase hK) x := by
    have := ((mem_chartRing_iff K).mp hx).map_of_comp_eq (Subalgebra.inclusion hle).toRingHom
      (RingHom.id L) (by ext a; rfl)
    simpa using this
  exact O.mem_of_valuation_le_one x
    ((O.integers_toSubalgebraOfBase hK).isIntegral_iff_v_le_one.mp hxO)

variable (K)
variable (s : L)

def centre (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) :
    Ideal (chartRing K ({s} : Set L)) where
  carrier := {a | O.valuation a < 1}
  add_mem' {a b} ha hb := lt_of_le_of_lt (O.valuation.map_add a b) (max_lt ha hb)
  zero_mem' := by simp
  smul_mem' c a ha := by
    have hc : O.valuation c ≤ 1 := (O.valuation_le_one_iff _).mpr
      (chartRing_le_valuationSubring O hK (Set.singleton_subset_iff.mpr hs) c.2)
    show O.valuation ((c : L) * a) < 1
    rw [map_mul]
    exact mul_lt_of_le_one_of_lt hc ha

/--
@isnad1 id=iff.2h5v.s10.8e1ecc203eac from=translated src=- shape=cbc535f6 vocab=73609c9a
-/
theorem mem_centre_iff (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (a : chartRing K ({s} : Set L)) :
    a ∈ centre K s O hK hs ↔ O.valuation a < 1 := Iff.rfl

/--
@isnad1 id=le.2h5v.s8.e78f669428e6 from=translated src=- shape=2f373646 vocab=cbe5bbb6
-/
theorem valuation_coe_le_one (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (a : chartRing K ({s} : Set L)) : O.valuation a ≤ 1 :=
  (O.valuation_le_one_iff _).mpr
    (chartRing_le_valuationSubring O hK (Set.singleton_subset_iff.mpr hs) a.2)

/--
@isnad1 id=eq.3h5v.s10.e44cc31d81a0 from=translated src=- shape=f2e225a4 vocab=212395c2
-/
theorem valuation_eq_one_of_not_mem_centre (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) {a : chartRing K ({s} : Set L)}
    (ha : a ∉ centre K s O hK hs) : O.valuation a = 1 :=
  le_antisymm (valuation_coe_le_one K s O hK hs a) (not_lt.mp ha)

/--
@isnad1 id=isprime.2h4v.s7.ccad1bc8594f from=translated src=- shape=6ab8d8df vocab=c81d909c
-/
instance centre_isPrime (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) : (centre K s O hK hs).IsPrime where
  ne_top' := by
    rw [Ne, Ideal.eq_top_iff_one, mem_centre_iff]
    simp
  mem_or_mem' {a b} hab := by
    by_contra h
    push Not at h
    rw [mem_centre_iff, Subalgebra.coe_mul, map_mul,
      valuation_eq_one_of_not_mem_centre K s O hK hs h.1,
      valuation_eq_one_of_not_mem_centre K s O hK hs h.2, mul_one] at hab
    exact lt_irrefl _ hab

def chartPlaces (s : L) : Set (Place K L) := {v | s ∈ v.toValuationSubring}

/--
@isnad1 id=iff.0h4v.s6.09da358fea97 from=translated src=- shape=c3ed9d79 vocab=48d45d98
-/
theorem mem_chartPlaces_iff {s : L} {v : Place K L} :
    v ∈ chartPlaces K s ↔ s ∈ v.toValuationSubring := Iff.rfl

/--
@isnad1 id=or.0h4v.s6.1c321a9eacd9 from=translated src=- shape=d8e7ab1b vocab=db7bfe13
-/
theorem mem_chartPlaces_or_mem_chartPlaces_inv (v : Place K L) (t : L) :
    v ∈ chartPlaces K t ∨ v ∈ chartPlaces K t⁻¹ :=
  v.toValuationSubring.mem_or_inv_mem t

variable [FiniteDimensional K⟮s⟯ L] [CharZero K]

omit [CharZero K] in

/--
@isnad1 id=ne.3h4v.s9.5807164fecf3 from=translated src=- shape=02197221 vocab=e1c33c8a
-/
theorem centre_ne_bot (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (hO : O ≠ ⊤) : centre K s O hK hs ≠ ⊥ := by
  intro hbot
  apply hO
  refine top_unique fun x _ => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := chartRing K ({s} : Set L)) x
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbc : b ∉ centre K s O hK hs := by rw [hbot]; simpa using hb0
  apply O.mem_of_valuation_le_one
  rw [map_div₀, show O.valuation (algebraMap _ L b) = 1 from
    valuation_eq_one_of_not_mem_centre K s O hK hs hbc, div_one]
  exact valuation_coe_le_one K s O hK hs a

def primeOfValuationSubring (O : ValuationSubring L) (hK : ∀ a : K, algebraMap K L a ∈ O)
    (hs : s ∈ O) (hO : O ≠ ⊤) : HeightOneSpectrum (chartRing K ({s} : Set L)) :=
  ⟨centre K s O hK hs, inferInstance, centre_ne_bot K s O hK hs hO⟩

/--
@isnad1 id=le.3h4v.s8.3a421ba79b9e from=translated src=- shape=69ce9706 vocab=cf3dc0b9
-/
theorem valuationSubringAtPrime_le (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime L (primeOfValuationSubring K s O hK hs hO) ≤ O := by
  intro x hx
  have hx' : ∃ (a b : chartRing K ({s} : Set L)) (_ : b ∈ (centre K s O hK hs).primeCompl),
      x = algebraMap _ L a * (algebraMap _ L b)⁻¹ := hx
  obtain ⟨a, b, hb, rfl⟩ := hx'
  apply O.mem_of_valuation_le_one
  rw [map_mul, map_inv₀, show O.valuation (algebraMap _ L b) = 1 from
    valuation_eq_one_of_not_mem_centre K s O hK hs hb, inv_one, mul_one]
  exact valuation_coe_le_one K s O hK hs a

/--
@isnad1 id=eq.3h4v.s8.af9f57a530b1 from=translated src=- shape=69ce9706 vocab=8a99762c
-/
theorem valuationSubringAtPrime_primeOfValuationSubring (O : ValuationSubring L)
    (hK : ∀ a : K, algebraMap K L a ∈ O) (hs : s ∈ O) (hO : O ≠ ⊤) :
    HeightOneSpectrum.valuationSubringAtPrime L (primeOfValuationSubring K s O hK hs hO) = O :=
  ValuationSubring.eq_of_le_of_ne_top _ (valuationSubringAtPrime_le K s O hK hs hO) hO

/--
@isnad1 id=ex.1h4v.s9.fded219aa43f from=translated src=- shape=dd6b67fb vocab=409d1f2c
-/
theorem exists_ofHeightOneSpectrum_eq (v : Place K L) (hs : s ∈ v.toValuationSubring) :
    ∃ 𝔭 : HeightOneSpectrum (chartRing K ({s} : Set L)),
      Place.ofHeightOneSpectrum (K := K) 𝔭 = v := by
  refine ⟨primeOfValuationSubring K s v.toValuationSubring v.algebraMap_mem' hs v.ne_top', ?_⟩
  apply Place.ext
  rw [Place.ofHeightOneSpectrum_toValuationSubring,
    ← HeightOneSpectrum.valuationSubringAtPrime_eq_valuationSubring]
  exact valuationSubringAtPrime_primeOfValuationSubring K s _ _ hs _

/--
@isnad1 id=mem.0h4v.s8.425478b22aef from=translated src=- shape=96ff3dfb vocab=9e2ec193
-/
theorem mem_ofHeightOneSpectrum (𝔭 : HeightOneSpectrum (chartRing K ({s} : Set L))) :
    s ∈ (Place.ofHeightOneSpectrum (K := K) (F := L) 𝔭).toValuationSubring := by
  rw [Place.ofHeightOneSpectrum_toValuationSubring, Valuation.mem_valuationSubring_iff]
  exact 𝔭.valuation_le_one (K := L)
    (⟨s, subset_chartRing K ({s} : Set L) (Set.mem_singleton s)⟩ : chartRing K ({s} : Set L))

/--
@isnad1 id=injectiv.0h3v.s8.fff5366f7a0c from=translated src=- shape=e71ce47a vocab=6332ebe3
-/
theorem ofHeightOneSpectrum_injective :
    Function.Injective
      (Place.ofHeightOneSpectrum (K := K) (F := L) (R := chartRing K ({s} : Set L))) := by
  intro 𝔭 𝔮 h
  have hv := congrArg Place.toValuationSubring h
  simp only [Place.ofHeightOneSpectrum_toValuationSubring] at hv
  have hequiv := (Valuation.isEquiv_iff_valuationSubring _ _).mpr hv
  ext a
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L),
    ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := L)]
  exact hequiv.lt_one_iff_lt_one

def primeEquivChartPlaces : HeightOneSpectrum (chartRing K ({s} : Set L)) ≃ chartPlaces K s :=
  Equiv.ofBijective
    (fun 𝔭 => ⟨Place.ofHeightOneSpectrum (K := K) 𝔭, mem_ofHeightOneSpectrum K s 𝔭⟩)
    ⟨fun 𝔭 𝔮 h => ofHeightOneSpectrum_injective K s (congrArg Subtype.val h),
     fun v => by
      obtain ⟨𝔭, h𝔭⟩ := exists_ofHeightOneSpectrum_eq K s v.1 v.2
      exact ⟨𝔭, Subtype.ext h𝔭⟩⟩

/--
@isnad1 id=eq.0h4v.s10.79f9c190d488 from=translated src=- shape=6ba70b8c vocab=5b3502d8
-/
@[simp] theorem coe_primeEquivChartPlaces (𝔭 : HeightOneSpectrum (chartRing K ({s} : Set L))) :
    (primeEquivChartPlaces K s 𝔭 : Place K L) = Place.ofHeightOneSpectrum (K := K) 𝔭 :=
  rfl

end Valuation

section InvertGenerator

variable {K}

/--
@isnad1 id=ex.3h5v.s8.735962cf7195 from=translated src=- shape=9c79a45b vocab=b6ca1f4e
-/
theorem exists_pow_mul_mem_adjoin {S : Set L} {s : L} (hs : s ∈ S) (hs0 : s ≠ 0) {x : L}
    (hx : x ∈ Algebra.adjoin K (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ Algebra.adjoin K S := by
  have hsA : s ∈ Algebra.adjoin K S := Algebra.subset_adjoin hs
  induction hx using Algebra.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | hy
    · exact ⟨1, by rw [pow_one, mul_inv_cancel₀ hs0]; exact one_mem _⟩
    · exact ⟨0, by rw [pow_zero, one_mul]; exact Algebra.subset_adjoin hy⟩
  | algebraMap a => exact ⟨0, by rw [pow_zero, one_mul]; exact Subalgebra.algebraMap_mem _ a⟩
  | add y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y + z) = s ^ n * (s ^ m * y) + s ^ m * (s ^ n * z) := by ring
    rw [this]
    exact add_mem (mul_mem (pow_mem hsA n) hm) (mul_mem (pow_mem hsA m) hn)
  | mul y z _ _ hy hz =>
    obtain ⟨m, hm⟩ := hy
    obtain ⟨n, hn⟩ := hz
    refine ⟨m + n, ?_⟩
    have : s ^ (m + n) * (y * z) = (s ^ m * y) * (s ^ n * z) := by ring
    rw [this]
    exact mul_mem hm hn

/--
@isnad1 id=ex.3h5v.s7.08b319af4759 from=translated src=- shape=9c79a45b vocab=60395727
-/
theorem exists_pow_mul_mem_chartRing {S : Set L} {s : L} (hs : s ∈ S) (hs0 : s ≠ 0) {x : L}
    (hx : x ∈ chartRing K (insert s⁻¹ S)) : ∃ n : ℕ, s ^ n * x ∈ chartRing K S := by
  classical
  obtain ⟨p, hmonic, hroot⟩ := (mem_chartRing_iff K).mp hx

  have hcoeff : ∀ i, ∃ n : ℕ, s ^ n * (p.coeff i : L) ∈ Algebra.adjoin K S :=
    fun i => exists_pow_mul_mem_adjoin hs hs0 (p.coeff i).2
  choose n hn using hcoeff
  set N : ℕ := ∑ i ∈ Finset.range (p.natDegree + 1), n i with hN
  have hnN : ∀ i ≤ p.natDegree, n i ≤ N := fun i hi =>
    Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _)
      (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))

  set q : L[X] := (p.map (algebraMap (Algebra.adjoin K (insert s⁻¹ S)) L)).scaleRoots (s ^ N)
    with hq
  have hqmonic : q.Monic := (Polynomial.monic_scaleRoots_iff _).mpr (hmonic.map _)
  have hqroot : q.eval (s ^ N * x) = 0 := by
    rw [hq, Polynomial.scaleRoots_eval_mul, Polynomial.eval_map, hroot, mul_zero]

  have hqcoeff : ∀ i, q.coeff i ∈ Algebra.adjoin K S := by
    intro i
    rw [hq, Polynomial.coeff_scaleRoots, Polynomial.coeff_map, hmonic.natDegree_map]
    by_cases hi : i < p.natDegree
    · have hle : n i ≤ N * (p.natDegree - i) := by
        calc n i ≤ N := hnN i hi.le
          _ = N * 1 := (mul_one N).symm
          _ ≤ N * (p.natDegree - i) := Nat.mul_le_mul_left N (Nat.one_le_iff_ne_zero.mpr (by omega))
      obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
      have : (s ^ N) ^ (p.natDegree - i) = s ^ k * s ^ n i := by
        rw [← pow_mul, hk, pow_add, mul_comm]
      rw [this, Subalgebra.algebraMap_def, Algebra.algebraMap_self_apply,
        show (p.coeff i : L) * (s ^ k * s ^ n i) = s ^ k * (s ^ n i * (p.coeff i : L)) by ring]
      exact mul_mem (pow_mem (Algebra.subset_adjoin hs) k) (hn i)
    · rcases (not_lt.mp hi).lt_or_eq with hlt | heq
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hlt, map_zero, zero_mul]
        exact zero_mem _
      · rw [← heq, hmonic.coeff_natDegree, map_one, one_mul, Nat.sub_self, pow_zero]
        exact one_mem _

  have hlifts : q ∈ Polynomial.lifts (algebraMap (Algebra.adjoin K S) L) :=
    (Polynomial.lifts_iff_coeff_lifts q).mpr fun i => ⟨⟨q.coeff i, hqcoeff i⟩, rfl⟩
  obtain ⟨q', hq'q, -, hq'monic⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlifts hqmonic
  refine ⟨N, (mem_chartRing_iff K).mpr ⟨q', hq'monic, ?_⟩⟩
  rw [Polynomial.eval₂_eq_eval_map, hq'q, hqroot]

end InvertGenerator

end CurveModel

end AlgebraicCurve

end
