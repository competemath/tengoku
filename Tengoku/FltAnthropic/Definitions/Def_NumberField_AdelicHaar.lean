import Tengoku.Seed.NumberTheory.NumberField.AdeleRing
import Tengoku.Seed.NumberTheory.NumberField.Completion.FinitePlace
import Tengoku.Seed.Topology.Algebra.Valued.LocallyCompact

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open IsDedekindDomain NumberField MeasureTheory
open scoped RestrictedProduct

noncomputable section

namespace NumberField.AdelicHaar

section Local

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K] (v : HeightOneSpectrum R)

/--
@isnad1 id=fact.0h2v.s7.fa7840a47e32 from=translated src=- shape=ca282281 vocab=1e53a331
-/
instance fact_isOpen_adicCompletionIntegers :
    Fact (∀ v : HeightOneSpectrum R,
      IsOpen (v.adicCompletionIntegers K : Set (v.adicCompletion K))) :=
  ⟨fun _ => Valued.isOpen_valuationSubring _⟩

/--
@isnad1 id=ex.0h4v.s9.144758be6d7b from=translated src=- shape=f051eb47 vocab=55bd60ba
-/
theorem exists_valued_algebraMap_sub_lt_one (x : v.adicCompletionIntegers K) :
    ∃ a : R, Valued.v ((algebraMap R (v.adicCompletion K) a) - (x : v.adicCompletion K)) < 1 := by
  have hn : {z : v.adicCompletion K | Valued.v (z - (x : v.adicCompletion K)) < 1} ∈
      nhds (x : v.adicCompletion K) := by
    refine Valued.mem_nhds.mpr ⟨1, fun z hz => ?_⟩
    have hz' : Valued.v.restrict (z - (x : v.adicCompletion K)) < 1 := by
      rw [← Units.val_one]; exact hz
    exact (Valuation.restrict_lt_one_iff _).mp hz'
  obtain ⟨_, hz, y, rfl⟩ := mem_closure_iff_nhds.mp
    (HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v) (x : v.adicCompletion K)) _ hn
  have hy1 : Valued.v (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) < 1 := hz
  have hyint : v.valuation K y ≤ 1 := by
    have hx1 : Valued.v (x : v.adicCompletion K) ≤ 1 := x.2
    have h : Valued.v (algebraMap K (v.adicCompletion K) y) ≤ 1 := by
      have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
        (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K)) (x : v.adicCompletion K)
      rw [sub_add_cancel] at this
      exact this.trans (max_le hy1.le hx1)
    rwa [show algebraMap K (v.adicCompletion K) y = (y : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation'] at h
  obtain ⟨a, ha⟩ := HeightOneSpectrum.exists_valuation_sub_lt_of_integer v hyint 1
  refine ⟨a, ?_⟩
  have ha' : Valued.v ((algebraMap R (v.adicCompletion K) a) -
      algebraMap K (v.adicCompletion K) y) < 1 := by
    rw [IsScalarTower.algebraMap_apply R K (v.adicCompletion K) a, ← map_sub,
      show algebraMap K (v.adicCompletion K) (algebraMap R K a - y) =
        ((algebraMap R K a - y : K) : v.adicCompletion K) from rfl,
      HeightOneSpectrum.valuedAdicCompletion_eq_valuation']
    exact ha.trans_eq Units.val_one
  have := Valuation.map_add (Valued.v : Valuation (v.adicCompletion K) _)
    ((algebraMap R (v.adicCompletion K) a) - algebraMap K (v.adicCompletion K) y)
    (algebraMap K (v.adicCompletion K) y - (x : v.adicCompletion K))
  rw [sub_add_sub_cancel] at this
  exact lt_of_le_of_lt this (max_lt ha' hy1)

/--
@isnad1 id=iff.0h4v.s11.4a64db35a483 from=translated src=- shape=614da919 vocab=fdb53050
-/
theorem mem_maximalIdeal_iff_valued_lt_one (d : v.adicCompletionIntegers K) :
    d ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers K) ↔
      Valued.v (d : v.adicCompletion K) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    HeightOneSpectrum.adicCompletionIntegers.isUnit_iff_valued_eq_one]
  have hd : Valued.v (d : v.adicCompletion K) ≤ 1 := d.2
  exact ⟨fun h => lt_of_le_of_ne hd h, fun h => ne_of_lt h⟩

/--
@isnad1 id=surjecti.0h3v.s12.df09fc77a016 from=translated src=- shape=10278560 vocab=7577c1c0
-/
theorem residue_algebraMap_surjective :
    Function.Surjective (fun a : R =>
      IsLocalRing.residue (v.adicCompletionIntegers K)
        (algebraMap R (v.adicCompletionIntegers K) a)) := by
  intro z
  obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
  obtain ⟨a, ha⟩ := exists_valued_algebraMap_sub_lt_one R K v x
  refine ⟨a, ?_⟩
  show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [Ideal.Quotient.eq, mem_maximalIdeal_iff_valued_lt_one]
  simpa [HeightOneSpectrum.algebraMap_adicCompletion] using ha

/--
@isnad1 id=eq.1h4v.s12.e14aac6f0cfb from=translated src=- shape=9ee30947 vocab=d8406d85
-/
theorem residue_algebraMap_eq_zero_of_mem {a : R} (ha : a ∈ v.asIdeal) :
    IsLocalRing.residue (v.adicCompletionIntegers K)
      (algebraMap R (v.adicCompletionIntegers K) a) = 0 := by
  rw [IsLocalRing.residue_eq_zero_iff, mem_maximalIdeal_iff_valued_lt_one]
  simp only [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply]
  rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
  exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v a).mpr ha

variable [Module.Free ℤ R] [Module.Finite ℤ R]

/--
@isnad1 id=finite.0h3v.s7.6991d0480634 from=translated src=- shape=a25b815f vocab=3f0e4a43
-/
instance finite_residueField_adicCompletionIntegers :
    Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)) := by
  haveI : Finite (R ⧸ v.asIdeal) := Ideal.finiteQuotientOfFreeOfNeBot v.asIdeal v.ne_bot
  let f : R ⧸ v.asIdeal → IsLocalRing.ResidueField (v.adicCompletionIntegers K) :=
    Ideal.Quotient.lift v.asIdeal
      ((IsLocalRing.residue (v.adicCompletionIntegers K)).comp
        (algebraMap R (v.adicCompletionIntegers K)))
      (fun a ha => residue_algebraMap_eq_zero_of_mem R K v ha)
  refine Finite.of_surjective f fun z => ?_
  obtain ⟨a, ha⟩ := residue_algebraMap_surjective R K v z
  exact ⟨Ideal.Quotient.mk _ a, ha⟩

open scoped Valued in

/--
@isnad1 id=propersp.0h3v.s7.e9eb2bf43c53 from=translated src=- shape=225c0b71 vocab=b716595d
-/
instance properSpace_adicCompletion : ProperSpace (v.adicCompletion K) := by
  haveI : IsDiscreteValuationRing 𝒪[v.adicCompletion K] :=
    inferInstanceAs (IsDiscreteValuationRing (v.adicCompletionIntegers K))
  haveI : Finite 𝓀[v.adicCompletion K] :=
    inferInstanceAs (Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers K)))
  exact Valued.integer.properSpace_iff_completeSpace_and_isDiscreteValuationRing_integer_and_finite_residueField.mpr
    ⟨inferInstance, inferInstance, inferInstance⟩

open scoped Valued in

/--
@isnad1 id=compacts.0h3v.s8.3ab72fbfef61 from=translated src=- shape=ab5c6929 vocab=bda06808
-/
instance compactSpace_adicCompletionIntegers : CompactSpace (v.adicCompletionIntegers K) := by
  have h : CompactSpace 𝒪[v.adicCompletion K] :=
    Valued.integer.properSpace_iff_compactSpace_integer.mp inferInstance
  exact h

end Local

section Adele

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/--
@isnad1 id=t2space.0h2v.s5.9b2497f59a34 from=translated src=- shape=98925e46 vocab=b25b9c96
-/
instance t2Space_finiteAdeleRing : T2Space (FiniteAdeleRing R K) :=
  inferInstanceAs (T2Space (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

/--
@isnad1 id=t2space.0h1v.s3.c0b7b608541a from=translated src=- shape=1666ae32 vocab=74ec96c3
-/
instance t2Space_infiniteAdeleRing : T2Space (InfiniteAdeleRing K) :=
  inferInstanceAs (T2Space ((v : InfinitePlace K) → v.Completion))

/--
@isnad1 id=t2space.0h2v.s5.afdfc7afcdaa from=translated src=- shape=98925e46 vocab=d1064f32
-/
instance t2Space_adeleRing : T2Space (AdeleRing R K) :=
  inferInstanceAs (T2Space (InfiniteAdeleRing K × FiniteAdeleRing R K))

@[reducible] def adeleBorel : MeasurableSpace (AdeleRing R K) := borel _

/--
@isnad1 id=borelspa.0h2v.s6.36eddb822483 from=translated src=- shape=98925e46 vocab=4c70e9b0
-/
theorem borelSpace_adeleBorel : @BorelSpace (AdeleRing R K) _ (adeleBorel R K) :=
  @BorelSpace.mk _ _ (adeleBorel R K) rfl

variable [Module.Free ℤ R] [Module.Finite ℤ R]

/--
@isnad1 id=locallyc.0h2v.s6.cba3b3347287 from=translated src=- shape=bb5be406 vocab=05b79087
-/
instance locallyCompactSpace_finiteAdeleRing : LocallyCompactSpace (FiniteAdeleRing R K) :=
  inferInstanceAs (LocallyCompactSpace
    (Πʳ v : HeightOneSpectrum R, [v.adicCompletion K, v.adicCompletionIntegers K]))

/--
@isnad1 id=locallyc.0h2v.s6.8981554a364d from=translated src=- shape=4e6c09ca vocab=163d9a97
-/
instance locallyCompactSpace_adeleRing [NumberField K] : LocallyCompactSpace (AdeleRing R K) :=
  inferInstanceAs (LocallyCompactSpace (InfiniteAdeleRing K × FiniteAdeleRing R K))

def adelicAddHaar [NumberField K] : @Measure (AdeleRing R K) (adeleBorel R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  exact Measure.addHaar

/--
@isnad1 id=isaddhaa.0h2v.s7.66bbfb192be1 from=translated src=- shape=18ea43be vocab=388a1075
-/
theorem isAddHaarMeasure_adelicAddHaar [NumberField K] :
    @Measure.IsAddHaarMeasure (AdeleRing R K) _ _ (adeleBorel R K) (adelicAddHaar R K) := by
  letI := adeleBorel R K
  haveI := borelSpace_adeleBorel R K
  exact Measure.isAddHaarMeasure_addHaarMeasure _

end Adele

section GeneralLinear

variable (n : Type*) (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]

/--
@isnad1 id=t2space.0h3v.s6.00009e0b9579 from=translated src=- shape=635dedb3 vocab=89269899
-/
instance t2Space_matrix_adeleRing : T2Space (Matrix n n (AdeleRing R K)) :=
  inferInstanceAs (T2Space (n → n → AdeleRing R K))

/--
@isnad1 id=locallyc.0h3v.s6.4a594dac917e from=translated src=- shape=ff4ac482 vocab=78ab6a94
-/
instance locallyCompactSpace_matrix_adeleRing [Finite n] [Module.Free ℤ R] [Module.Finite ℤ R]
    [NumberField K] : LocallyCompactSpace (Matrix n n (AdeleRing R K)) :=
  inferInstanceAs (LocallyCompactSpace (n → n → AdeleRing R K))

variable [Fintype n] [DecidableEq n]

/--
@isnad1 id=t2space.0h3v.s7.2a74fa177f10 from=translated src=- shape=86a4cc95 vocab=80e42503
-/
instance t2Space_gl_adeleRing : T2Space (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  inferInstance

@[reducible] def glBorel : MeasurableSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  borel _

/--
@isnad1 id=borelspa.0h3v.s7.ea15bab169b8 from=translated src=- shape=86a4cc95 vocab=629ff98f
-/
theorem borelSpace_glBorel :
    @BorelSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) _ (glBorel n R K) :=
  @BorelSpace.mk _ _ (glBorel n R K) rfl

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

/--
@isnad1 id=locallyc.0h3v.s7.6a95580d6fee from=translated src=- shape=70547da8 vocab=490b1d15
-/
instance locallyCompactSpace_gl_adeleRing :
    LocallyCompactSpace (Matrix.GeneralLinearGroup n (AdeleRing R K)) :=
  inferInstance

def adelicGLHaar : @Measure (Matrix.GeneralLinearGroup n (AdeleRing R K)) (glBorel n R K) := by
  letI := glBorel n R K
  haveI := borelSpace_glBorel n R K
  exact Measure.haar

/--
@isnad1 id=ishaarme.0h3v.s8.5b000adf7a8c from=translated src=- shape=59c52805 vocab=d5affc97
-/
theorem isHaarMeasure_adelicGLHaar :
    @Measure.IsHaarMeasure (Matrix.GeneralLinearGroup n (AdeleRing R K)) _ _ (glBorel n R K)
      (adelicGLHaar n R K) := by
  letI := glBorel n R K
  haveI := borelSpace_glBorel n R K
  exact Measure.isHaarMeasure_haarMeasure _

end GeneralLinear

end NumberField.AdelicHaar

end
