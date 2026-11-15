import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicHaar
import Tengoku.FltAnthropic.Definitions.Def_AutomorphicForm_AdelicLsXi

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open IsDedekindDomain NumberField NumberField.AdelicHaar MeasureTheory

noncomputable section

namespace AutomorphicForm

structure CarrierPins (F : Type*) [Field F] [NumberField F] where
  mS : MeasurableSpace (AdelicGL2 (𝓞 F) F)
  μ : @Measure (AdelicGL2 (𝓞 F) F) mS
  D : Set (AdelicGL2 (𝓞 F) F)
  Z : Subgroup (AdeleRing (𝓞 F) F)ˣ
  U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F)
  gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F
  nS : MeasurableSpace (AdeleRing (𝓞 F) F)
  ν : @Measure (AdeleRing (𝓞 F) F) nS

def productionPinsOf (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F))
    (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F)
    (B : Set (AdeleRing (𝓞 F) F)) :
    CarrierPins F where
  mS := glBorel (Fin 2) (𝓞 F) F
  μ := adelicGLHaar (Fin 2) (𝓞 F) F
  D := D
  Z := ⊤
  U := U
  gen := gen
  nS := adeleBorel (𝓞 F) F
  ν := @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) B

/--
@isnad1 id=eq.0h5v.s8.0a3ff7bd8db2 from=translated src=- shape=32b36c2c vocab=89fe9eee
-/
theorem productionPinsOf_mS (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).mS = glBorel (Fin 2) (𝓞 F) F := rfl

/--
@isnad1 id=eq.0h5v.s9.0dff7b43f9ca from=translated src=- shape=898a4b67 vocab=d696371e
-/
theorem productionPinsOf_Z (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).Z = ⊤ := rfl

/--
@isnad1 id=eq.0h5v.s8.46d2448a7c36 from=translated src=- shape=f767f10e vocab=49ab89b0
-/
theorem productionPinsOf_nS (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).nS = adeleBorel (𝓞 F) F := rfl

/--
@isnad1 id=eq.0h5v.s8.ce0b548f968b from=translated src=- shape=cc733a66 vocab=29550d3c
-/
theorem productionPinsOf_D (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).D = D := rfl

/--
@isnad1 id=eq.0h5v.s8.7621f9dbf30b from=translated src=- shape=e14cfd91 vocab=821d8690
-/
theorem productionPinsOf_U (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).U = U := rfl

/--
@isnad1 id=eq.0h5v.s8.82db7320260c from=translated src=- shape=52a307dc vocab=364e705e
-/
theorem productionPinsOf_gen (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).gen = gen := rfl

/--
@isnad1 id=eq.0h5v.s8.fabb8a9703e5 from=translated src=- shape=7847944a vocab=d6365600
-/
theorem productionPinsOf_ν (F : Type) [Field F] [NumberField F] (D U gen B) :
    (productionPinsOf F D U gen B).ν
      = @ProbabilityTheory.cond _ (adeleBorel (𝓞 F) F) (adelicAddHaar (𝓞 F) F) B := rfl

/--
@isnad1 id=ishaarme.0h5v.s9.a1eedd395ff8 from=translated src=- shape=5460de42 vocab=8c21cf8d
-/
theorem isHaarMeasure_productionPinsOf_μ (F : Type) [Field F] [NumberField F] (D U gen B) :
    @Measure.IsHaarMeasure _ _ _ (productionPinsOf F D U gen B).mS
      (productionPinsOf F D U gen B).μ :=
  isHaarMeasure_adelicGLHaar (Fin 2) (𝓞 F) F

/--
@isnad1 id=isprobab.2h5v.s8.80ebcbd26971 from=translated src=- shape=7125d55e vocab=555fb503
-/
theorem isProbabilityMeasure_productionPinsOf_ν (F : Type) [Field F] [NumberField F]
    (D : Set (AdelicGL2 (𝓞 F) F)) (U : Ideal (𝓞 F) → Subgroup (AdelicGL2 (𝓞 F) F))
    (gen : HeightOneSpectrum (𝓞 F) → AdelicGL2 (𝓞 F) F) (B : Set (AdeleRing (𝓞 F) F))
    (hB0 : adelicAddHaar (𝓞 F) F B ≠ 0) (hBtop : adelicAddHaar (𝓞 F) F B ≠ ⊤) :
    @IsProbabilityMeasure _ (productionPinsOf F D U gen B).nS
      (productionPinsOf F D U gen B).ν := by
  letI := adeleBorel (𝓞 F) F
  exact ProbabilityTheory.cond_isProbabilityMeasure_of_finite hB0 hBtop

end AutomorphicForm

end
