module

public import Tengoku

@[expose] public section

open MeasureTheory ENNReal WithLp

namespace ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

section HasLaw

variable {𝓧} {m𝓧 : MeasurableSpace 𝓧} {X : Ω → 𝓧} {μ : Measure 𝓧} {P : Measure Ω}

/--
@isnad1 id=haslaw.1h6v.s5.8b19d404b557 from=translated src=- shape=32f0199b vocab=f8eca661
-/
lemma hasLaw_map (hX : AEMeasurable X P) : HasLaw X (P.map X) P where
  aemeasurable := hX
  map_eq := rfl

section dirac

-- don't upstream this: it's too specific. Delete it here eventually.
/--
@isnad1 id=eventual.1h5v.s5.a35558834a7f from=translated src=- shape=1558ecc0 vocab=f53c2b09
-/
lemma HasLaw.ae_eq_const_of_gaussianReal {X : Ω → ℝ} {μ : ℝ} (hX : HasLaw X (gaussianReal μ 0) P) :
    ∀ᵐ ω ∂P, X ω = μ := by
  rw [gaussianReal_zero_var] at hX
  exact hX.ae_eq_of_dirac

end dirac

end HasLaw

end ProbabilityTheory
