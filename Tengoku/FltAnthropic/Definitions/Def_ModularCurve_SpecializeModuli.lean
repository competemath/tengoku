import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularCurve_JqCoeff
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Tengoku.FltAnthropic.Theorems.Thm_ModularCurve_transcendental_jqModC

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section Transcendence

variable (K : Type*) [Field K]

def ratFuncEquivCharLOneC : RatFunc K ≃ₐ[K] (modularFunctionFieldC K 1) :=
  (RatFunc.algEquivOfTranscendental (jqModC K) (transcendental_jqModC K)).trans
    (IntermediateField.equivOfEq (modularFunctionFieldC_one K).symm)

end Transcendence

section Jacobian

variable (K : Type*) [Field K]

abbrev charLJacobian (N : ℕ) [NeZero N] : Type _ :=
  Pic0 K (modularFunctionFieldC K N)

def charLGeomPlaceEquiv :
    Place K (RatFunc K) ≃ Place K (modularFunctionFieldC K 1) :=
  Place.congrEquiv (ratFuncEquivCharLOneC K).toRingEquiv
    (fun a => (ratFuncEquivCharLOneC K).commutes a)

def charLGeomPlaceOfPoint (a : K) : Place K (modularFunctionFieldC K 1) :=
  charLGeomPlaceEquiv K (RationalFunctionField.placeOfPoint K a)

/--
@isnad1 id=injectiv.0h1v.s9.155f09e5643c from=translated src=- shape=7f3534a7 vocab=3c9c541b
-/
theorem charLGeomPlaceOfPoint_injective : Function.Injective (charLGeomPlaceOfPoint K) :=
  fun _ _ h => RationalFunctionField.placeOfPoint_injective K
    ((charLGeomPlaceEquiv K).injective h)

def charLGeomModuliDictionary :
    (K →₀ ℤ) →+ Divisor K (modularFunctionFieldC K 1) :=
  Finsupp.mapDomain.addMonoidHom (charLGeomPlaceOfPoint K)

/--
@isnad1 id=injectiv.0h1v.s12.87489e6f2441 from=translated src=- shape=cc901eee vocab=07c2b358
-/
theorem charLGeomModuliDictionary_injective :
    Function.Injective (charLGeomModuliDictionary K) :=
  Finsupp.mapDomain_injective (charLGeomPlaceOfPoint_injective K)

/--
@isnad1 id=eq.0h3v.s12.42ae1f0bc21f from=translated src=- shape=425e410e vocab=f09c2067
-/
@[simp]
theorem charLGeomModuliDictionary_single (a : K) (n : ℤ) :
    charLGeomModuliDictionary K (Finsupp.single a n)
      = Finsupp.single (charLGeomPlaceOfPoint K a) n := by
  simp only [charLGeomModuliDictionary, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain_single]

end Jacobian

section Map

variable {K k : Type*} [Field K] [Field k]

def specializePlace (r : K → k) (a : K) : Place k (modularFunctionFieldC k 1) :=
  charLGeomPlaceOfPoint k (r a)

omit [Field K] in
/--
@isnad1 id=eq.0h4v.s9.d1972017bee3 from=translated src=- shape=70b30820 vocab=6f924309
-/
@[simp]
theorem specializePlace_def (r : K → k) (a : K) :
    specializePlace r a = charLGeomPlaceOfPoint k (r a) := rfl

omit [Field K] in

/--
@isnad1 id=eq.1h5v.s9.ae57952ca996 from=translated src=- shape=ec96d820 vocab=6966b303
-/
theorem specializePlace_eq_of_eq (r : K → k) {a b : K} (h : r a = r b) :
    specializePlace r a = specializePlace r b := by
  simp only [specializePlace, h]

omit [Field K] in

/--
@isnad1 id=iff.0h5v.s9.21b55bf70429 from=translated src=- shape=5169b175 vocab=6966b303
-/
theorem specializePlace_inj_iff (r : K → k) {a b : K} :
    specializePlace r a = specializePlace r b ↔ r a = r b :=
  ⟨fun h => charLGeomPlaceOfPoint_injective k h, specializePlace_eq_of_eq r⟩

def specializeModuli (r : K → k) :
    (K →₀ ℤ) →+ Divisor k (modularFunctionFieldC k 1) :=
  (charLGeomModuliDictionary k).comp (Finsupp.mapDomain.addMonoidHom r)

omit [Field K] in
/--
@isnad1 id=eq.0h5v.s12.33e12f008b60 from=translated src=- shape=43c6edb7 vocab=aacecf4c
-/
@[simp]
theorem specializeModuli_single (r : K → k) (a : K) (n : ℤ) :
    specializeModuli r (Finsupp.single a n)
      = Finsupp.single (specializePlace r a) n := by
  simp only [specializeModuli, AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_single,
    charLGeomModuliDictionary_single, specializePlace_def]

omit [Field K] in

/--
@isnad1 id=eq.0h4v.s12.61dd626e733d from=translated src=- shape=fbf3a0e8 vocab=92801bb3
-/
theorem specializeModuli_eq_mapDomain (r : K → k) (D : K →₀ ℤ) :
    specializeModuli r D = Finsupp.mapDomain (specializePlace r) D := by
  simp only [specializeModuli, AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply, charLGeomModuliDictionary,
    Finsupp.mapDomain.addMonoidHom_apply]
  rw [← Finsupp.mapDomain_comp]
  rfl

/--
@isnad1 id=eq.0h2v.s13.baed6e173d03 from=translated src=- shape=a8519bb0 vocab=9e7da703
-/
theorem specializeModuli_id (D : K →₀ ℤ) :
    specializeModuli (id : K → K) D = charLGeomModuliDictionary K D := by
  simp only [specializeModuli, AddMonoidHom.coe_comp, Function.comp_apply,
    Finsupp.mapDomain.addMonoidHom_apply, Finsupp.mapDomain_id]

omit [Field K] in
open scoped Classical in

/--
@isnad1 id=le.0h4v.s13.5047e8da2079 from=translated src=- shape=475b6926 vocab=dad13d60
-/
theorem support_specializeModuli_subset (r : K → k) (D : K →₀ ℤ) :
    (specializeModuli r D).support ⊆ D.support.image (specializePlace r) := by
  rw [specializeModuli_eq_mapDomain]
  exact Finsupp.mapDomain_support

end Map

section Degree

variable {K k : Type*} [Field K] [Field k]

end Degree

section Galois

variable {K k : Type*} [Field K] [Field k]

omit [Field K] in

/--
@isnad1 id=eq.0h5v.s13.995cbaf5f3aa from=translated src=- shape=ef106a7e vocab=935b3d96
-/
theorem specializeModuli_mapDomain (r : K → k) (σ : K → K) (D : K →₀ ℤ) :
    specializeModuli r (Finsupp.mapDomain σ D) = specializeModuli (r ∘ σ) D := by
  rw [specializeModuli_eq_mapDomain, specializeModuli_eq_mapDomain,
    ← Finsupp.mapDomain_comp]
  rfl

omit [Field K] in

/--
@isnad1 id=eq.1h5v.s13.390fbd6bcee7 from=translated src=- shape=2fe47b1b vocab=4c236c04
-/
theorem specializeModuli_inertia_invariant (r : K → k) (σ : K → K)
    (hσ : ∀ a, r (σ a) = r a) (D : K →₀ ℤ) :
    specializeModuli r (Finsupp.mapDomain σ D) = specializeModuli r D := by
  rw [specializeModuli_mapDomain, show (r ∘ σ) = r from funext hσ]

omit [Field K] in

/--
@isnad1 id=eq.1h6v.s13.210a7e674ee9 from=translated src=- shape=8548bfce vocab=9197c604
-/
theorem specializeModuli_intertwines (r : K → k) (σ : K → K) (τ : k → k)
    (h : ∀ a, r (σ a) = τ (r a)) (D : K →₀ ℤ) :
    specializeModuli r (Finsupp.mapDomain σ D)
      = charLGeomModuliDictionary k
          (Finsupp.mapDomain τ (Finsupp.mapDomain r D)) := by
  rw [specializeModuli_mapDomain, show (r ∘ σ) = (τ ∘ r) from funext h,
    ← Finsupp.mapDomain_comp]
  rfl

omit [Field K] in

/--
@isnad1 id=eq.1h6v.s9.34a9a9f4d1d4 from=translated src=- shape=31aa03cd vocab=6f924309
-/
theorem specializePlace_intertwines (r : K → k) (σ : K → K) (τ : k → k)
    (h : ∀ a, r (σ a) = τ (r a)) (a : K) :
    specializePlace r (σ a) = charLGeomPlaceOfPoint k (τ (r a)) := by
  simp only [specializePlace, h]

end Galois

end ModularCurve

end
