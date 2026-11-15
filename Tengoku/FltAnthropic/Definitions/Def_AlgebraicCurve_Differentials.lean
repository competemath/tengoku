import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.Seed.RingTheory.Kaehler.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable {K F : Type*} [Field K] [Field F] [Algebra K F]

namespace Place

variable (v : Place K F)

open Classical in

def uniformizer_alt : F :=
  if h : ∃ t : F, v.ord t = 1 then h.choose else 0

/--
@isnad1 id=eq.1h3v.s6.dd9b98a3a0b5 from=translated src=- shape=8932df0c vocab=b630f5b9
-/
theorem ord_uniformizer_alt (h : ∃ t : F, v.ord t = 1) : v.ord v.uniformizer_alt = 1 := by
  rw [uniformizer_alt, dite_eq_left h]
  exact h.choose_spec

open Classical in

def diffCoeff (t : F) (ω : Ω[F⁄K]) : F :=
  if h : ∃ g : F, ω = g • D K F t then h.choose else 0

/--
@isnad1 id=eq.1h4v.s9.54978bb794a0 from=translated src=- shape=4da14f62 vocab=88dcd3d4
-/
theorem diffCoeff_smul_D {t : F} {ω : Ω[F⁄K]} (h : ∃ g : F, ω = g • D K F t) :
    diffCoeff t ω • D K F t = ω := by
  rw [diffCoeff, dite_eq_left h]
  exact h.choose_spec.symm

/--
@isnad1 id=eq.1h4v.s8.137d3859de50 from=translated src=- shape=148738c2 vocab=88dcd3d4
-/
theorem diffCoeff_of_not_exists {t : F} {ω : Ω[F⁄K]} (h : ¬ ∃ g : F, ω = g • D K F t) :
    diffCoeff t ω = 0 := by
  rw [diffCoeff, dite_eq_right h]

def ordDiff (ω : Ω[F⁄K]) : ℤ :=
  v.ord (diffCoeff v.uniformizer_alt ω)

/--
@isnad1 id=eq.0h4v.s6.ec7c014cdb88 from=translated src=- shape=737a0629 vocab=fbbb1c09
-/
theorem ordDiff_def (ω : Ω[F⁄K]) : v.ordDiff ω = v.ord (diffCoeff v.uniformizer_alt ω) := rfl

end Place

variable (K F) in

def IsRegularDiff (ω : Ω[F⁄K]) : Prop :=
  ∀ v : Place K F, 0 ≤ v.ordDiff ω

/--
@isnad1 id=iff.0h3v.s6.7f0ee468b4ec from=translated src=- shape=20ad1046 vocab=80bb3151
-/
theorem isRegularDiff_iff (ω : Ω[F⁄K]) :
    IsRegularDiff K F ω ↔ ∀ v : Place K F, 0 ≤ v.ordDiff ω := Iff.rfl

variable (K F) in

def regularDiffs : Submodule K Ω[F⁄K] :=
  Submodule.span K {ω : Ω[F⁄K] | IsRegularDiff K F ω}

/--
@isnad1 id=mem.1h3v.s7.b0ce3e30ca26 from=translated src=- shape=f1125409 vocab=ceaedd62
-/
theorem mem_regularDiffs_of_isRegularDiff {ω : Ω[F⁄K]} (h : IsRegularDiff K F ω) :
    ω ∈ regularDiffs K F :=
  Submodule.subset_span h

/--
@isnad1 id=eq.0h2v.s7.97581bddee03 from=translated src=- shape=e00a1c9e vocab=bf01decf
-/
theorem regularDiffs_eq_span :
    regularDiffs K F = Submodule.span K {ω : Ω[F⁄K] | IsRegularDiff K F ω} := rfl

section Pullback

variable {F' : Type*} [Field F'] [Algebra K F']

def pullbackDiff (φ : F →ₐ[K] F') : Ω[F⁄K] →ₗ[K] Ω[F'⁄K] :=
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  (KaehlerDifferential.map K K F F').restrictScalars K

/--
@isnad1 id=eq.0h5v.s9.46213ef5e38c from=translated src=- shape=9278e69d vocab=e9098942
-/
theorem pullbackDiff_D (φ : F →ₐ[K] F') (x : F) :
    pullbackDiff φ (D K F x) = D K F' (φ x) := by
  letI : Algebra F F' := φ.toRingHom.toAlgebra
  haveI : IsScalarTower K F F' := IsScalarTower.of_algebraMap_eq fun k => (φ.commutes k).symm
  exact KaehlerDifferential.map_D K K F F' x

end Pullback

end AlgebraicCurve

end
