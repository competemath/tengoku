import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

open KaehlerDifferential

noncomputable section

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

namespace Place

variable {K F}
variable (v : Place K F)

private def uniformizer : F :=
  ((IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose : F)

private theorem ord_uniformizer : v.ord v.uniformizer = 1 := by
  have hirr := (IsDiscreteValuationRing.exists_irreducible v.toValuationSubring).choose_spec
  simpa [uniformizer] using v.ord_coe_irreducible hirr

private theorem uniformizer_ne_zero : v.uniformizer ≠ 0 := by
  intro h
  simpa [h, v.ord_zero] using v.ord_uniformizer

def dCoord : Ω[F⁄K] := KaehlerDifferential.D K F v.uniformizer

class DCoordGenerates : Prop where
  span_eq_top : Submodule.span F {v.dCoord} = ⊤

/--
@isnad1 id=ne.0h3v.s7.84f0f476a49a from=translated src=- shape=81a12065 vocab=de466259
-/
theorem dCoord_ne_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] : v.dCoord ≠ 0 := by
  intro h0
  have htop := DCoordGenerates.span_eq_top (v := v)
  obtain ⟨x, hx⟩ := exists_ne (0 : Ω[F⁄K])
  have hx_mem : x ∈ Submodule.span F {v.dCoord} := htop ▸ Submodule.mem_top
  rw [h0, Submodule.span_zero_singleton] at hx_mem
  exact hx hx_mem

def differentialCoeff (ω : Ω[F⁄K]) : F :=
  letI := Classical.propDecidable
  if h : ∃ f : F, ω = f • v.dCoord then h.choose else 0

/--
@isnad1 id=ex.0h4v.s7.bd0227178309 from=translated src=- shape=5b7ae686 vocab=1180179c
-/
theorem exists_eq_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    ∃ f : F, ω = f • v.dCoord := by
  have hω : ω ∈ (⊤ : Submodule F Ω[F⁄K]) := Submodule.mem_top
  rw [← DCoordGenerates.span_eq_top (v := v), Submodule.mem_span_singleton] at hω
  exact hω.imp fun _ hf => hf.symm

/--
@isnad1 id=eq.0h4v.s7.e9cfbb44ee96 from=translated src=- shape=90d43431 vocab=ed455aeb
-/
theorem differentialCoeff_smul_dCoord [v.DCoordGenerates] (ω : Ω[F⁄K]) :
    v.differentialCoeff ω • v.dCoord = ω := by
  rw [differentialCoeff, dite_eq_left (v.exists_eq_smul_dCoord ω)]
  exact (v.exists_eq_smul_dCoord ω).choose_spec.symm

/--
@isnad1 id=eq.1h5v.s7.1f03fe492c22 from=translated src=- shape=c1989705 vocab=e5b7a7f3
-/
theorem differentialCoeff_unique [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {ω : Ω[F⁄K]} {f : F} (hf : ω = f • v.dCoord) : v.differentialCoeff ω = f := by
  have key : (v.differentialCoeff ω - f) • v.dCoord = 0 := by
    rw [sub_smul, v.differentialCoeff_smul_dCoord ω, hf, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h v.dCoord_ne_zero

/--
@isnad1 id=eq.0h3v.s6.09e84289318e from=translated src=- shape=756474bd vocab=535214e2
-/
@[simp]
theorem differentialCoeff_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff v.dCoord = 1 :=
  v.differentialCoeff_unique (one_smul F v.dCoord).symm

/--
@isnad1 id=eq.0h3v.s7.c071ebb4d281 from=translated src=- shape=e6ce97d7 vocab=0d95c735
-/
@[simp]
theorem differentialCoeff_zero [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.differentialCoeff (0 : Ω[F⁄K]) = 0 :=
  v.differentialCoeff_unique (zero_smul F v.dCoord).symm

/--
@isnad1 id=eq.0h5v.s7.8eb50ffe8b2a from=translated src=- shape=acf4ab4d vocab=975c9fc7
-/
theorem differentialCoeff_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    (c : F) (ω : Ω[F⁄K]) :
    v.differentialCoeff (c • ω) = c * v.differentialCoeff ω :=
  v.differentialCoeff_unique
    (by rw [mul_smul, v.differentialCoeff_smul_dCoord])

def ordDifferential (ω : Ω[F⁄K]) : ℤ := v.ord (v.differentialCoeff ω)

/--
@isnad1 id=eq.0h3v.s6.8f64d99de2a1 from=translated src=- shape=a7fadcf5 vocab=3f627bad
-/
theorem gate_ordDifferential_dCoord [v.DCoordGenerates] [Nontrivial Ω[F⁄K]] :
    v.ordDifferential v.dCoord = 0 := by
  rw [ordDifferential, v.differentialCoeff_dCoord, v.ord_one]

/--
@isnad1 id=eq.2h5v.s7.1a720f083697 from=translated src=- shape=bac3ad9d vocab=6a6ae66e
-/
theorem ordDifferential_smul [v.DCoordGenerates] [Nontrivial Ω[F⁄K]]
    {c : F} (hc : c ≠ 0) {ω : Ω[F⁄K]} (hω : v.differentialCoeff ω ≠ 0) :
    v.ordDifferential (c • ω) = v.ord c + v.ordDifferential ω := by
  rw [ordDifferential, ordDifferential, v.differentialCoeff_smul, v.ord_mul hc hω]

end Place

end AlgebraicCurve

end
