import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.ResidualAction
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Comparison.StructuredProductF0

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The residual action as an automorphism of the accepted rational Albert algebra

The structured source coordinates are identified with the accepted `F0`
coordinates by the independently proved comparison equivalence.  Conjugating
the source action by that equivalence gives a rational linear equivalence of
the literal 27-coordinate algebra.  The comparison theorem and the source
product-invariance theorem prove that it preserves the frozen product.
-/

noncomputable section

namespace AlbertLean.Generic.ResidualAction

open AlbertLean
open AlbertLean.Residual.SL4PairAction
open AlbertLean.Triality.CoordinateTensor
open AlbertLean.Triality.StructuredCubic
open AlbertLean.Triality.StructuredProduct
open AlbertLean.Comparison.StructuredF0
open AlbertLean.Comparison.StructuredProductF0

/-- Conjugation of the structured residual action into the accepted rational
27-coordinate presentation.-/
def f0LinearEquiv (G : DetOneMatrix ℚ) : Coord ≃ₗ[ℚ] Coord :=
  structuredEquiv.symm.trans ((linearEquiv G).trans structuredEquiv)

/--
@isnad1 id=eq.0h2v.s9.6b0c2805bc56 from=translated src=- shape=c7dae064 vocab=f9ffab46
-/
@[simp] theorem f0LinearEquiv_apply (G : DetOneMatrix ℚ) (x : Coord) :
    f0LinearEquiv G x = structuredEquiv (act G (structuredEquiv.symm x)) := rfl

/-- The conjugated action fixes the accepted F0 unit.
@isnad1 id=eq.0h1v.s7.d808340e3117 from=translated src=- shape=a6301b0c vocab=6ce5cfc1
-/
theorem f0LinearEquiv_one (G : DetOneMatrix ℚ) :
    f0LinearEquiv G AlbertLean.one = AlbertLean.one := by
  have hsource : structuredEquiv.symm AlbertLean.one =
      (sourceOne : JCoord ℚ) := by
    apply structuredEquiv.injective
    rw [LinearEquiv.apply_symm_apply, structuredEquiv_sourceOne]
  rw [f0LinearEquiv_apply, hsource, sourceOne_act, structuredEquiv_sourceOne]

/-- The conjugated action preserves the literal accepted F0 product.
@isnad1 id=eq.0h3v.s9.1115c2cfb2a9 from=translated src=- shape=8f1a1e2e vocab=4bbcf9a1
-/
theorem f0LinearEquiv_product (G : DetOneMatrix ℚ) (x y : Coord) :
    f0LinearEquiv G (AlbertLean.structuredProduct x y) =
      AlbertLean.structuredProduct (f0LinearEquiv G x) (f0LinearEquiv G y) := by
  obtain ⟨u, rfl⟩ := structuredEquiv.surjective x
  obtain ⟨v, rfl⟩ := structuredEquiv.surjective y
  have huv := StructuredSourceProductAgreesWithF0 u v
  change structuredEquiv (sourceProduct u v) =
    AlbertLean.structuredProduct (structuredEquiv u) (structuredEquiv v) at huv
  calc
    f0LinearEquiv G
        (AlbertLean.structuredProduct (structuredEquiv u) (structuredEquiv v)) =
        structuredEquiv (act G (sourceProduct u v)) := by
          rw [← huv, f0LinearEquiv_apply, LinearEquiv.symm_apply_apply]
    _ = structuredEquiv (sourceProduct (act G u) (act G v)) := by
          rw [sourceProduct_act]
    _ = AlbertLean.structuredProduct
          (structuredEquiv (act G u)) (structuredEquiv (act G v)) := by
          exact StructuredSourceProductAgreesWithF0 (act G u) (act G v)
    _ = AlbertLean.structuredProduct
          (f0LinearEquiv G (structuredEquiv u))
          (f0LinearEquiv G (structuredEquiv v)) := by
          rw [f0LinearEquiv_apply, f0LinearEquiv_apply,
            LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply]

/-- The actual rational-linear unital Albert automorphism associated to a
determinant-one residual matrix.-/
def jordanAut (G : DetOneMatrix ℚ) : AlbertLean.JordanAut where
  toLinearEquiv := f0LinearEquiv G
  map_one := f0LinearEquiv_one G
  map_circle := f0LinearEquiv_product G

/-- Conjugation retains the residual multiplication law.
@isnad1 id=eq.0h2v.s7.3b79b9a9d6c5 from=translated src=- shape=689f2358 vocab=b1f60b37
-/
theorem f0LinearEquiv_compose (G H : DetOneMatrix ℚ) :
    f0LinearEquiv (compose G H) =
      (f0LinearEquiv H).trans (f0LinearEquiv G) := by
  apply LinearEquiv.ext
  intro x
  change structuredEquiv (act (compose G H) (structuredEquiv.symm x)) =
    structuredEquiv
      (act G (structuredEquiv.symm
        (structuredEquiv (act H (structuredEquiv.symm x)))))
  rw [act_compose, LinearEquiv.symm_apply_apply]

/-- Pointwise homomorphism law for the resulting Albert automorphisms.
@isnad1 id=eq.0h3v.s9.352ac1be38a2 from=translated src=- shape=d06f609c vocab=6662582d
-/
theorem jordanAut_compose_apply (G H : DetOneMatrix ℚ) (x : Coord) :
    jordanAut (compose G H) x = jordanAut G (jordanAut H x) := by
  change f0LinearEquiv (compose G H) x =
    f0LinearEquiv G (f0LinearEquiv H x)
  have h := congrArg (fun e : Coord ≃ₗ[ℚ] Coord => e x)
    (f0LinearEquiv_compose G H)
  exact h

end AlbertLean.Generic.ResidualAction
