import Tengoku.Seed.NumberTheory.Modular
import Tengoku.Seed.NumberTheory.ModularForms.Petersson
import Tengoku.Seed.NumberTheory.ModularForms.CongruenceSubgroups
import Tengoku.Seed.Analysis.Complex.UpperHalfPlane.Measure
import Tengoku.Seed.MeasureTheory.Integral.Bochner.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open scoped MatrixGroups ModularForm

namespace CuspForm

def peterssonOnIntegrand (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ)
    (τ : UpperHalfPlane) : ℂ :=
  ∑ᶠ q : SL(2, ℤ) ⧸ Γ,
    UpperHalfPlane.petersson k (f ∣[k] (q.out⁻¹ : SL(2, ℤ))) (g ∣[k] (q.out⁻¹ : SL(2, ℤ))) τ

def peterssonOn (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) : ℂ :=
  MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
    (peterssonOnIntegrand Γ k f g)

/--
@isnad1 id=eq.0h4v.s6.948b454a27c8 from=translated src=- shape=19f943ec vocab=4fc0fa4c
-/
theorem peterssonOn_def (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : UpperHalfPlane → ℂ) :
    peterssonOn Γ k f g =
      MeasureTheory.integral (MeasureTheory.volume.restrict ModularGroup.fd)
        (peterssonOnIntegrand Γ k f g) := rfl

end CuspForm

end
