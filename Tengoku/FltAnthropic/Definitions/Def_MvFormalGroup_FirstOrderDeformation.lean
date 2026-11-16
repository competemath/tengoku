import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_Deformation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

noncomputable section

namespace Tengoku.FltAnthropic.MvFormalGroup

variable {k : Type} [Field k] {d : ℕ}

@[reducible] def dualNumberResidueAlgebra (k : Type) [Field k] : Algebra (DualNumber k) k :=
  (TrivSqZeroExt.fstHom k k k).toRingHom.toAlgebra

attribute [local instance] dualNumberResidueAlgebra

def epsPart (G₀ : MvFormalGroup d k) (D : Deformation G₀ (DualNumber k)) :
    Fin d → MvPowerSeries (Fin d ⊕ Fin d) k :=
  fun i n => TrivSqZeroExt.snd (MvPowerSeries.coeff n (D.F.toPowerSeries i))

def firstOrderCocycles (G₀ : MvFormalGroup d k) : Submodule k (Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :=
  Submodule.span k (epsPart G₀ '' {D | D.F.IsComm})

def firstOrderCoboundaries (G₀ : MvFormalGroup d k) : Submodule k (Fin d → MvPowerSeries (Fin d ⊕ Fin d) k) :=
  Submodule.span k (epsPart G₀ ''
    {D | D.F.IsComm ∧ ∃ D' : Deformation G₀ (DualNumber k), D.IsIso D' ∧ epsPart G₀ D' = 0})

abbrev firstOrderDeformationSpace (G₀ : MvFormalGroup d k) : Type :=
  ↥(firstOrderCocycles G₀) ⧸ (firstOrderCoboundaries G₀).comap (firstOrderCocycles G₀).subtype

end Tengoku.FltAnthropic.MvFormalGroup

end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
