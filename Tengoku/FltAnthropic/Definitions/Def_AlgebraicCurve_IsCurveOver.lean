import Tengoku.FltAnthropic.Definitions.Def_AlgebraicCurve_DivisorClassGroup
import Tengoku.Seed.RingTheory.Kaehler.Basic
import Tengoku.Seed.FieldTheory.IsAlgClosed.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]

class IsCurveOver : Prop extends HasPrincipalDivisors K F where

  finiteResidue : ∀ v : Place K F, Module.Finite K v.ResidueField

  kaehler_free_rank_one : Module.Free F Ω[F⁄K] ∧ Module.finrank F Ω[F⁄K] = 1

namespace IsCurveOver

variable {K F}

end IsCurveOver

namespace Place

variable {K F}

end Place

namespace IsCurveOver

variable {K F}

end IsCurveOver

end AlgebraicCurve
