import Tengoku.FltAnthropic.Definitions.Def_NumberField_AdelicBox
import Tengoku.Seed.Analysis.SpecificLimits.Basic
import Tengoku.Seed.Analysis.Complex.Basic
import Tengoku.Seed.Topology.Compactness.Compact
import Tengoku.Seed.MeasureTheory.Group.Measure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_AdelicBox_exists_eq_sum_indicator_image_integralFiniteAdeles

set_option autoImplicit false

open NumberField NumberField.AdelicBox IsDedekindDomain
open scoped nonZeroDivisors

namespace LatKer0

open IsDedekindDomain Filter Topology

variable (F : Type) [Field F] [NumberField F]

private def _root_.LatKer0.dBox (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
    integralFiniteAdeles (𝓞 F) F

export _root_.LatKer0 (dBox)

end LatKer0

namespace LatIdx

open IsDedekindDomain MeasureTheory

variable (F : Type) [Field F] [NumberField F]

def dBox (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) ''
    integralFiniteAdeles (𝓞 F) F

/--
@isnad1 id=mem.2h3v.s8.82ca31d3b7fd from=translated src=- shape=e4d16b89 vocab=1eecb234
-/
theorem add_mem' {z w : FiniteAdeleRing (𝓞 F) F} (hz : z ∈ integralFiniteAdeles (𝓞 F) F)
    (hw : w ∈ integralFiniteAdeles (𝓞 F) F) : z + w ∈ integralFiniteAdeles (𝓞 F) F := fun v =>
  add_mem (hz v) (hw v)

variable {F}

end LatIdx

namespace LatDec

open IsDedekindDomain Filter Topology

variable {F : Type} [Field F] [NumberField F]

def coset (k : F) (d : 𝓞 F) : Set (FiniteAdeleRing (𝓞 F) F) :=
  (fun z : FiniteAdeleRing (𝓞 F) F ↦ algebraMap F (FiniteAdeleRing (𝓞 F) F) k
    + algebraMap F (FiniteAdeleRing (𝓞 F) F) (d : F) * z) '' integralFiniteAdeles (𝓞 F) F

end LatDec
