import Tengoku.FltAnthropic.Definitions.Def_MvFormalGroup_BasicV2

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

noncomputable section

namespace Tengoku.FltAnthropic.MvFormalGroup

@[ext]
structure Deformation {S : Type} [CommRing S] {d : ℕ} (G₀ : MvFormalGroup d S)
    (B : Type) [CommRing B] [Algebra B S] : Type where

  F : MvFormalGroup d B

  map_eq : F.map (algebraMap B S) = G₀

namespace Deformation

variable {S : Type} [CommRing S] {d : ℕ} {G₀ : MvFormalGroup d S} {B : Type} [CommRing B] [Algebra B S]

def IsIso (D D' : Deformation G₀ B) : Prop :=
  ∃ φ : MvFormalGroup.Hom D.F D'.F,
    (∃ ψ : MvFormalGroup.Hom D'.F D.F, ψ.comp φ = MvFormalGroup.Hom.id D.F ∧ φ.comp ψ = MvFormalGroup.Hom.id D'.F) ∧
    ∀ i : Fin d, MvPowerSeries.map (algebraMap B S) (φ.toPowerSeries i) = MvPowerSeries.X i

def refl (G₀ : MvFormalGroup d S) : Deformation G₀ S where
  F := G₀
  map_eq := by
    ext i n
    simp [MvFormalGroup.map, Algebra.algebraMap_self]

end Deformation

end Tengoku.FltAnthropic.MvFormalGroup

end
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
