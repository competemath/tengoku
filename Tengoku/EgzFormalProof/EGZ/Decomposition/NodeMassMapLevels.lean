import Tengoku.EgzFormalProof.EGZ.Decomposition.NodeMassMap
import Tengoku.EgzFormalProof.EGZ.Decomposition.LevelInjectivity

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Level comparison for mass-transport maps

For a minimal output decomposition, compatibility on cumulative support
extends to its whole represented affine space. Thus a node mass map already
contains all data needed for level monotonicity and equal-level coordinate
injectivity; no extra transport fields are required.
-/

namespace EGZ.FlagDecomposition.NodeMassMap

variable {p d : ℕ} [Fact p.Prime] {f : FpCoord p d → ℕ}
    {Φ Ψ : FlagDecomposition p d f} {x : Φ.flag.Node} {y : Ψ.flag.Node}
    (M : NodeMassMap Φ Ψ x y) (hΨ : Ψ.IsMinimal)

include M hΨ

/--
@isnad1 id=le.1h8v.s8.4ce1a1d5f6c0 from=translated src=- shape=70bc02fa vocab=c4d74635
-/
theorem space_le : Ψ.representation.space y ≤ Φ.representation.space x := by
  rw [(hΨ y).1]
  apply affineSpan_le.mpr
  intro v hv
  exact Φ.originalWeights.cumulative_supported x v
    (ne_of_gt ((Nat.pos_of_ne_zero hv).trans_le (M.cumulative_le v)))

/-- Compatibility extends from the support to its full affine span.
@isnad1 id=eq.2h9v.s10.a0b1ce706e4c from=translated src=- shape=547ec899 vocab=64f25d9e
-/
theorem map_eq_on_space (v : FpCoord p d) (hv : v ∈ Ψ.representation.space y) :
    M.coord.modp p (Ψ.representation.map y v) = Φ.representation.map x v := by
  rw [(hΨ y).1] at hv
  exact AffineMap.eqOn_affineSpan
    (f := (M.coord.modp p).comp (Ψ.representation.map y))
    (g := Φ.representation.map x) M.map_eq hv

/--
@isnad1 id=le.1h8v.s6.c08fa4299bf4 from=translated src=- shape=00e9590c vocab=7f6ea381
-/
theorem level_le : Φ.level x ≤ Ψ.level y :=
  Φ.representation.level_le_of_space_le_of_factor Ψ.representation x y (M.coord.modp p)
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm)

/--
@isnad1 id=eq.2h8v.s7.8db683e1e6c9 from=translated src=- shape=b9a57809 vocab=83878d8f
-/
theorem space_eq_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Ψ.representation.space y = Φ.representation.space x :=
  Φ.representation.space_eq_of_codimension_eq_of_le Ψ.representation x y (M.space_le hΨ)
    (Φ.representation.codimension_eq_and_rank_eq_of_level_eq Ψ.representation x y hlevel).1

/--
@isnad1 id=injectiv.2h8v.s9.0e2806161e9b from=translated src=- shape=89c2b5ff vocab=b7452737
-/
theorem modp_injective_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Function.Injective (M.coord.modp p) :=
  Φ.representation.factor_modp_injective_of_level_eq Ψ.representation x y (M.coord.modp p)
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm) hlevel

/--
@isnad1 id=injectiv.2h8v.s9.db137b1e5ec9 from=translated src=- shape=1ba8c855 vocab=9c39d165
-/
theorem real_injective_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Function.Injective M.coord.real :=
  Φ.representation.factor_real_injective_of_level_eq Ψ.representation x y M.coord
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm) hlevel

/--
@isnad1 id=injectiv.2h8v.s6.c0ed34241d93 from=translated src=- shape=ca8ad946 vocab=2d982881
-/
theorem integer_injective_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Function.Injective M.coord.integer :=
  Φ.representation.factor_integer_injective_of_level_eq Ψ.representation x y M.coord
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm) hlevel

/--
@isnad1 id=bijectiv.2h8v.s9.51bb0a872fe1 from=translated src=- shape=1ba8c855 vocab=5cca438d
-/
theorem real_bijective_of_level_eq (hlevel : Φ.level x = Ψ.level y) :
    Function.Bijective M.coord.real :=
  Φ.representation.factor_real_bijective_of_level_eq Ψ.representation x y M.coord
    (M.space_le hΨ) (fun v hv ↦ (M.map_eq_on_space hΨ v hv).symm) hlevel

end EGZ.FlagDecomposition.NodeMassMap
