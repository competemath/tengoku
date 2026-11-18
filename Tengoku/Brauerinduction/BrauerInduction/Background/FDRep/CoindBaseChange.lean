import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Induced
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.CoindBasic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!

# Base change for coinduction along quotient maps

Let `K` be a normal subgroup of `G`, let `π : G → G ⧸ K` be the quotient map,
and let `Q ≤ G ⧸ K`. Writing `H = π⁻¹ Q`, this file proves that pulling back
a coinduced representation along `π` agrees with coinducing the pulled-back
representation from `H` to `G`.

The main result is

* `FDRep.CoindBaseChange.comap_coind_quotient_iso`:
  `comap π (coind Q σ) ≅ coind H (comap (H → Q) σ)`.
-/

universe u v

variable {k : Type u} [Field k]
variable {G : Type u} [Group G]

namespace FDRep

namespace CoindBaseChange

/-- The quotient map `G → G ⧸ K`.-/
abbrev quotientMap (K : Subgroup G) [K.Normal] : G →* G ⧸ K :=
  QuotientGroup.mk' K

/-- The inverse image in `G` of a subgroup of `G ⧸ K`.-/
abbrev quotientPreimage
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K)) : Subgroup G :=
  Q.comap (quotientMap K)

/--
The restricted quotient map `π⁻¹(Q) → Q`.-/
abbrev quotientPreimageMap
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K)) :
    quotientPreimage K Q →* Q :=
  ((quotientMap K).comp (quotientPreimage K Q).subtype).codRestrict
    Q
    (fun x => x.2)

private noncomputable def comapCoindToCoindComap
    [Finite G]
    (K : Subgroup G) [K.Normal]
    (Q : Subgroup (G ⧸ K))
    (σ : FDRep k Q) :
    (FDRep.comap (quotientMap K) (FDRep.coind Q σ)) →ₗ[k]
      (FDRep.coind (quotientPreimage K Q)
        (FDRep.comap (quotientPreimageMap K Q) σ)) where
  toFun v :=
    { val := fun x => v.val ((quotientMap K) x)
      property := by
        intro h x
        change
          v.val ((quotientMap K) ((h : G) * x))
            =
          σ.ρ ((quotientPreimageMap K Q) h)
            (v.val ((quotientMap K) x))
        exact v.property (quotientPreimageMap K Q h) (quotientMap K x)
  }
  map_add' := by
    intro v w
    apply FDRep.coind_ext_val
      (I := quotientPreimage K Q)
      (σ := FDRep.comap (quotientPreimageMap K Q) σ)
    intro x
    rfl
  map_smul' := by
    intro c v
    apply FDRep.coind_ext_val
      (I := quotientPreimage K Q)
      (σ := FDRep.comap (quotientPreimageMap K Q) σ)
    intro x
    rfl

end CoindBaseChange
end FDRep
