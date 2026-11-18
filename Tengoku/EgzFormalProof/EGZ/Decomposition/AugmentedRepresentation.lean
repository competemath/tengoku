import Tengoku.EgzFormalProof.EGZ.Decomposition.AugmentedDiagram
import Tengoku.EgzFormalProof.EGZ.Decomposition.SupportDiagramRepresentation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The represented augmented support flag

After choosing integer lattice charts with injective reductions modulo `p`,
the augmented support diagram admits a representation on the old cumulative
support spans. Its maps are the modular chart inverses of the augmented maps.
-/

namespace EGZ.FlagDecomposition.Augmented

variable {p d : ℕ} [NeZero p] [Fact p.Prime] {f : FpCoord p d → ℕ}
    (Φ : FlagDecomposition p d f) (e : Φ.flag.Node → ℕ)
    (ξ : ℕ → FpCoord p d →ᵃ[ZMod p] ZMod p) (hp : Odd p) (he : Antitone e)
    (C : ∀ x, IntegerLatticeChart (support Φ e ξ x))
    (hmod : ∀ x, Function.Injective ((IntegralAffineMap.ofIntAffineMap (C x).map).modp p))

/-- A surjective representation of the charted augmented flag.-/
noncomputable abbrev representation :
    FpRepresentation p d ((diagram Φ e ξ hp he).chartedFlag C) :=
  (diagram Φ e ξ hp he).chartedRepresentation C Φ.localWeight (map Φ e ξ) hmod
    (fun x ↦ (support_mod Φ e ξ x).symm)
    (fun {x _} h {v} hv ↦ map_compatible Φ e ξ he h
      (Φ.originalWeights.cumulative_supported x v hv))

/--
@isnad1 id=eq.3h8v.s10.a28bae76dc2c from=translated src=- shape=768b92c8 vocab=6b5e3fda
-/
@[simp]
theorem representation_map (x : Φ.flag.Node) :
    (representation Φ e ξ hp he C hmod).map x = (C x).rechartMap (map Φ e ξ x) := rfl

/--
@isnad1 id=eq.3h8v.s10.f57ea51c1ab1 from=translated src=- shape=caf42d97 vocab=169c4c70
-/
@[simp]
theorem representation_space (x : Φ.flag.Node) :
    (representation Φ e ξ hp he C hmod).space x =
      affineSpan (ZMod p) {v | Φ.cumulativeWeight x v ≠ 0} := rfl

/--
@isnad1 id=mem.4h9v.s10.9e38897412bc from=translated src=- shape=f292cf1c vocab=3d30889f
-/
theorem local_supported (x : Φ.flag.Node) (v : FpCoord p d) (hv : Φ.localWeight x v ≠ 0) :
    v ∈ (representation Φ e ξ hp he C hmod).space x :=
  FpRepresentation.local_supported_cumulativeSpace Φ.localWeight x v hv

end EGZ.FlagDecomposition.Augmented
