import Tengoku.MobiusCpt.MobiusCPT.Wightman.Mobius
import Tengoku.MobiusCpt.MobiusCPT.Wightman.StrongTopology

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MobiusCPT

open scoped Topology

/-!
# The Wightman covariance axiom

[T26], Definition 2.5: this module defines the two parts of Möbius covariance
in (W1), their immediate continuity consequences, and the bundled predicate
`IsWightmanCFT` for regularity together with (W1)--(W4). Locality (W2) lives on
`WightmanStruct` in `MobiusCPT.Wightman.Basic` because it needs only `smear`.
-/

variable {G TF 𝓓 𝓕 : Type*}
variable [Group G]
variable [AddCommGroup TF] [Module ℂ TF] [TopologicalSpace TF]
variable [TestFunctions TF] [MobiusAction G TF]
variable [AddCommGroup 𝓓] [Module ℂ 𝓓]

namespace WightmanData

/-- [T26], Definition 2.5(3): the `𝓕`-strong topology of the underlying
`WightmanStruct`, exposed so downstream continuity statements can name it.-/
abbrev strongTop (W : WightmanData G TF 𝓓 𝓕) : TopologicalSpace 𝓓 :=
  W.toWightmanStruct.fStrongTopology

/-- [T26], Definition 2.5(3) and (W1): Möbius covariance.  The first
conjunct says that `U` takes values in the `𝓕`-strong continuous endomorphisms;
the second is (W1) proper.-/
def W1 (W : WightmanData G TF 𝓓 𝓕) : Prop :=
  (∀ γ : G, Continuous[strongTop W, strongTop W] (W.U γ)) ∧
    (∀ φ : 𝓕, W.IsCovariant φ (W.dim φ))

/-- [T26], Definition 2.5(3): the representation `U` is strong-continuous
when `W1` holds.
@isnad1 id=continuo.1h6v.s7.0bda278fba23 from=translated src=- shape=7afe45ec vocab=aeef2a73
-/
theorem W1.continuous (W : WightmanData G TF 𝓓 𝓕) (h : W.W1) (γ : G) :
    Continuous[strongTop W, strongTop W] (W.U γ) := by
  exact h.1 γ

/-- [T26], Definition 2.5 (W1): every field is Möbius-covariant at its supplied
conformal dimension when `W1` holds.
@isnad1 id=iscovari.1h6v.s6.832c4597bf10 from=translated src=- shape=9a1d4f5a vocab=74125a62
-/
theorem W1.covariant (W : WightmanData G TF 𝓓 𝓕) (h : W.W1) :
    ∀ φ : 𝓕, W.IsCovariant φ (W.dim φ) := by
  exact h.2

/-- [T26], Definition 3.1 and Definition 2.5(3): every boost is strongly
continuous when `W1` holds.
@isnad1 id=continuo.1h6v.s7.04947f95ad59 from=translated src=- shape=e1ea6906 vocab=8f3eb245
-/
theorem w1_continuous_boost (W : WightmanData G TF 𝓓 𝓕) (h : W.W1) (t : ℝ) :
    Continuous[strongTop W, strongTop W] (W.boost t) := by
  change Continuous[strongTop W, strongTop W]
    (W.U (MobiusAction.boostElt (G := G) (TF := TF) t))
  exact W1.continuous W h _

/-- [T26], Definition 2.5: a Möbius-covariant Wightman CFT — the regular action of `𝓕`
together with (W1)–(W4). Definition 2.5(3)'s `𝓕`-strong continuity of `U` is the first
conjunct of `W1`, and Definition 2.5(4)'s `Ω ≠ 0` is already the `vac_ne_zero` field of
`WightmanData`, so neither is repeated here.-/
def IsWightmanCFT (W : WightmanData G TF 𝓓 𝓕) : Prop :=
  W.toWightmanStruct.ActsRegularly ∧ W.W1 ∧ W.toWightmanStruct.W2 ∧ W.W3 ∧ W.W4

/-- [T26], Definition 2.5: a Wightman CFT acts regularly.
@isnad1 id=actsregu.1h5v.s6.d30e3586d8f5 from=translated src=- shape=65d62c27 vocab=6464d8b5
-/
theorem IsWightmanCFT.actsRegularly (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.toWightmanStruct.ActsRegularly :=
  h.1

/-- [T26], Definition 2.5: a Wightman CFT satisfies (W1).
@isnad1 id=w1.1h5v.s6.2f7ae38fd7af from=translated src=- shape=cbe0e3da vocab=fed5dff6
-/
theorem IsWightmanCFT.w1 (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.W1 :=
  h.2.1

/-- [T26], Definition 2.5: a Wightman CFT satisfies (W2).
@isnad1 id=w2.1h5v.s6.2dd25f5c342e from=translated src=- shape=65d62c27 vocab=b540e2ec
-/
theorem IsWightmanCFT.w2 (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.toWightmanStruct.W2 :=
  h.2.2.1

/-- [T26], Definition 2.5: a Wightman CFT satisfies (W3).
@isnad1 id=w3.1h5v.s6.9f3903bf8e89 from=translated src=- shape=cbe0e3da vocab=f9f35218
-/
theorem IsWightmanCFT.w3 (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.W3 :=
  h.2.2.2.1

/-- [T26], Definition 2.5: a Wightman CFT satisfies (W4).
@isnad1 id=w4.1h5v.s6.f16b05bd4a1e from=translated src=- shape=cbe0e3da vocab=9574e271
-/
theorem IsWightmanCFT.w4 (W : WightmanData G TF 𝓓 𝓕)
    (h : W.IsWightmanCFT) : W.W4 :=
  h.2.2.2.2

end WightmanData

end MobiusCPT
