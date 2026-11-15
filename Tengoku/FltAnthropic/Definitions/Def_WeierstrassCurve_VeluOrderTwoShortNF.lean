import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_VeluOrderTwo

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace WeierstrassCurve

section KernelData

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsShortNF]

/--
@isnad1 id=eq.0h4v.s6.f1c49817f9a4 from=translated src=- shape=90de60f5 vocab=f47b39b6
-/
lemma veluGx_of_isShortNF (x y : R) : W.veluGx x y = 3 * x ^ 2 + W.a₄ := by
  simp only [veluGx, a₁_of_isShortNF, a₂_of_isShortNF]
  ring

/--
@isnad1 id=eq.0h3v.s5.63a3e23882c3 from=translated src=- shape=25a66d23 vocab=e1bbde44
-/
lemma veluGy_zero_of_isShortNF (x : R) : W.veluGy x 0 = 0 := by
  simp only [veluGy, a₁_of_isShortNF, a₃_of_isShortNF]
  ring

/--
@isnad1 id=eq.0h3v.s7.ab7ca9d2bb12 from=translated src=- shape=a0a6984f vocab=630cfc2c
-/
lemma velu2QuadDisc_of_isShortNF (x : R) :
    W.velu2QuadDisc x = -16 * (3 * x ^ 2 + 4 * W.a₄) := by
  simp only [velu2QuadDisc, b₂_of_isShortNF, b₄_of_isShortNF]
  ring

/--
@isnad1 id=iff.0h3v.s7.1ab13c5ddc7c from=translated src=- shape=1a27d62c vocab=1a763313
-/
lemma equation_zero_iff_of_isShortNF (e : R) :
    W.toAffine.Equation e 0 ↔ e ^ 3 + W.a₄ * e + W.a₆ = 0 := by
  rw [Affine.equation_iff]
  constructor <;> intro h <;>
    linear_combination -h - e ^ 2 * a₂_of_isShortNF W

/--
@isnad1 id=isshortn.0h3v.s5.ff312d41717a from=translated src=- shape=ed83edae vocab=a4a3cfec
-/
instance instIsShortNFMk (a b : R) : (WeierstrassCurve.mk 0 0 0 a b).IsShortNF :=
  ⟨rfl, rfl, rfl⟩

end KernelData

section ShortQuotient

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R) [W.IsShortNF]

/--
@isnad1 id=isshortn.0h4v.s4.6788e2bf9a87 from=translated src=- shape=2c81cb6f vocab=38a1e37a
-/
instance veluQuotient2_isShortNF (x₀ y₀ : R) : (W.veluQuotient2 x₀ y₀).IsShortNF where
  a₁ := a₁_of_isShortNF W
  a₂ := a₂_of_isShortNF W
  a₃ := a₃_of_isShortNF W

/--
@isnad1 id=eq.0h3v.s7.87010b9eb3d3 from=translated src=- shape=0434e3d6 vocab=22a3dbd6
-/
lemma veluQuotient2_a₄_of_isShortNF (e : R) :
    (W.veluQuotient2 e 0).a₄ = -(15 * e ^ 2 + 4 * W.a₄) := by
  rw [veluQuotient2_a₄, veluGx_of_isShortNF]
  ring

/--
@isnad1 id=eq.0h3v.s7.5a5fa3ff87c2 from=translated src=- shape=ea7e7222 vocab=256a51da
-/
lemma veluQuotient2_a₆_of_isShortNF (e : R) :
    (W.veluQuotient2 e 0).a₆ = W.a₆ - 21 * e ^ 3 - 7 * W.a₄ * e := by
  rw [veluQuotient2_a₆, veluGx_of_isShortNF, b₂_of_isShortNF]
  ring

/--
@isnad1 id=eq.0h3v.s8.e2bbc26b8864 from=translated src=- shape=a414f182 vocab=13d0c087
-/
theorem veluQuotient2_eq_of_isShortNF (e : R) :
    W.veluQuotient2 e 0
      = ⟨0, 0, 0, -(15 * e ^ 2 + 4 * W.a₄), W.a₆ - 21 * e ^ 3 - 7 * W.a₄ * e⟩ := by
  ext
  · exact a₁_of_isShortNF W
  · exact a₂_of_isShortNF W
  · exact a₃_of_isShortNF W
  · exact veluQuotient2_a₄_of_isShortNF W e
  · exact veluQuotient2_a₆_of_isShortNF W e

end ShortQuotient

end WeierstrassCurve
