import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_WeierstrassCurve_Velu

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace WeierstrassCurve

section CommRing

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

def veluQuotient2 (x₀ y₀ : R) : WeierstrassCurve R where
  a₁ := W.a₁
  a₂ := W.a₂
  a₃ := W.a₃
  a₄ := W.a₄ - 5 * W.veluGx x₀ y₀
  a₆ := W.a₆ - W.b₂ * W.veluGx x₀ y₀ - 7 * (x₀ * W.veluGx x₀ y₀)

variable (x₀ y₀ : R)

/--
@isnad1 id=eq.0h4v.s4.9b7675f6f359 from=translated src=- shape=f718534b vocab=7c1d1824
-/
@[simp] lemma veluQuotient2_a₁ : (W.veluQuotient2 x₀ y₀).a₁ = W.a₁ := rfl
/--
@isnad1 id=eq.0h4v.s4.4a28e86374d0 from=translated src=- shape=f718534b vocab=c2ee7b06
-/
@[simp] lemma veluQuotient2_a₂ : (W.veluQuotient2 x₀ y₀).a₂ = W.a₂ := rfl
/--
@isnad1 id=eq.0h4v.s4.c078c6b9fcab from=translated src=- shape=f718534b vocab=bd72e641
-/
@[simp] lemma veluQuotient2_a₃ : (W.veluQuotient2 x₀ y₀).a₃ = W.a₃ := rfl
/--
@isnad1 id=eq.0h4v.s6.211e083d46cb from=translated src=- shape=afb2baaf vocab=432e71a1
-/
lemma veluQuotient2_a₄ : (W.veluQuotient2 x₀ y₀).a₄ = W.a₄ - 5 * W.veluGx x₀ y₀ := rfl
/--
@isnad1 id=eq.0h4v.s7.73077e64fa55 from=translated src=- shape=036e6789 vocab=12e07af9
-/
lemma veluQuotient2_a₆ :
    (W.veluQuotient2 x₀ y₀).a₆ = W.a₆ - W.b₂ * W.veluGx x₀ y₀ - 7 * (x₀ * W.veluGx x₀ y₀) :=
  rfl

/--
@isnad1 id=eq.0h4v.s4.447de45003e6 from=translated src=- shape=f718534b vocab=7c9f45ef
-/
lemma veluQuotient2_b₂ : (W.veluQuotient2 x₀ y₀).b₂ = W.b₂ := by
  simp [b₂]

def velu2QuadDisc (x₀ : R) : R :=
  W.b₂ ^ 2 - 8 * W.b₂ * x₀ - 48 * x₀ ^ 2 - 32 * W.b₄

/--
@isnad1 id=eq.0h3v.s7.75e366c01773 from=translated src=- shape=b976a852 vocab=0d7171d4
-/
lemma velu2QuadDisc_def (x₀ : R) :
    W.velu2QuadDisc x₀ = W.b₂ ^ 2 - 8 * W.b₂ * x₀ - 48 * x₀ ^ 2 - 32 * W.b₄ := rfl

/--
@isnad1 id=eq.0h3v.s8.eee57933e413 from=translated src=- shape=dd54eaa5 vocab=dd183d6d
-/
lemma velu2QuadDisc_eq_disc_cofactor (x₀ : R) :
    W.velu2QuadDisc x₀
      = (W.b₂ + 4 * x₀) ^ 2 - 16 * (4 * x₀ ^ 2 + W.b₂ * x₀ + 2 * W.b₄) := by
  simp only [velu2QuadDisc]; ring

/--
@isnad1 id=eq.0h5v.s7.7d155b71bc73 from=translated src=- shape=c11c4571 vocab=dcb88213
-/
lemma map_velu2QuadDisc {S : Type*} [CommRing S] (f : R →+* S) (x₀ : R) :
    (W.map f).velu2QuadDisc (f x₀) = f (W.velu2QuadDisc x₀) := by
  simp only [velu2QuadDisc, map_b₂, map_b₄, map_sub, map_mul, map_pow, map_ofNat]

end CommRing

end WeierstrassCurve
