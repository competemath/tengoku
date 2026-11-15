import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_FormalUpperHalfPlaneCharts

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace CerednikDrinfeld.FormalOmega.AlgFunctor

variable {𝒪 : Type} [CommRing 𝒪]

def const (X : Type) : AlgFunctor 𝒪 where
  obj _ := X
  map _ x := x
  map_id _ := rfl
  map_comp _ _ _ := rfl

@[simp] theorem const_map (X : Type) {B : Type} [CommRing B] [Algebra 𝒪 B] {B' : Type} [CommRing B'] [Algebra 𝒪 B']
    (φ : B →ₐ[𝒪] B') (x : X) : (const (𝒪 := 𝒪) X).map φ x = x := rfl

end CerednikDrinfeld.FormalOmega.AlgFunctor
