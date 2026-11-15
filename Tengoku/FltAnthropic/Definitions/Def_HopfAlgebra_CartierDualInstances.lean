import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace CartierDual

universe u v

section
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

instance instIsCocommViaBialgebra :
    @Coalgebra.IsCocomm R (CartierDual R A) _ _ _ (@Bialgebra.toCoalgebra R (CartierDual R A) _ _ (instBialgebra R A)) :=
  instIsCocomm R A

instance instModuleFiniteViaBialgebra :
    @Module.Finite R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFinite R A

instance instModuleFreeViaBialgebra :
    @Module.Free R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFree R A

end

section Test

universe w
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]

theorem test_bialgebra_mixins {C : Type w} [Semiring C] [Bialgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Free R C] [Module.Flat R C] : True := trivial

theorem test_commring_hopf_mixins {C : Type w} [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Free R C] [Module.Flat R C] : True := trivial

end Test

end CartierDual
