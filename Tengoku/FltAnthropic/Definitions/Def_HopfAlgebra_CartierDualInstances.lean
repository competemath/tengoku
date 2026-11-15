import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_CartierDual

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace CartierDual

universe u v

section
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]

/--
@isnad1 id=iscocomm.0h2v.s7.72d2ebc223aa from=translated src=- shape=13a02700 vocab=ed439585
-/
instance instIsCocommViaBialgebra :
    @Coalgebra.IsCocomm R (CartierDual R A) _ _ _ (@Bialgebra.toCoalgebra R (CartierDual R A) _ _ (instBialgebra R A)) :=
  instIsCocomm R A

/--
@isnad1 id=finite.0h2v.s7.ce0877bea113 from=translated src=- shape=464b8fe9 vocab=074c29f3
-/
instance instModuleFiniteViaBialgebra :
    @Module.Finite R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFinite R A

/--
@isnad1 id=free.0h2v.s7.a3ff7a862a29 from=translated src=- shape=a96fd7a1 vocab=074c29f3
-/
instance instModuleFreeViaBialgebra :
    @Module.Free R (CartierDual R A) _ _ (@Algebra.toModule R (CartierDual R A) _ _ (@Bialgebra.toAlgebra R (CartierDual R A) _ _ (instBialgebra R A))) :=
  instModuleFree R A

end

section Test

universe w
variable (R : Type u) (A : Type v) [CommRing R] [CommRing A]

/--
@isnad1 id=true.0h2v.s7.1c727f0eb22d from=translated src=- shape=01002588 vocab=8a33b320
-/
theorem test_bialgebra_mixins {C : Type w} [Semiring C] [Bialgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Free R C] [Module.Flat R C] : True := trivial

/--
@isnad1 id=true.0h2v.s8.7e087fa3e6c3 from=translated src=- shape=add7d3e1 vocab=a815d102
-/
theorem test_commring_hopf_mixins {C : Type w} [CommRing C] [HopfAlgebra R C] [Coalgebra.IsCocomm R C]
    [Module.Finite R C] [Module.Free R C] [Module.Flat R C] : True := trivial

end Test

end CartierDual
