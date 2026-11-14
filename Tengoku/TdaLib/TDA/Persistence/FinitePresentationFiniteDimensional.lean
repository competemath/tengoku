import Tengoku.TdaLib.TDA.Persistence.FinitePresentation
import Tengoku.Seed.LinearAlgebra.FiniteDimensional.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Finite-dimensional fibers of finitely presented modules

Over a field, every fiber of a finitely presented persistence module is finite-dimensional.
The proof uses the finite free cover at each index and transports finite-dimensionality
across the presentation isomorphism.
-/

set_option autoImplicit false

universe u v w

namespace TDA.Persistence

namespace GradedFree

variable {k : Type u} [Field k] {P : Type v} [Preorder P]

/-- A graded free module on finitely many generators has finite-dimensional fibers.
@isnad1 id=finitedi.0h4v.s7.ad5e35a08367 from=translated src=- shape=80cf72a2 vocab=5799c808
-/
theorem finiteDimensional_fiber (W : GradedGenerators.{v,w} P)
    [Finite W.Carrier] (a : P) :
    FiniteDimensional k ((module (R := k) W).obj a) := by
  change FiniteDimensional k (fiber (R := k) W a)
  infer_instance

namespace Presentation

/-- A presentation with finitely many generators has finite-dimensional fibers.
Finiteness of the relation family is not needed for this conclusion.
@isnad1 id=finitedi.1h4v.s7.4b544e08d64f from=translated src=- shape=d4541600 vocab=46c6edb3
-/
theorem finiteDimensional_of_finite_generators
    (D : GradedFree.Presentation.{u,v,w} (R := k) (P := P))
    (hW : Finite D.generators.Carrier) (a : P) :
    FiniteDimensional k (D.presented.obj a) := by
  letI : Finite D.generators.Carrier := hW
  haveI : FiniteDimensional k ((module (R := k) D.generators).obj a) :=
    finiteDimensional_fiber D.generators a
  apply FiniteDimensional.of_surjective (D.cover.app a).hom
  exact D.cover_surjective a

end Presentation

/-- Every fiber of a finitely presented persistence module over a field is
finite-dimensional.
@isnad1 id=finitedi.1h4v.s6.74d701a92040 from=translated src=- shape=a92573bb vocab=cdb09cdf
-/
theorem finitelyPresented_finiteDimensional
    (M : PModule.{u,v,max u w} k P)
    (hM : FinitelyPresented (R := k) (P := P) M) (a : P) :
    FiniteDimensional k (M.obj a) := by
  classical
  obtain ⟨D, hD, ⟨e⟩⟩ := hM
  letI : FiniteDimensional k (D.presented.obj a) :=
    D.finiteDimensional_of_finite_generators hD.1 a
  exact (e.app a).toLinearEquiv.finiteDimensional

end GradedFree

end TDA.Persistence
