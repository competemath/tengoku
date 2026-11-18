import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_HopfAlgebra_HopfKer

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_finite_free_hopfKer_of_isPrincipalIdealRing

set_option autoImplicit false

open HopfAlgebra

universe u v w

namespace S17KT5b

variable {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
variable {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
variable {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B)

theorem finite : Module.Finite R ↥(hopfKer π) := by
  haveI : IsNoetherianRing R := inferInstance
  haveI : IsNoetherian R A := isNoetherian_of_isNoetherianRing_of_finite R A
  exact Module.Finite.of_injective (Subalgebra.val (hopfKer π)).toLinearMap Subtype.val_injective

theorem free : Module.Free R ↥(hopfKer π) := by
  haveI := finite π
  exact Module.free_of_finite_type_torsion_free'

end S17KT5b

theorem solution {R : Type u} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
    {A : Type v} [CommRing A] [Bialgebra R A] [Module.Finite R A] [Module.Free R A]
    {B : Type w} [CommRing B] [Bialgebra R B] (π : A →ₐc[R] B) :
    Module.Finite R ↥(HopfAlgebra.hopfKer π) ∧ Module.Free R ↥(HopfAlgebra.hopfKer π) :=
  ⟨S17KT5b.finite π, S17KT5b.free π⟩
