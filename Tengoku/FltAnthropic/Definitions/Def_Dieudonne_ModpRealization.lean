import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
namespace Tengoku.FltAnthropic end Tengoku.FltAnthropic open Tengoku.FltAnthropic
set_option autoImplicit false

open scoped TensorProduct
open Deformation

universe u v w

section Realization

variable (k : Type u) [Field k] (p : ℕ) [Fact p.Prime] [CharP k p]
variable (A : Type v) [CommRing A] [HopfAlgebra k A]

noncomputable def _root_.Tengoku.FltAnthropic.primitives : Submodule k A :=
  LinearMap.ker (Coalgebra.comul (R := k) (A := A)
    - (TensorProduct.mk k A A).flip 1 - TensorProduct.mk k A A 1)

abbrev _root_.Tengoku.FltAnthropic.cotangentSpace : Type v :=
  (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent

structure _root_.Tengoku.FltAnthropic.ModpDieudonneRealization
    [Module.Finite k A] [Module.Free k A] [Coalgebra.IsCocomm k A]
    (D : Type w) [AddCommGroup D] [Module k D] [Module.Finite k D] where

  datum : DieudonneDatum ((p : ℕ) : k) D

  order_eq : Module.finrank k A = p ^ Module.finrank k D

  finrank_kerFrob : Module.finrank k (LinearMap.ker datum.F)
    = Module.finrank k (cotangentSpace k A)

  finrank_kerVer : Module.finrank k (LinearMap.ker datum.V)
    = Module.finrank k (primitives k A)

end Realization
-- Tengoku: root names of this library moved to Tengoku.FltAnthropic so they do not collide with other libraries (generated)
