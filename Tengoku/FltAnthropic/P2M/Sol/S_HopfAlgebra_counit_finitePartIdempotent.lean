import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_counit_finitePartIdempotent.lean`: wrote out 7 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 7 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_counit_finitePartIdempotent
set_option maxHeartbeats 1600000

open scoped TensorProduct

open IsLocalRing

namespace FinitePart

section Away
variable {H : Type*} [CommRing H]

theorem algebraMap_eq_one_of_isIdempotentElem {e : H} (he : IsIdempotentElem e)
    (L : Type*) [CommRing L] [Algebra H L] [IsLocalization.Away e L] : algebraMap H L e = 1 := by
  have hu : IsUnit (algebraMap H L e) := IsLocalization.Away.algebraMap_isUnit e
  apply hu.mul_left_cancel
  rw [← map_mul, he.eq, mul_one]

theorem algebraMap_surjective_of_isIdempotentElem {e : H} (he : IsIdempotentElem e)
    (L : Type*) [CommRing L] [Algebra H L] [IsLocalization.Away e L] : Function.Surjective (algebraMap H L) := by
  intro x
  obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers e) x
  refine ⟨r, ?_⟩
  obtain ⟨n, hn⟩ := s.2
  symm
  rw [IsLocalization.mk'_eq_iff_eq_mul, ← hn, map_pow, algebraMap_eq_one_of_isIdempotentElem he L, one_pow, mul_one]

end Away

section Local
variable {R : Type*} [CommRing R] [IsLocalRing R] {H : Type*} [CommRing H] [Algebra R H]

end Local

end FinitePart

section Counit
open IsLocalRing
variable {R : Type*} [CommRing R] [IsLocalRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

end Counit

section MapAlong
open IsLocalRing
variable {R : Type*} [CommRing R] {H H' : Type*} [CommRing H] [CommRing H'] [Algebra R H] [Algebra R H']

end MapAlong

section Antipode
open IsLocalRing HopfAlgebra

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

noncomputable def FinitePart.antipodeAlgHom : H →ₐ[R] H :=
  AlgHom.ofLinearMap (HopfAlgebraStruct.antipode R) antipode_one (fun a b => by rw [antipode_mul_antidistrib, mul_comm])

variable [IsLocalRing R]

end Antipode
open scoped _root_.P2MW.S_HopfAlgebra_counit_finitePartIdempotent.FinitePart

section Galois
open HopfAlgebra

variable {R : Type*} [CommRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

namespace FinitePart

local notation "L" => (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
local notation "Rg" => (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)
local notation "Sₐ" => (FinitePart.antipodeAlgHom (R := R) (H := H))

end FinitePart
open scoped _root_.P2MW.S_HopfAlgebra_counit_finitePartIdempotent.FinitePart
end Galois
open scoped _root_.P2MW.S_HopfAlgebra_counit_finitePartIdempotent.FinitePart

section DeltaMain
open IsLocalRing HopfAlgebra

namespace FinitePart

variable {R : Type*} [CommRing R]

variable {H : Type*} [CommRing H]

end FinitePart
open scoped _root_.P2MW.S_HopfAlgebra_counit_finitePartIdempotent.FinitePart
end DeltaMain
open scoped _root_.P2MW.S_HopfAlgebra_counit_finitePartIdempotent.FinitePart

section DeltaCard
open IsLocalRing HopfAlgebra

namespace FinitePart
variable {R : Type*} [CommRing R] [IsLocalRing R] {H : Type*} [CommRing H] [HopfAlgebra R H]

local notation "L" => (Algebra.TensorProduct.includeLeft : H →ₐ[R] H ⊗[R] H)
local notation "Rg" => (Algebra.TensorProduct.includeRight : H →ₐ[R] H ⊗[R] H)

end FinitePart
open scoped _root_.P2MW.S_HopfAlgebra_counit_finitePartIdempotent.FinitePart
end DeltaCard
open scoped _root_.P2MW.S_HopfAlgebra_counit_finitePartIdempotent.FinitePart
