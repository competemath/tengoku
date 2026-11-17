import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_wittHomMap_convMul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_wittHomMap_convMul

set_option autoImplicit false

open Function Deformation Deformation.TruncWitt

universe u v w

theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A]
    {B : Type w} [CommRing B] [Bialgebra R B] [Coalgebra.IsCocomm R B]
    (φ ψ : WithConv (B →ₐc[R] A)) (x : Deformation.wittHom R p n B) :
    Deformation.wittHomMap p n (φ * ψ).ofConv x =
      Deformation.wittHomMap p n φ.ofConv x + Deformation.wittHomMap p n ψ.ofConv x := by
  refine Subtype.ext ?_
  rw [AddSubgroup.coe_add, coe_wittHomMap, coe_wittHomMap, coe_wittHomMap]
  have h := map_convMul_of_mem_wittHom (T := A) x.2
    (WithConv.toConv (φ.ofConv : B →ₐ[R] A)) (WithConv.toConv (ψ.ofConv : B →ₐ[R] A))
  have hmul : ((φ * ψ).ofConv : B →ₐ[R] A) =
      (WithConv.toConv (φ.ofConv : B →ₐ[R] A) * WithConv.toConv (ψ.ofConv : B →ₐ[R] A)).ofConv :=
    congrArg WithConv.ofConv (BialgHom.toAlgHom_convMul φ ψ)
  rw [hmul]
  exact h
