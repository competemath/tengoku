import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_ClassSetGraph
import Tengoku.FltAnthropic.Definitions.Def_QuaternionAlgebra_Order
import Tengoku.FltAnthropic.Definitions.Def_Submodule_LocalBox

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_classSetForget_mk_of_le.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_classSetForget_mk_of_le

set_option autoImplicit false

open scoped TensorProduct Quaternion
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

theorem solution
    {a b : ℚ} {U U' : Subgroup (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ} (h : U ≤ U') (x : (ℍ[ℚ, a, b] ⊗[ℚ] FiniteAdeleRing (𝓞 ℚ) ℚ)ˣ) :
    CerednikDrinfeld.classSetForget U U' (QuaternionAlgebra.ClassSet.mk U x) = QuaternionAlgebra.ClassSet.mk U' x := by
  obtain ⟨d, k, hd, hk, hout⟩ :=
    DoubleCoset.mk_out_eq_mul (Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b]).range U x
  obtain ⟨δ, rfl⟩ := MonoidHom.mem_range.mp hd
  show ClassSet.mk U' (ClassSet.mk U x).out = _
  rw [show (ClassSet.mk U x).out = Submodule.finiteIdeleDiagonal ℍ[ℚ, a, b] δ * x * k from hout,
    ClassSet.mk_mul_of_mem _ _ (h hk), ClassSet.mk_diagonal_mul]
