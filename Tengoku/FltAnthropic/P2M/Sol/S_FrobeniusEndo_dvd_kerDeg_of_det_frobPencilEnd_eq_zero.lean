import Tengoku.FltAnthropic.Definitions.Def_EllipticCurve_FrobeniusEndo
import Tengoku.Seed.LinearAlgebra.Determinant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_FrobeniusEndo_dvd_kerDeg_of_det_frobPencilEnd_eq_zero

open _root_.WeierstrassCurve open _root_.WeierstrassCurve.Affine open _root_.WeierstrassCurve.Affine.Point open _root_.FrobeniusEndo

namespace FrobeniusEndo
export _root_.FrobeniusEndo (linePencil linePencil_apply kerDeg kerDeg_def frobEnd frobEnd_apply frobPencilEnd)
open _root_.FrobeniusEndo

section Pencil

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ)

/--
@isnad1 id=eq.0h9v.s12.75eadadeea9b from=translated src=- shape=5f49625c vocab=8919aff9
-/
lemma coe_frobPencilEnd_apply (m n : ℤ) (x : Submodule.torsionBy ℤ (W⁄K).Point p) :
    ((frobPencilEnd W σ p m n x : Submodule.torsionBy ℤ (W⁄K).Point p) : (W⁄K).Point)
      = linePencil (frobEnd W σ) m n x := by
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, linePencil_apply,
    frobEnd_apply, Int.cast_smul_eq_zsmul, Submodule.coe_sub, Submodule.coe_smul_of_tower]
  rfl

/--
@isnad1 id=iff.0h9v.s12.94d28a24a8d6 from=translated src=- shape=4c210609 vocab=9609db8c
-/
lemma frobPencilEnd_eq_zero_iff (m n : ℤ) (x : Submodule.torsionBy ℤ (W⁄K).Point p) :
    frobPencilEnd W σ p m n x = 0 ↔ (x : (W⁄K).Point) ∈ (linePencil (frobEnd W σ) m n).ker := by
  rw [AddMonoidHom.mem_ker, ← coe_frobPencilEnd_apply, ZeroMemClass.coe_eq_zero]

end Pencil

section Dictionary

variable {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K]
  [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K]
  (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime]

/--
@isnad1 id=dvd.1h8v.s14.9abd0599112f from=translated src=- shape=6b07c5cc vocab=8d594428
-/
theorem dvd_kerDeg_of_det_eq_zero {m n : ℤ}
    (hdet : LinearMap.det (frobPencilEnd W σ p m n) = 0) :
    p ∣ kerDeg (frobEnd W σ) m n := by

  have hker : LinearMap.ker (frobPencilEnd W σ p m n) ≠ ⊥ :=
    bot_lt_iff_ne_bot.mp (LinearMap.bot_lt_ker_of_det_eq_zero hdet)
  obtain ⟨x, hxker, hx0⟩ := (Submodule.ne_bot_iff _).mp hker
  rw [LinearMap.mem_ker, frobPencilEnd_eq_zero_iff] at hxker

  have hx0' : (x : (W⁄K).Point) ≠ 0 := fun h0 => hx0 (Subtype.ext h0)
  have hxp : p • (x : (W⁄K).Point) = 0 := by
    have hx_tors : ((p : ℤ)) • (x : (W⁄K).Point) = 0 := (Submodule.mem_torsionBy_iff _ _).mp x.2
    rwa [Nat.cast_smul_eq_nsmul] at hx_tors

  set y : (linePencil (frobEnd W σ) m n).ker := ⟨_, hxker⟩ with hy
  have hyp : p • y = 0 := Subtype.ext hxp
  have hy0 : y ≠ 0 := fun h0 => hx0' (congrArg Subtype.val h0)
  have hyord : addOrderOf y = p := by
    have h1 : addOrderOf y ∣ p := addOrderOf_dvd_of_nsmul_eq_zero hyp
    rcases (Nat.Prime.eq_one_or_self_of_dvd (Fact.out : p.Prime) _ h1) with h | h
    · exact absurd (AddMonoid.addOrderOf_eq_one_iff.mp h) hy0
    · exact h

  rw [kerDeg_def, ← hyord]
  exact addOrderOf_dvd_natCard y

end Dictionary

end FrobeniusEndo

/--
@isnad1 id=dvd.1h8v.s14.9abd0599112f from=translated src=- shape=6b07c5cc vocab=8d594428
-/
theorem solution {R : Type*} {S : Type*} {K : Type*} [CommRing R] [CommRing S] [Field K] [DecidableEq K] [Algebra R S] [Algebra R K] [Algebra S K] [IsScalarTower R S K] (W : WeierstrassCurve R) (σ : K ≃ₐ[S] K) (p : ℕ) [Fact p.Prime] {m n : ℤ} (h : LinearMap.det (frobPencilEnd W σ p m n) = 0) : p ∣ kerDeg (frobEnd W σ) m n :=
  FrobeniusEndo.dvd_kerDeg_of_det_eq_zero W σ p h
