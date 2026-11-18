import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_HeckeOperator
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_AtkinLehnerDatum

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.lean`: wrote out 35 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_export`, 33 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.lean`: removed 2 `#adaptation_note` / `set_option linter` line(s) (notes and linter settings: no declaration depends on them). What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0

set_option autoImplicit false

namespace WcPort

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup
open scoped MatrixGroups ModularForm

noncomputable section

namespace HeckeAnalytic

def repMat (ℓ : ℕ) : Option (Fin ℓ) → Matrix (Fin 2) (Fin 2) ℤ
  | none => !![(ℓ : ℤ), 0; 0, 1]
  | some j => !![1, (j : ℤ); 0, (ℓ : ℤ)]

lemma det_repMat (ℓ : ℕ) (i : Option (Fin ℓ)) : (repMat ℓ i).det = (ℓ : ℤ) := by
  cases i <;> simp [repMat, Matrix.det_fin_two_of]

def repGL (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℝ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

def heckeSlashSum (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ i : Option (Fin ℓ), f ∣[k] repGL ℓ i

end HeckeAnalytic
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

namespace SlashInvariantForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} {k : ℤ}

end SlashInvariantForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

namespace HeckeAnalytic

open OnePoint
open scoped Manifold

def repGLQ (ℓ : ℕ) [NeZero ℓ] (i : Option (Fin ℓ)) : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero ((repMat ℓ i).map (algebraMap ℤ ℚ)) (by
    have h : ((repMat ℓ i).map (algebraMap ℤ ℚ)).det = (algebraMap ℤ ℚ) (repMat ℓ i).det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, det_repMat]
    simp [NeZero.ne ℓ])

end HeckeAnalytic
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

namespace ModularForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

end ModularForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

end CuspForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

end
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Real

noncomputable section

namespace HeckeAnalytic

variable {ℓ : ℕ} [NeZero ℓ]

local notation "𝕢" => Function.Periodic.qParam

end HeckeAnalytic
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

end
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace HeckeAnalytic

def heckeUSlashSum (k : ℤ) (ℓ : ℕ) [NeZero ℓ] (f : ℍ → ℂ) : ℍ → ℂ :=
  ∑ j : Fin ℓ, f ∣[k] repGL ℓ (some j)

open OnePoint

end HeckeAnalytic
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

namespace SlashInvariantForm

open HeckeAnalytic CongruenceSubgroup

variable {N : ℕ} {k : ℤ}

end SlashInvariantForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic

namespace ModularForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

end ModularForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm

namespace CuspForm

open HeckeAnalytic CongruenceSubgroup OnePoint

variable {N : ℕ} [NeZero N] {k : ℤ}

end CuspForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm

end
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace ModularCurve

variable (M q : ℕ)

structure ALData : Type where

  R : ℕ

  hM : M = q * R

  a : ℤ

  b : ℤ

  bezout : (q : ℤ) * a - (R : ℤ) * b = 1

namespace ALData

variable {M q : ℕ} (W : ALData M q)

include W in

lemma q_pos [NeZero M] : 0 < q := by
  rcases Nat.eq_zero_or_pos q with h | h
  · exact absurd (W.hM.trans (Nat.mul_eq_zero.mpr (Or.inl h))) (NeZero.ne M)
  · exact h

def mat : Matrix (Fin 2) (Fin 2) ℤ := !![(q : ℤ) * W.a, W.b; (q : ℤ) * (W.R : ℤ), (q : ℤ)]

@[scoped simp] lemma det_mat : W.mat.det = (q : ℤ) := by
  rw [mat, Matrix.det_fin_two_of]
  linear_combination (q : ℤ) * W.bezout

def sqUnit : Matrix (Fin 2) (Fin 2) ℤ :=
  !![(q : ℤ) * W.a ^ 2 + (W.R : ℤ) * W.b, W.b * (W.a + 1);
     (q : ℤ) * (W.R : ℤ) * (W.a + 1), (W.R : ℤ) * W.b + (q : ℤ)]

@[scoped simp] lemma det_sqUnit : W.sqUnit.det = 1 := by
  rw [sqUnit, Matrix.det_fin_two_of]
  linear_combination ((q : ℤ) * W.a - (W.R : ℤ) * W.b + 1) * W.bezout

def sqUnitSL : SL(2, ℤ) := ⟨W.sqUnit, W.det_sqUnit⟩

end ALData
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData

end ModularCurve
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve

namespace HeckeAnalytic

open ModularCurve OnePoint

variable {M q : ℕ} (W : ALData M q)

private def _root_.WcPort.HeckeAnalytic.alGL [NeZero M] : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℝ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℝ)).det = (algebraMap ℤ ℝ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using W.q_pos.ne')

export _root_.WcPort.HeckeAnalytic (alGL)

def alGLQ [NeZero M] : GL (Fin 2) ℚ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (W.mat.map (algebraMap ℤ ℚ)) (by
    have h : ((W.mat).map (algebraMap ℤ ℚ)).det = (algebraMap ℤ ℚ) W.mat.det := by
      rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    rw [h, W.det_mat]
    simpa using W.q_pos.ne')

private def _root_.WcPort.HeckeAnalytic.alSlash (k : ℤ) [NeZero M] (f : ℍ → ℂ) : ℍ → ℂ := f ∣[k] alGL W

export _root_.WcPort.HeckeAnalytic (alSlash)

variable (q) in

def scalarGL (hq : 0 < q) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℝ), 0; 0, (q : ℝ)] (by
    rw [Matrix.det_fin_two_of]
    have hq' : (q : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    simpa using mul_ne_zero hq' hq')

end HeckeAnalytic
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve

namespace SlashInvariantForm

open HeckeAnalytic ModularCurve CongruenceSubgroup

variable {M q : ℕ} {k : ℤ}

end SlashInvariantForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

namespace ModularForm

open HeckeAnalytic ModularCurve CongruenceSubgroup OnePoint

variable {M q : ℕ} {k : ℤ}

end ModularForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

namespace CuspForm

open HeckeAnalytic ModularCurve CongruenceSubgroup OnePoint

variable {M q : ℕ} {k : ℤ}

end CuspForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

end
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm Manifold

noncomputable section

namespace ModularCurve
namespace ALData

variable {M q : ℕ} (W : ALData M q)

def traceRepMat : Option (Fin q) → Matrix (Fin 2) (Fin 2) ℤ
  | none => W.mat
  | some j => HeckeAnalytic.repMat q (some j)

end ModularCurve.ALData
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

namespace HeckeAnalytic

open ModularCurve

variable {M q : ℕ} (W : ALData M q)

def traceRepGL [NeZero M] [NeZero q] : Option (Fin q) → GL (Fin 2) ℝ
  | Option.none => alGL W
  | Option.some j => repGL q (Option.some j)

def traceSlashSum (k : ℤ) [NeZero M] [NeZero q] (f : ℍ → ℂ) : ℍ → ℂ :=
  f + heckeUSlashSum k q (alSlash W k f)

open OnePoint

end HeckeAnalytic
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

namespace CuspForm

open HeckeAnalytic ModularCurve CongruenceSubgroup OnePoint

variable {M q : ℕ} [NeZero M]

end CuspForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

end
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

open Matrix UpperHalfPlane ModularForm CongruenceSubgroup Function
open scoped MatrixGroups ModularForm

noncomputable section

namespace HeckeAnalytic

open ModularCurve

variable {M q : ℕ}

end HeckeAnalytic
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

namespace ModularCurve
namespace ALData

variable {M q : ℕ}

end ModularCurve.ALData
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

end
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm

end WcPort
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort

namespace WcPort
namespace HeckeAnalytic

open UpperHalfPlane
open scoped ModularForm MatrixGroups

end WcPort.HeckeAnalytic
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort

namespace WcPort
open UpperHalfPlane
open scoped ModularForm MatrixGroups

def toALData {M q : ℕ} (W : _root_.ModularForm.AtkinLehnerDatum M q) : ModularCurve.ALData M q :=
  ⟨W.R, W.hM, W.a, W.b, W.bezout⟩

end WcPort
open scoped _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.HeckeAnalytic _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.CuspForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve.ALData _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.ModularCurve _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort.SlashInvariantForm _root_.P2MW.S_ModularForm_add_heckeU_alSlash_slash_eq_self_of_mem_Gamma0.WcPort
