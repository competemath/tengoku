import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.Topology.Compactification.OnePoint.ProjectiveLine
import Tengoku.FltAnthropic.Definitions.Def_ModularForm_HeckeOperator

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_ModularCurve_cosetPoly_smul.lean`: wrote out 3 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 3 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_ModularCurve_cosetPoly_smul

set_option autoImplicit false

noncomputable section

open Matrix.SpecialLinearGroup UpperHalfPlane Polynomial
open scoped MatrixGroups ModularForm OnePoint

namespace ModularCurve

namespace CosetPoly

open ModularForm

/--
@isnad1 id=eq.0h1v.s8.df8917939df4 from=translated src=- shape=3d4d5f77 vocab=ec2cc098
-/
theorem det_eq (g : SL(2, ℤ)) : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
  have h := g.det_coe
  rwa [Matrix.det_fin_two] at h

section commutation

variable {p : ℕ} (hp : p ≠ 0)
include hp

end commutation

section projectiveLine

variable {p : ℕ}

def heckeRep (p : ℕ) (x : OnePoint (ZMod p)) : GL (Fin 2) ℝ :=
  x.elim (heckeDiagMatrix p) (fun j ↦ heckeMatrix p j.val)

variable [Fact p.Prime]

variable (p) in

def redMatrix (g : SL(2, ℤ)) : GL (Fin 2) (ZMod p) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero
    !![((g 1 1 : ℤ) : ZMod p), ((g 0 1 : ℤ) : ZMod p); ((g 1 0 : ℤ) : ZMod p), ((g 0 0 : ℤ) : ZMod p)]
    (by
      have := congrArg (Int.cast : ℤ → ZMod p) (det_eq g)
      push_cast at this
      rw [Matrix.det_fin_two_of,
        show ((g 1 1 : ℤ) : ZMod p) * ((g 0 0 : ℤ) : ZMod p) - ((g 0 1 : ℤ) : ZMod p) * ((g 1 0 : ℤ) : ZMod p)
          = 1 by linear_combination this]
      exact one_ne_zero)

scoped instance : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩

end projectiveLine

section reindex

variable {p : ℕ} [NeZero p]

end reindex

end CosetPoly
open scoped _root_.P2MW.S_ModularCurve_cosetPoly_smul.ModularCurve.CosetPoly

end ModularCurve
open scoped _root_.P2MW.S_ModularCurve_cosetPoly_smul.ModularCurve.CosetPoly _root_.P2MW.S_ModularCurve_cosetPoly_smul.ModularCurve

end
open scoped _root_.P2MW.S_ModularCurve_cosetPoly_smul.ModularCurve.CosetPoly _root_.P2MW.S_ModularCurve_cosetPoly_smul.ModularCurve
