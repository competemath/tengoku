/-
Copyright (c) 2026 Dominique Lawson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Dominique Lawson, Henning Basold, Peter Bruin
-/
module

public import Tengoku
public import Tengoku.LeanPool.LeanPool.DirectedTopologyLean4.Dipath

/-!
# LeanPool.DirectedTopologyLean4.TransRefl
-/

@[expose] public section

/-
  Auxiliary lemmas for the reflTrans and transRefl definitions in directed_path_homotopy.lean.
  These two are definitions are dihomotopies related to a `p : Dipath x₀ x₁`:
    reflTrans : from `(refl x₀).trans p` to `p`
    transRefl : from `p` to `p.trans (refl x₁)`

  Those for transRefl can be based on the auxiliary lemmas found in
  algebraic_topology.fundamental_groupoid.basic.
  They use symmetry for reflTrans which is not possible in the directed case, so we have to define
  them manually.
-/

open DirectedSpace DirectedMap
open scoped unitInterval

universe u v

variable {X : Type u} {Y : Type v}
variable [DirectedSpace X] [DirectedSpace Y]
variable {x₀ x₁ : X}

noncomputable section

namespace Dipath

namespace Dihomotopy

open Path.Homotopy

/--
@isnad1 id=directed.0h0v.s6.6b5c44fce2a1 from=translated src=- shape=fb48e863 vocab=2cd1ee16
-/
lemma directed_transReflReparamAux : DirectedMap.Directed
    ({ toFun := fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩
       continuous_toFun := Continuous.subtype_mk continuous_transReflReparamAux _ } :
      C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold transReflReparamAux
  simp only [one_div, ContinuousMap.coe_mk, Subtype.mk_le_mk]
  have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs <;> linarith

/-- The auxiliary reparametrization map `I → I` used to show that `p.trans (refl _)` is
dihomotopic to `p`, packaged as a directed map. -/
def TransReflReparamAuxMap : D(I,I) where
  toFun := fun t => ⟨transReflReparamAux t, transReflReparamAux_mem_I t⟩
  continuous_toFun := Continuous.subtype_mk continuous_transReflReparamAux _
  directed_toFun := directed_transReflReparamAux

/--
@isnad1 id=eq.0h4v.s5.f4c8b8a60118 from=translated src=- shape=9a5a58ff vocab=ad3cf80f
-/
lemma trans_refl_reparam_dipath (p : Dipath x₀ x₁) : p.trans (Dipath.refl x₁) =
    p.reparam TransReflReparamAuxMap (Subtype.ext transReflReparamAux_zero)
      (Subtype.ext transReflReparamAux_one) := by
  ext t
  rw [show (p.trans (Dipath.refl x₁)) t = p.toPath.trans (Path.refl x₁) t from rfl,
    Path.Homotopy.trans_refl_reparam p.toPath]
  rfl

/-- Auxilliary function for `ReflTransReparam` -/
def ReflTransReparamAux (t : I) : ℝ :=
if (t : ℝ) ≤ 1/2 then
  0
else
  2 * t - 1

/--
@isnad1 id=continuo.0h0v.s4.66feb79c6094 from=translated src=- shape=f7148d33 vocab=755cc9e3
-/
@[continuity]
lemma continuous_ReflTransReparamAux : Continuous ReflTransReparamAux := by
  refine continuous_if_le ?_ ?_ (Continuous.continuousOn ?_) (Continuous.continuousOn ?_) ?_ <;>
  [continuity; continuity; continuity; continuity; skip]
  simp_all

/--
@isnad1 id=mem.0h1v.s3.d89fe9cd7993 from=translated src=- shape=036a84be vocab=79f9bcf4
-/
lemma reflTransReparamAux_mem_I (t : I) : ReflTransReparamAux t ∈ I := by
  unfold ReflTransReparamAux
  split_ifs <;> constructor <;> linarith [unitInterval.le_one t, unitInterval.nonneg t]

/--
@isnad1 id=eq.0h0v.s4.8ff527bfe7bb from=translated src=- shape=bc5c0df9 vocab=aacd4204
-/
lemma reflTransReparamAux_zero : ReflTransReparamAux 0 = 0 :=
by norm_num [ReflTransReparamAux]

/--
@isnad1 id=eq.0h0v.s4.c377e78e2e74 from=translated src=- shape=bc5c0df9 vocab=aacd4204
-/
lemma reflTransReparamAux_one : ReflTransReparamAux 1 = 1 :=
by norm_num [ReflTransReparamAux]

/--
@isnad1 id=directed.0h0v.s6.17a59e95af4e from=translated src=- shape=fb48e863 vocab=30b7820c
-/
lemma directed_ReflTransReparamAux : DirectedMap.Directed
    ({ toFun := fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩
       continuous_toFun := Continuous.subtype_mk continuous_ReflTransReparamAux _ } :
      C(I, I)) := by
  apply DirectedUnitInterval.directed_of_monotone _
  intros x y hxy
  unfold ReflTransReparamAux
  simp only [one_div, ContinuousMap.coe_mk, Subtype.mk_le_mk]
  have hxy' : (x : ℝ) ≤ (y : ℝ) := hxy
  split_ifs with h₁ h₂
  · linarith
  · have := lt_of_not_ge h₂
    linarith
  · linarith
  · linarith

/-- The auxiliary reparametrization map `I → I` used to show that `(refl _).trans p` is
dihomotopic to `p`, packaged as a directed map. -/
def ReflTransReparamAuxMap : D(I,I) where
  toFun := fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩
  continuous_toFun := Continuous.subtype_mk continuous_ReflTransReparamAux _
  directed_toFun := directed_ReflTransReparamAux

/--
@isnad1 id=eq.0h4v.s6.8f914829b4ac from=translated src=- shape=6f86de83 vocab=fc7cd89e
-/
lemma refl_trans_reparam (p : Path x₀ x₁) :
    (Path.refl x₀).trans p =
      p.reparam (fun t => ⟨ReflTransReparamAux t, reflTransReparamAux_mem_I t⟩) (by continuity)
        (Subtype.ext reflTransReparamAux_zero) (Subtype.ext reflTransReparamAux_one) := by
  ext
  unfold ReflTransReparamAux
  simp [Path.trans_apply, Function.comp_apply]
  split_ifs <;> simp

/--
@isnad1 id=eq.0h4v.s5.79ad07e204d3 from=translated src=- shape=35f24186 vocab=8ea28071
-/
lemma refl_trans_reparam_dipath (p : Dipath x₀ x₁) : (Dipath.refl x₀).trans p =
    p.reparam ReflTransReparamAuxMap
      (Subtype.ext reflTransReparamAux_zero) (Subtype.ext reflTransReparamAux_one) := by
  ext t
  rw [show ((Dipath.refl x₀).trans p) t = (Path.refl x₀).trans p.toPath t from rfl,
    refl_trans_reparam p.toPath]
  rfl

end Dihomotopy

end Dipath
