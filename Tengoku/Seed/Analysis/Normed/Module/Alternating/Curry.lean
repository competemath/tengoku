/-
Copyright (c) 2025 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Eric Wieser
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.LinearAlgebra.Alternating.Curry
public import Tengoku.Seed.Analysis.Normed.Module.Alternating.Basic
public import Tengoku.Seed.Analysis.Normed.Module.Multilinear.Curry

/-!
# Currying continuous alternating forms

In this file we define `ContinuousAlternatingMap.curryLeft`
which interprets a continuous alternating map in `n + 1` variables
as a continuous linear map in the 0th variable
taking values in the continuous alternating maps in `n` variables.
-/

@[expose] public section

variable {𝕜 E F G : Type*} [NontriviallyNormedField 𝕜]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G]
  {n : ℕ}

namespace ContinuousAlternatingMap

/-- Given a continuous alternating map `f` in `n+1` variables, split the first variable to obtain
a continuous linear map into continuous alternating maps in `n` variables,
given by `x ↦ (m ↦ f (Matrix.vecCons x m))`.
It can be thought of as a map $Hom(\bigwedge^{n+1} M, N) \to Hom(M, Hom(\bigwedge^n M, N))$.

This is `ContinuousMultilinearMap.curryLeft` for `AlternatingMap`. See also
`ContinuousAlternatingMap.curryLeftLI`. -/
noncomputable def curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : E →L[𝕜] E [⋀^Fin n]→L[𝕜] F :=
  AlternatingMap.mkContinuousLinear f.toAlternatingMap.curryLeft ‖f‖
    f.toContinuousMultilinearMap.norm_map_cons_le

/--
@isnad1 id=eq.0h6v.s10.a69872f593be from=seed src=0 shape=253b4ca9 vocab=ef4e7164
-/
@[simp]
lemma toContinuousMultilinearMap_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) :
    (f.curryLeft x).toContinuousMultilinearMap = f.toContinuousMultilinearMap.curryLeft x :=
  rfl

/--
@isnad1 id=eq.0h6v.s10.3b7de2fdd33f from=seed src=0 shape=9793545d vocab=80e64cea
-/
@[simp]
lemma toAlternatingMap_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) :
    (f.curryLeft x).toAlternatingMap = f.toAlternatingMap.curryLeft x :=
  rfl

/--
@isnad1 id=eq.0h5v.s9.964f17bada2e from=seed src=0 shape=53a5d626 vocab=81517cc6
-/
@[simp]
lemma norm_curryLeft (f : E [⋀^Fin (n + 1)]→L[𝕜] F) : ‖f.curryLeft‖ = ‖f‖ :=
  f.toContinuousMultilinearMap.curryLeft_norm

/--
@isnad1 id=eq.0h7v.s10.e3969229a644 from=seed src=0 shape=d29fcff9 vocab=8bcdf561
-/
@[simp]
theorem curryLeft_apply_apply (f : E [⋀^Fin (n + 1)]→L[𝕜] F) (x : E) (v : Fin n → E) :
    curryLeft f x v = f (Matrix.vecCons x v) :=
  rfl

/--
@isnad1 id=eq.0h4v.s10.7432f7d0abbc from=seed src=0 shape=c7eb0381 vocab=2b5fda68
-/
@[simp]
theorem curryLeft_zero : curryLeft (0 : E [⋀^Fin (n + 1)]→L[𝕜] F) = 0 :=
  rfl

/--
@isnad1 id=eq.0h6v.s11.86c848c49c98 from=seed src=0 shape=30c2c849 vocab=2b5fda68
-/
@[simp]
theorem curryLeft_add (f g : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryLeft (f + g) = curryLeft f + curryLeft g :=
  rfl

/--
@isnad1 id=eq.0h6v.s11.e23a35d41134 from=seed src=0 shape=af2fe433 vocab=1e68ffbb
-/
@[simp]
theorem curryLeft_smul (r : 𝕜) (f : E [⋀^Fin (n + 1)]→L[𝕜] F) :
    curryLeft (r • f) = r • curryLeft f :=
  rfl

/-- `ContinuousAlternatingMap.curryLeft` as a `LinearIsometry`. -/
@[simps]
noncomputable def curryLeftLI :
    (E [⋀^Fin (n + 1)]→L[𝕜] F) →ₗᵢ[𝕜] (E →L[𝕜] E [⋀^Fin n]→L[𝕜] F) where
  toFun f := f.curryLeft
  map_add' := curryLeft_add
  map_smul' := curryLeft_smul
  norm_map' := norm_curryLeft

/-- Currying with the same element twice gives the zero map.
@isnad1 id=eq.0h6v.s10.2fc34ecef0a4 from=seed src=0 shape=13148c6a vocab=f230284d
-/
@[simp]
theorem curryLeft_same (f : E [⋀^Fin (n + 2)]→L[𝕜] F) (x : E) :
    (f.curryLeft x).curryLeft x = 0 :=
  ext fun _ ↦ f.map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one

/--
@isnad1 id=eq.0h8v.s10.b932edba9e97 from=seed src=0 shape=09507e12 vocab=30691f3b
-/
@[simp]
theorem curryLeft_compContinuousAlternatingMap (g : F →L[𝕜] G) (f : E [⋀^Fin (n + 1)]→L[𝕜] F)
    (x : E) :
    (g.compContinuousAlternatingMap f).curryLeft x =
      g.compContinuousAlternatingMap (f.curryLeft x) :=
  rfl

/--
@isnad1 id=eq.0h8v.s11.a9fb1804267c from=seed src=0 shape=7d6a4ef8 vocab=f475e050
-/
@[simp]
theorem curryLeft_compContinuousLinearMap (g : F [⋀^Fin (n + 1)]→L[𝕜] G) (f : E →L[𝕜] F) (x : E) :
    (g.compContinuousLinearMap f).curryLeft x = (g.curryLeft (f x)).compContinuousLinearMap f :=
  ext fun v ↦ congr_arg g <| funext fun i ↦ by cases i using Fin.cases <;> simp

end ContinuousAlternatingMap
