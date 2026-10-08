/-
Copyright (c) 2024 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
Changed for Tengoku: copied from Mathlib (leanprover-community/mathlib4 at 85e3a25e006c); import paths rewritten.
-/
module

public import Tengoku.Seed.Algebra.Star.TransferInstance
public import Tengoku.Seed.Analysis.InnerProductSpace.Adjoint
public import Tengoku.Seed.Analysis.InnerProductSpace.Dual
public import Tengoku.Seed.Analysis.LocallyConvex.WeakOperatorTopology

/-!
# The weak operator topology in Hilbert spaces

This file gives a few properties of the weak operator topology that are specific to operators on
Hilbert spaces. This mostly involves using the Fréchet-Riesz representation to convert between
applications of elements of the dual and inner products with vectors in the space.

## Main results

+ `ContinuousLinearMapWOT.tendsto_iff_forall_inner_apply_tendsto`: a function `f : α → E →WOT[𝕜] F`
  tends to `𝓝 A` if and only if `fun a ↦ ⟪y, (f a) x⟫_𝕜` tends to `𝓝 ⟪y, A x⟫_𝕜` for all
  `x : E`, `y : F`. Also included are the corresponding characterizations of continuity.
+ The adjoint operation is continuous in the weak operator topology, declared as an instance of
  `ContinuousStar (F →WOT[𝕜] F)`.
-/

public section

open scoped Topology InnerProductSpace

namespace ContinuousLinearMapWOT

variable {𝕜 : Type*} {E : Type*} {F : Type*} [RCLike 𝕜] [AddCommGroup E] [TopologicalSpace E]
  [Module 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

/--
@isnad1 id=eq.1h5v.s9.12ebcbdfebbd from=seed src=0 shape=e5ca58ca vocab=132fb81c
-/
@[ext]
lemma ext_inner {A B : E →WOT[𝕜] F} (h : ∀ x y, ⟪y, A x⟫_𝕜 = ⟪y, B x⟫_𝕜) : A = B := by
  rw [ContinuousLinearMapWOT.ext_iff]
  exact fun x => ext_inner_left 𝕜 fun y => h x y

variable [CompleteSpace F]

open Filter in
/-- The defining property of the weak operator topology: a function `f` tends to
`A : E →WOT[𝕜] F` along filter `l` iff `⟪y, (f a) x⟫` tends to `⟪y, A x⟫` along the same filter.
@isnad1 id=iff.0h7v.s9.6ed8d579c6fb from=seed src=0 shape=99eda2b1 vocab=ead5c8fa
-/
lemma tendsto_iff_forall_inner_apply_tendsto {α : Type*} {l : Filter α}
    {f : α → E →WOT[𝕜] F} {A : E →WOT[𝕜] F} :
    Tendsto f l (𝓝 A) ↔ ∀ x y, Tendsto (fun a => ⟪y, (f a) x⟫_𝕜) l (𝓝 ⟪y, A x⟫_𝕜) := by
  simp_rw [tendsto_iff_forall_dual_apply_tendsto]
  exact .symm <| forall_congr' fun _ ↦
    Equiv.forall_congr (InnerProductSpace.toDual 𝕜 F) fun _ ↦ Iff.rfl

/--
@isnad1 id=iff.0h5v.s10.3bd8db5d84b0 from=seed src=0 shape=8f5acb4f vocab=de644d08
-/
lemma le_nhds_iff_forall_inner_apply_le_nhds {l : Filter (E →WOT[𝕜] F)}
    {A : E →WOT[𝕜] F} : l ≤ 𝓝 A ↔ ∀ x y, l.map (fun T => ⟪y, T x⟫_𝕜) ≤ 𝓝 (⟪y, A x⟫_𝕜) :=
  tendsto_iff_forall_inner_apply_tendsto (f := id)

/--
@isnad1 id=iff.0h7v.s8.6051960b4c65 from=seed src=0 shape=7dd16aa9 vocab=a1ba861c
-/
lemma continuousWithinAt_iff {α : Type*} [TopologicalSpace α]
    {f : α → E →WOT[𝕜] F} {s : Set α} {a : α} :
    ContinuousWithinAt f s a ↔ ∀ x y, ContinuousWithinAt (⟪y, f · x⟫_𝕜) s a :=
  tendsto_iff_forall_inner_apply_tendsto

/--
@isnad1 id=iff.0h6v.s8.6ba828661c24 from=seed src=0 shape=385ad58c vocab=5796eb4c
-/
lemma continuousAt_iff {α : Type*} [TopologicalSpace α] {f : α → E →WOT[𝕜] F} {a : α} :
    ContinuousAt f a ↔ ∀ x y, ContinuousAt (⟪y, f · x⟫_𝕜) a :=
  tendsto_iff_forall_inner_apply_tendsto

/--
@isnad1 id=iff.0h6v.s8.361313c227a2 from=seed src=0 shape=3c8d1fa5 vocab=1a69231d
-/
lemma continuousOn_iff {α : Type*} [TopologicalSpace α] {f : α → E →WOT[𝕜] F} {s : Set α} :
    ContinuousOn f s ↔ ∀ x y, ContinuousOn (⟪y, f · x⟫_𝕜) s := by
  simp_rw [ContinuousOn, forall_comm (α := E), forall_comm (α := F), continuousWithinAt_iff]

/--
@isnad1 id=iff.0h5v.s8.3acc9e620384 from=seed src=0 shape=d69425c6 vocab=9ce855a8
-/
lemma continuous_iff {α : Type*} [TopologicalSpace α] {f : α → E →WOT[𝕜] F} :
    Continuous f ↔ ∀ x y, Continuous (⟪y, f · x⟫_𝕜) := by
  simp_rw [continuous_iff_continuousAt, forall_comm (α := E), forall_comm (α := F),
    continuousAt_iff]

@[fun_prop] alias ⟨continuousWithinAt_inner_apply, continuousWithinAt⟩ := continuousWithinAt_iff
@[fun_prop] alias ⟨continuousOn_inner_apply, continuousOn⟩ := continuousOn_iff
@[fun_prop] alias ⟨continuousAt_inner_apply, continuousAt⟩ := continuousAt_iff
@[fun_prop] alias ⟨continuous_inner_apply, continuous⟩ := continuous_iff

noncomputable instance : StarRing (F →WOT[𝕜] F) := equiv.starRing

/--
@isnad1 id=eq.0h4v.s11.993d7f7f00dc from=seed src=0 shape=23e35971 vocab=9ae01203
-/
lemma star_apply (A : F →WOT[𝕜] F) (x : F) : star A x = star (toCLM A) x := rfl

instance : StarModule 𝕜 (F →WOT[𝕜] F) := equiv.starModule 𝕜

instance : ContinuousStar (F →WOT[𝕜] F) where
  continuous_star := by
    simp_rw [continuous_iff, star_apply, ContinuousLinearMap.star_eq_adjoint,
      ContinuousLinearMap.adjoint_inner_right, coe_toCLM]
    rw [forall_comm]
    conv in ⟪_, _⟫_𝕜 => rw [← inner_conj_symm, ← RCLike.star_def]
    fun_prop

end ContinuousLinearMapWOT
