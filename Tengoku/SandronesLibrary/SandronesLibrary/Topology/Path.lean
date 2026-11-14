/-
Copyright (c) 2026 Sandrone's Library contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sandrone's Library contributors
-/
import Tengoku.SandronesLibrary.SandronesLibrary.Topology.RealLine
import Tengoku.Seed.Topology.Path
import Tengoku.Seed.Tactic.Linarith
import Tengoku.Seed.Tactic.NormNum

/-!
# Textbook paths and loops

Paths are defined from the Sandrone unit interval and Sandrone continuity.  This module does not
import the Mathlib topology bridge or Mathlib's `Path`.

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

Current entry:

* `topology.homotopy.path-definition-foundation`.
* `topology.homotopy.path-concatenation-foundation`.
-/

open Set Function

namespace SandronesLibrary.Topology

variable {X : Type*}

/-- Mathlib 的 `Path x y` 恰好打包一条从闭单位区间到空间的连续函数，以及它在零、一端点的
取值。这是教材道路定义的数据展开。

> **Entry**: topology.homotopy.path-definition-foundation
@isnad1 id=iff.0h3v.s6.f5ea51781cb4 from=translated src=- shape=74415f1b vocab=ea2a3bc0
-/
theorem nonempty_path_iff_exists_continuous [TopologicalSpace X] (x y : X) :
    Nonempty (_root_.Path x y) ↔
      ∃ f : unitInterval → X, _root_.Continuous f ∧
        f ⟨0, unitInterval.zero_mem⟩ = x ∧ f ⟨1, unitInterval.one_mem⟩ = y := by
  constructor
  · rintro ⟨γ⟩
    exact ⟨γ, γ.continuous, γ.source, γ.target⟩
  · rintro ⟨f, hf, h0, h1⟩
    exact ⟨{ toFun := f, continuous_toFun := hf, source' := h0, target' := h1 }⟩

/-- Mathlib 的逆道路用单位区间反射重新参数化，因此在参数 `t` 处取原道路在 `1-t` 处的值。

> **Entry**: topology.homotopy.path-reversal-foundation
@isnad1 id=eq.0h5v.s6.eb89abbc6aa7 from=translated src=- shape=6ffc82b2 vocab=0084fe4c
-/
theorem path_symm_apply [TopologicalSpace X] {x y : X}
    (γ : _root_.Path x y) (t : unitInterval) :
    γ.symm t = γ (unitInterval.symm t) := by
  exact _root_.Path.symm_apply γ t

/-- 道路反向两次严格恢复原道路；这是参数函数的严格等式，不需要道路同伦。
@isnad1 id=eq.0h4v.s5.200f0a07b699 from=translated src=- shape=d9486c31 vocab=de4bfb46
-/
theorem path_symm_symm [TopologicalSpace X] {x y : X} (γ : _root_.Path x y) :
    γ.symm.symm = γ :=
  γ.symm_symm

/-- 在参数区间左半段，Mathlib 道路拼接以双倍速度沿第一条道路前进。

> **Entry**: topology.homotopy.path-concatenation-foundation
@isnad1 id=eq.1h7v.s7.b6340308e52d from=translated src=- shape=d6b2aec0 vocab=87105995
-/
theorem path_trans_apply_of_le [TopologicalSpace X] {x y z : X}
    (γ : _root_.Path x y) (δ : _root_.Path y z) (t : unitInterval)
    (h : (t : ℝ) ≤ 1 / 2) :
    γ.trans δ t = γ ⟨2 * t, by constructor <;> linarith [t.2.1, t.2.2]⟩ := by
  rw [_root_.Path.trans_apply]
  simp only [dite_eq_left h]

/-- 在参数区间右半段，Mathlib 道路拼接以双倍速度沿第二条道路前进。
@isnad1 id=eq.1h7v.s8.08914f1da10e from=translated src=- shape=2b2ca113 vocab=438682a0
-/
theorem path_trans_apply_of_not_le [TopologicalSpace X] {x y z : X}
    (γ : _root_.Path x y) (δ : _root_.Path y z) (t : unitInterval)
    (h : ¬(t : ℝ) ≤ 1 / 2) :
    γ.trans δ t = δ ⟨2 * t - 1, by constructor <;> linarith [t.2.1, t.2.2]⟩ := by
  rw [_root_.Path.trans_apply]
  simp only [dite_eq_right h]

end SandronesLibrary.Topology

namespace SandronesLibrary.Topology.TextbookTopology

variable {X Y : Type*}

/-!
> **Entry**: topology.homotopy.path-concatenation-foundation
-/
namespace UnitInterval

/-- Double a parameter in the left half of the unit interval.-/
def leftDouble (t : UnitInterval) (h : t.1 ≤ (1 / 2 : ℝ)) : UnitInterval :=
  ⟨2 * t.1, mul_nonneg (by norm_num) t.2.1, by linarith⟩

/-- Translate and double a parameter in the right half of the unit interval.-/
def rightDouble (t : UnitInterval) (h : ¬ t.1 ≤ (1 / 2 : ℝ)) : UnitInterval :=
  ⟨2 * t.1 - 1, by linarith, by linarith [t.2.2]⟩

end UnitInterval

/-- A path from `a` to `b` in `(X, τX)` is a continuous map from the closed unit interval whose
values at zero and one are `a` and `b`.

> **Entry**: topology.homotopy.path-definition-foundation-/
structure Path (τX : TextbookTopology X) (a b : X) where
  /-- The parametrized map underlying the path.-/
  toFun : UnitInterval → X
  /-- Continuity with respect to the Sandrone unit-interval topology.-/
  continuous : Continuous unitInterval τX toFun
  /-- The path starts at `a`.-/
  source : toFun UnitInterval.zero = a
  /-- The path ends at `b`.-/
  target : toFun UnitInterval.one = b

namespace Path

instance {τX : TextbookTopology X} {a b : X} : CoeFun (Path τX a b) (fun _ ↦ UnitInterval → X) :=
  ⟨Path.toFun⟩

/--
@isnad1 id=eq.1h6v.s5.a51952c34dbe from=translated src=- shape=da3fcb79 vocab=3667b01f
-/
@[ext]
theorem ext {τX : TextbookTopology X} {a b : X} {γ δ : Path τX a b}
    (h : ∀ t, γ t = δ t) : γ = δ := by
  cases γ with
  | mk γ hγ hγ0 hγ1 =>
      cases δ with
      | mk δ hδ hδ0 hδ1 =>
          have hfun : γ = δ := funext h
          subst δ
          rfl

/-- The constant path at `a`.-/
def refl (τX : TextbookTopology X) (a : X) : Path τX a a where
  toFun := fun _ ↦ a
  continuous := continuous_const unitInterval τX a
  source := rfl
  target := rfl

/--
@isnad1 id=eq.0h4v.s4.7ff5bd33b66b from=translated src=- shape=a8f0dfd3 vocab=58dfc768
-/
@[simp] theorem refl_apply (τX : TextbookTopology X) (a : X) (t : UnitInterval) :
    refl τX a t = a :=
  rfl

/-- A continuous map sends a path to a path between the images of its endpoints.-/
def map {τX : TextbookTopology X} {τY : TextbookTopology Y} {a b : X}
    (γ : Path τX a b) (f : X → Y) (hf : Continuous τX τY f) :
    Path τY (f a) (f b) where
  toFun := f ∘ γ
  continuous := hf.comp γ.continuous
  source := by simp [γ.source]
  target := by simp [γ.target]

/--
@isnad1 id=eq.1h9v.s6.44be8110e717 from=translated src=- shape=229e281e vocab=debc5c46
-/
@[simp] theorem map_apply {τX : TextbookTopology X} {τY : TextbookTopology Y} {a b : X}
    (γ : Path τX a b) (f : X → Y) (hf : Continuous τX τY f) (t : UnitInterval) :
    γ.map f hf t = f (γ t) :=
  rfl

/-- The reverse path traverses `γ` with reflected unit-interval parameter.

> **Entry**: topology.homotopy.path-reversal-foundation-/
def symm {τX : TextbookTopology X} {a b : X} (γ : Path τX a b) : Path τX b a where
  toFun := γ ∘ UnitInterval.reflect
  continuous := γ.continuous.comp continuous_unitInterval_reflect
  source := by simp [γ.target]
  target := by simp [γ.source]

/--
@isnad1 id=eq.0h6v.s5.b9f5578537ad from=translated src=- shape=4aeed84b vocab=1eb24591
-/
@[simp]
theorem symm_apply {τX : TextbookTopology X} {a b : X}
    (γ : Path τX a b) (t : UnitInterval) : γ.symm t = γ t.reflect :=
  rfl

/--
@isnad1 id=eq.0h5v.s5.af894c52f027 from=translated src=- shape=c80317aa vocab=6e81247f
-/
@[simp]
theorem symm_symm {τX : TextbookTopology X} {a b : X} (γ : Path τX a b) :
    γ.symm.symm = γ := by
  apply ext
  intro t
  simp

/-!
> **Entry**: topology.homotopy.path-concatenation-foundation
-/
variable {tau : TextbookTopology X}

/-- The piecewise parametrized function underlying concatenation of two paths.-/
noncomputable def transFun (gamma : Path tau a b) (delta : Path tau b c) (t : UnitInterval) : X :=
  if h : t.1 ≤ (1 / 2 : ℝ) then gamma (UnitInterval.leftDouble t h)
  else delta (UnitInterval.rightDouble t h)

/--
@isnad1 id=eq.1h8v.s6.d50691996a58 from=translated src=- shape=fc49d997 vocab=2e5743af
-/
theorem transFun_of_le (gamma : Path tau a b) (delta : Path tau b c) (t : UnitInterval)
    (h : t.1 ≤ (1 / 2 : ℝ)) :
    transFun gamma delta t = gamma (UnitInterval.leftDouble t h) := by
  rw [transFun]
  split
  · rfl
  · contradiction

/--
@isnad1 id=eq.1h8v.s6.0b8b24ced297 from=translated src=- shape=fa1eefbe vocab=0ffc792b
-/
theorem transFun_of_not_le (gamma : Path tau a b) (delta : Path tau b c) (t : UnitInterval)
    (h : ¬ t.1 ≤ (1 / 2 : ℝ)) :
    transFun gamma delta t = delta (UnitInterval.rightDouble t h) := by
  rw [transFun]
  split
  · contradiction
  · rfl

/-- The two halves of `transFun` glue continuously at their common endpoint.
@isnad1 id=continuo.0h7v.s5.1d1a54f42a64 from=translated src=- shape=29647a35 vocab=c97a3509
-/
theorem continuous_transFun (gamma : Path tau a b) (delta : Path tau b c) :
    Continuous unitInterval tau (transFun gamma delta) := by
  rw [continuous_from_unitInterval_iff]
  intro t v hv ht
  by_cases hleft : t.1 < (1 / 2 : ℝ)
  · have htle : t.1 ≤ (1 / 2 : ℝ) := le_of_lt hleft
    have hvalue := transFun_of_le gamma delta t htle
    obtain ⟨eta, heta, hgamma⟩ :=
      (continuous_from_unitInterval_iff tau gamma).mp gamma.continuous
        (UnitInterval.leftDouble t htle) v hv (hvalue ▸ ht)
    refine ⟨min ((1 / 2 : ℝ) - t.1) (eta / 2), lt_min (sub_pos.mpr hleft) (half_pos heta), ?_⟩
    intro u hu
    have habs := abs_lt.mp (lt_of_lt_of_le hu (min_le_left _ _))
    have huhalf : u.1 ≤ (1 / 2 : ℝ) := by linarith
    rw [transFun_of_le gamma delta u huhalf]
    apply hgamma
    dsimp [UnitInterval.leftDouble]
    have hsmall := abs_lt.mp (lt_of_lt_of_le hu (min_le_right _ _))
    rw [abs_lt]
    constructor <;> linarith
  · by_cases hright : (1 / 2 : ℝ) < t.1
    · have htno : ¬ t.1 ≤ (1 / 2 : ℝ) := not_le.mpr hright
      have hvalue := transFun_of_not_le gamma delta t htno
      obtain ⟨eta, heta, hdelta⟩ :=
        (continuous_from_unitInterval_iff tau delta).mp delta.continuous
          (UnitInterval.rightDouble t htno) v hv (hvalue ▸ ht)
      refine ⟨min (t.1 - (1 / 2 : ℝ)) (eta / 2),
        lt_min (sub_pos.mpr hright) (half_pos heta), ?_⟩
      intro u hu
      have habs := abs_lt.mp (lt_of_lt_of_le hu (min_le_left _ _))
      have huno : ¬ u.1 ≤ (1 / 2 : ℝ) := not_le.mpr (by linarith)
      rw [transFun_of_not_le gamma delta u huno]
      apply hdelta
      dsimp [UnitInterval.rightDouble]
      have hsmall := abs_lt.mp (lt_of_lt_of_le hu (min_le_right _ _))
      rw [abs_lt]
      constructor <;> linarith
    · have htval : t.1 = (1 / 2 : ℝ) := by linarith
      have htle : t.1 ≤ (1 / 2 : ℝ) := le_of_eq htval
      have hleftPoint : UnitInterval.leftDouble t htle = UnitInterval.one := by
        apply Subtype.ext
        dsimp [UnitInterval.leftDouble]
        linarith
      have hvalue : transFun gamma delta t = b := by
        simp only [transFun]
        split
        · rw [hleftPoint, gamma.target]
        · rename_i hbad
          exact (hbad htle).elim
      have hb : b ∈ v := hvalue ▸ ht
      obtain ⟨etaG, hetaG, hgamma⟩ :=
        (continuous_from_unitInterval_iff tau gamma).mp gamma.continuous UnitInterval.one v hv
          (gamma.target.symm ▸ hb)
      obtain ⟨etaD, hetaD, hdelta⟩ :=
        (continuous_from_unitInterval_iff tau delta).mp delta.continuous UnitInterval.zero v hv
          (delta.source.symm ▸ hb)
      refine ⟨min (etaG / 2) (etaD / 2), lt_min (half_pos hetaG) (half_pos hetaD), ?_⟩
      intro u hu
      by_cases hule : u.1 ≤ (1 / 2 : ℝ)
      · rw [transFun_of_le gamma delta u hule]
        apply hgamma
        dsimp [UnitInterval.leftDouble, UnitInterval.one]
        have hsmall := abs_lt.mp (lt_of_lt_of_le hu (min_le_left _ _))
        rw [abs_lt]
        constructor <;> linarith
      · rw [transFun_of_not_le gamma delta u hule]
        apply hdelta
        dsimp [UnitInterval.rightDouble, UnitInterval.zero]
        have hsmall := abs_lt.mp (lt_of_lt_of_le hu (min_le_right _ _))
        rw [abs_lt]
        constructor <;> linarith

/-- Concatenate paths with a common endpoint, traversing each path at twice the speed.

> **Entry**: topology.homotopy.path-concatenation-foundation-/
noncomputable def trans (gamma : Path tau a b) (delta : Path tau b c) : Path tau a c where
  toFun := transFun gamma delta
  continuous := continuous_transFun gamma delta
  source := by
    rw [show transFun gamma delta UnitInterval.zero = gamma UnitInterval.zero by
      simp [transFun, UnitInterval.leftDouble, UnitInterval.zero]]
    exact gamma.source
  target := by
    have h : ¬ (1 : ℝ) ≤ 1 / 2 := by norm_num
    rw [show transFun gamma delta UnitInterval.one = delta UnitInterval.one by
      simp only [transFun]
      split
      · rename_i hh
        exact (h (by simpa using hh)).elim
      · congr 1
        apply Subtype.ext
        norm_num [UnitInterval.rightDouble, UnitInterval.one]]
    exact delta.target

/-- On the left half, concatenation follows the first path at twice the speed.
@isnad1 id=eq.1h8v.s6.dbcce69934e8 from=translated src=- shape=49d3a06b vocab=7558d343
-/
theorem trans_apply_of_le (gamma : Path tau a b) (delta : Path tau b c) (t : UnitInterval)
    (h : t.1 ≤ (1 / 2 : ℝ)) :
    gamma.trans delta t = gamma (UnitInterval.leftDouble t h) :=
  transFun_of_le gamma delta t h

/-- On the right half, concatenation follows the second path at twice the speed.
@isnad1 id=eq.1h8v.s6.21bf5358042c from=translated src=- shape=981b7bf6 vocab=4f96f8b5
-/
theorem trans_apply_of_not_le (gamma : Path tau a b) (delta : Path tau b c) (t : UnitInterval)
    (h : ¬ t.1 ≤ (1 / 2 : ℝ)) :
    gamma.trans delta t = delta (UnitInterval.rightDouble t h) :=
  transFun_of_not_le gamma delta t h

end Path

/-- A loop based at `a` is a path which starts and ends at `a`.

> **Entry**: topology.homotopy.path-definition-foundation-/
def Loop (τX : TextbookTopology X) (a : X) := Path τX a a

/-- The constant path is the constant loop at its base point.-/
def loopRefl (τX : TextbookTopology X) (a : X) : Loop τX a :=
  Path.refl τX a

end SandronesLibrary.Topology.TextbookTopology
