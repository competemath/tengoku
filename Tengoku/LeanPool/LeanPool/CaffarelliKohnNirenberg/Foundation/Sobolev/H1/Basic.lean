/-
Copyright (c) 2026 Scott Armstrong, Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Vlad Vicol
-/
module

public import Tengoku.LeanPool.LeanPool.CaffarelliKohnNirenberg.Foundation.Sobolev.W1p.Basic

/-!
# Representative-level `H¹`

Adapted from PDEFoundation (EllipticRegularity, 2026) with the author's
permission. This port is the exact `p = 2` facade over the independent CKN
representative-level `W1pFunction` API.

## Main definitions

* `MemL2On` and `GradMemL2On`: scalar and coordinatewise `L²` membership.
* `H1Function`: a concrete scalar representative with a chosen weak gradient.

## Main results

* `H1Function.restrict`: restriction to an open subset.
* The conversion lemmas preserve values and gradients definitionally.
-/

@[expose] public section

open scoped ENNReal

namespace CKN

/-- Scalar `L²` membership on a restricted domain. -/
abbrev MemL2On {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  MemLpOn U (2 : ℝ≥0∞) u

/-- Coordinatewise gradient `L²` membership on a restricted domain. -/
abbrev GradMemL2On {d : ℕ}
    (U : Set (Vec d)) (Du : Vec d → Vec d) : Prop :=
  GradMemLpOn U (2 : ℝ≥0∞) Du

/-- A concrete scalar representative and a chosen coordinate weak gradient in
`L²(U)`. -/
structure H1Function {d : ℕ} (U : Set (Vec d)) where
  /-- Chosen scalar representative of the H¹ function. -/
  toFun : Vec d → ℝ
  /-- Chosen weak gradient of the H¹ representative. -/
  grad : Vec d → Vec d
  memL2 : MemL2On U toFun
  gradMemL2 : GradMemL2On U grad
  hasWeakGradient : HasWeakGradientOn U toFun grad

instance {d : ℕ} {U : Set (Vec d)} :
    CoeFun (H1Function U) (fun _ => Vec d → ℝ) where
  coe u := u.toFun

/-- Representative-level membership of a concrete function in `H¹(U)`. -/
def MemH1 {d : ℕ} (U : Set (Vec d)) (u : Vec d → ℝ) : Prop :=
  ∃ v : H1Function U, v.toFun = u

namespace H1Function

/--
@isnad1 id=eq.2h4v.s5.29bf9c672118 from=translated src=- shape=cd1927ea vocab=be072730
-/
@[ext]
theorem ext {d : ℕ} {U : Set (Vec d)} {u v : H1Function U}
    (htoFun : u.toFun = v.toFun) (hgrad : u.grad = v.grad) :
    u = v := by
  cases u
  cases v
  cases htoFun
  cases hgrad
  rfl

/-- The coordinate weak-derivative identity stored in an `H1Function`.
@isnad1 id=hasweakp.0h4v.s4.68baeea2f818 from=translated src=- shape=25fbb6ea vocab=009d7261
-/
theorem hasWeakPartialDerivOn {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (i : Fin d) :
    HasWeakPartialDerivOn U i u.toFun (fun x => u.grad x i) :=
  u.hasWeakGradient i

/-- The `i`th chosen gradient component belongs to `L²(U)`.
@isnad1 id=meml2on.0h4v.s4.aaeb1ce01362 from=translated src=- shape=56f06124 vocab=73e1aec9
-/
theorem grad_memL2 {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (i : Fin d) :
    MemL2On U (fun x => u.grad x i) :=
  u.gradMemL2 i

/-- The underlying representative belongs to representative-level `H¹(U)`.
@isnad1 id=memh1.0h3v.s4.853abf2eae78 from=translated src=- shape=463b29c3 vocab=6cc1faf1
-/
theorem memH1 {d : ℕ} {U : Set (Vec d)} (u : H1Function U) :
    MemH1 U u.toFun :=
  ⟨u, rfl⟩

/-- Regard an `H1Function` as the corresponding `W1pFunction` at `p = 2`. -/
def toW1pFunction {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) : W1pFunction U (2 : ℝ≥0∞) where
  toFun := u.toFun
  grad := u.grad
  memLp := u.memL2
  gradMemLp := u.gradMemL2
  hasWeakGradient := u.hasWeakGradient

/--
@isnad1 id=eq.0h3v.s5.562917f89e35 from=translated src=- shape=f457a166 vocab=dad5a19f
-/
@[simp]
theorem toW1pFunction_toFun {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.toFun = u.toFun :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.ec810088fb82 from=translated src=- shape=86a3413d vocab=225309ab
-/
@[simp]
theorem toW1pFunction_grad {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.grad = u.grad :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.cd96a2675b20 from=translated src=- shape=6aeb49d0 vocab=dad5a19f
-/
@[simp]
theorem toW1pFunction_apply {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) (x : Vec d) :
    u.toW1pFunction x = u x :=
  rfl

end H1Function

namespace W1pFunction

/-- Regard a `W1pFunction` at `p = 2` as the corresponding `H1Function`. -/
def toH1Function {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) : H1Function U where
  toFun := u.toFun
  grad := u.grad
  memL2 := u.memLp
  gradMemL2 := u.gradMemLp
  hasWeakGradient := u.hasWeakGradient

/--
@isnad1 id=eq.0h3v.s5.4feb331ac408 from=translated src=- shape=b4329834 vocab=a1b69dab
-/
@[simp]
theorem toH1Function_toFun {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.toFun = u.toFun :=
  rfl

/--
@isnad1 id=eq.0h3v.s5.5f8a3f24a3e5 from=translated src=- shape=ce540072 vocab=377de58f
-/
@[simp]
theorem toH1Function_grad {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.grad = u.grad :=
  rfl

/--
@isnad1 id=eq.0h4v.s5.dbf83ef01d45 from=translated src=- shape=039f06e3 vocab=a1b69dab
-/
@[simp]
theorem toH1Function_apply {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) (x : Vec d) :
    u.toH1Function x = u x :=
  rfl

end W1pFunction

namespace H1Function

/--
@isnad1 id=eq.0h3v.s4.e2b66313f866 from=translated src=- shape=b3ee8132 vocab=5cff6210
-/
@[simp]
theorem toH1Function_toW1pFunction {d : ℕ} {U : Set (Vec d)}
    (u : H1Function U) :
    u.toW1pFunction.toH1Function = u := by
  apply H1Function.ext <;> rfl

/-- Restrict an `H1Function` to an open subset. -/
def restrict {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    H1Function V :=
  (u.toW1pFunction.restrict hVOpen hVU).toH1Function

/--
@isnad1 id=eq.2h4v.s5.f5398a52ebf1 from=translated src=- shape=e1605c4b vocab=a1be57e4
-/
@[simp]
theorem restrict_toFun {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    (u.restrict hVOpen hVU).toFun = u.toFun :=
  rfl

/--
@isnad1 id=eq.2h4v.s6.238d504034e5 from=translated src=- shape=491249a2 vocab=6fc70aec
-/
@[simp]
theorem restrict_grad {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U) :
    (u.restrict hVOpen hVU).grad = u.grad :=
  rfl

/--
@isnad1 id=eq.2h5v.s6.b1b48899606b from=translated src=- shape=51dff7a1 vocab=a1be57e4
-/
@[simp]
theorem restrict_apply {d : ℕ} {U V : Set (Vec d)}
    (u : H1Function U) (hVOpen : IsOpen V) (hVU : V ⊆ U)
    (x : Vec d) :
    u.restrict hVOpen hVU x = u x :=
  rfl

end H1Function

namespace W1pFunction

/--
@isnad1 id=eq.0h3v.s5.c216c5f05ac8 from=translated src=- shape=9d557ade vocab=787ffe6a
-/
@[simp]
theorem toW1pFunction_toH1Function {d : ℕ} {U : Set (Vec d)}
    (u : W1pFunction U (2 : ℝ≥0∞)) :
    u.toH1Function.toW1pFunction = u := by
  apply W1pFunction.ext <;> rfl

end W1pFunction

end CKN
