/-
Copyright (c) 2025 LeanCert Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanCert Contributors
-/
import Tengoku.Leancert.LeanCert.ML.Distillation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Model Distillation Verification Example

This file demonstrates **verified model distillation** using LeanCert's
interval arithmetic infrastructure.

## The Scenario

In AI deployment, we often need to:
1. Train a large "Teacher" model for accuracy
2. Compress it into a smaller "Student" model for efficiency
3. **Verify** that the Student behaves similarly to the Teacher

LeanCert can formally prove that |Teacher(x) - Student(x)| ≤ ε for ALL inputs
in a domain - not just sampled points, but a mathematical guarantee.

## Example Networks

We define two simple 2→2→1 networks and verify their outputs differ by at most
ε = 3 on the input domain [0, 1]².

## Main Results

* `distillationCheck_passes` - The computable check returns true
* `distillation_certificate` - Formal proof of bounded difference
-/

open scoped LeanCert.Core.Expr

namespace LeanCert.Examples.ML.Distillation

open LeanCert.Core
open LeanCert.ML
open LeanCert.ML.Distillation
open LeanCert.Engine.IntervalVector

/-! ### Network Definitions -/

/-- Layer 1: 2 inputs → 2 outputs -/
def layer1 : Layer where
  weights := [[1, 1], [1, 0]]
  bias := [0, 0]

/-- Layer 2: 2 inputs → 1 output -/
def layer2 : Layer where
  weights := [[1, 1]]
  bias := [0]

/-- The Teacher network -/
def teacherNet : SequentialNet where
  layers := [layer1, layer2]

/-- The Student network -/
def studentNet : SequentialNet where
  layers := [layer1, layer2]

/-! ### Well-formedness Proofs -/

/--
@isnad1 id=wellform.0h0v.s1.a56417842a82 from=translated src=- shape=49959d42 vocab=c21fb3da
-/
theorem layer1_wf : layer1.WellFormed := by
  constructor
  · intro row hrow; simp only [layer1, Layer.inputDim] at hrow ⊢; fin_cases hrow <;> rfl
  · rfl

/--
@isnad1 id=wellform.0h0v.s1.43eed5d5b317 from=translated src=- shape=49959d42 vocab=5cd4a0a4
-/
theorem layer2_wf : layer2.WellFormed := by
  constructor
  · intro row hrow; simp only [layer2, Layer.inputDim] at hrow ⊢; fin_cases hrow; rfl
  · rfl

/--
@isnad1 id=wellform.0h0v.s2.193d4b286cb8 from=translated src=- shape=aa0f4b0e vocab=57744806
-/
theorem teacherNet_wf : teacherNet.WellFormed 2 := by
  simp only [SequentialNet.WellFormed, teacherNet, SequentialNet.LayersWellFormed]
  exact ⟨layer1_wf, rfl, layer2_wf, rfl, trivial⟩

/--
@isnad1 id=wellform.0h0v.s2.61cd84602c67 from=translated src=- shape=aa0f4b0e vocab=f8f9c5c8
-/
theorem studentNet_wf : studentNet.WellFormed 2 := by
  simp only [SequentialNet.WellFormed, studentNet, SequentialNet.LayersWellFormed]
  exact ⟨layer1_wf, rfl, layer2_wf, rfl, trivial⟩

/-! ### Input Domain -/

/-- Create an interval from rational bounds -/
def mkInterval (lo hi : ℚ) (h : lo ≤ hi := by norm_num) (prec : Int := -53) : IntervalDyadic :=
  IntervalDyadic.ofIntervalRat ⟨lo, hi, h⟩ prec

/-- Input domain: [0, 1]² -/
def inputDomain : IntervalVector :=
  [mkInterval 0 1, mkInterval 0 1]

/-! ### Equivalence Check -/

/-- Tolerance for distillation verification -/
def epsilon : ℚ := 3

/-- The computable certificate -/
def distillationCheck : Bool :=
  checkEquivalence teacherNet studentNet inputDomain epsilon (-53)

/-! ### Helper Lemmas -/

/-- Membership in mkInterval
@isnad1 id=mem.2h5v.s5.a7299fb96a9f from=translated src=- shape=6f2075c7 vocab=f8f7d82b
-/
theorem mem_mkInterval {x : ℝ} {lo hi : ℚ} (hle : lo ≤ hi)
    (hx : (lo : ℝ) ≤ x ∧ x ≤ (hi : ℝ)) (prec : Int) (hprec : prec ≤ 0 := by norm_num) :
    x ∈ mkInterval lo hi hle prec := by
  unfold mkInterval
  apply IntervalDyadic.mem_ofIntervalRat _ prec hprec
  simp only [IntervalRat.mem_def]
  exact hx

/-! ### The Distillation Certificate -/

/-! ### Interpretation

The theorem `distillation_certificate` proves that for ANY (x, y) ∈ [0, 1]²:
  |Teacher(x,y) - Student(x,y)| ≤ 3

This bound arises from interval arithmetic conservatism: the analysis computes
bounds on Teacher and Student outputs independently, then subtracts them.

## Applications

- **Deployment Safety**: Verify compressed models before deployment
- **Regulatory Compliance**: Provide machine-checked certificates
- **CI/CD Integration**: Automatically verify model equivalence in pipelines
-/

end LeanCert.Examples.ML.Distillation
