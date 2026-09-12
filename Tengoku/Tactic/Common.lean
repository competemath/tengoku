/-
Copyright (c) 2023 Kim Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

-- First import Aesop, Qq, and Plausible
module  -- shake: keep-all, shake: keep-downstream

public import Tengoku.Tactic.Aesop
public import Tengoku.Meta.Qq
public import Tengoku.Testing.Random

-- Import common Batteries tactics and commands
public import Tengoku.Std.Tactic.Basic
public import Tengoku.Std.Tactic.Case
public import Tengoku.Std.Tactic.HelpCmd
public import Tengoku.Std.Tactic.Alias
public import Tengoku.Std.Tactic.GeneralizeProofs

-- Import Batteries code actions
public import Tengoku.Std.CodeAction

-- Import syntax for leansearch
public import Tengoku.Search.LeanSearchClient

-- Import Mathlib-specific linters.
public import Tengoku.Tactic.Linter.Lint

-- Now import all tactics defined in Mathlib that do not require theory files.
public import Tengoku.Tactic.ApplyCongr
-- ApplyFun imports `Mathlib/Order/Monotone/Basic.lean`
-- import Mathlib.Tactic.ApplyFun
public import Tengoku.Tactic.ApplyAt
public import Tengoku.Tactic.ApplyWith
public import Tengoku.Tactic.Basic
public import Tengoku.Tactic.ByCases
public import Tengoku.Tactic.ByContra
public import Tengoku.Tactic.CasesM
public import Tengoku.Tactic.Check
public import Tengoku.Tactic.Choose
public import Tengoku.Tactic.ClearExclamation
public import Tengoku.Tactic.ClearExcept
public import Tengoku.Tactic.Clear_
public import Tengoku.Tactic.ClickSuggestions
public import Tengoku.Tactic.Coe
public import Tengoku.Tactic.CongrExclamation
public import Tengoku.Tactic.CongrM
public import Tengoku.Tactic.Constructor
public import Tengoku.Tactic.Contrapose
public import Tengoku.Tactic.Conv
public import Tengoku.Tactic.Convert
public import Tengoku.Tactic.DefEqAbuse
public import Tengoku.Tactic.DefEqTransformations
public import Tengoku.Tactic.DeprecateTo
public import Tengoku.Tactic.DepRewrite
public import Tengoku.Tactic.DSimpPercent
public import Tengoku.Tactic.ErwQuestion
public import Tengoku.Tactic.Eqns
public import Tengoku.Tactic.ExistsI
public import Tengoku.Tactic.ExtractGoal
public import Tengoku.Tactic.FailIfNoProgress
public import Tengoku.Tactic.Find
public import Tengoku.Tactic.FunProp
public import Tengoku.Tactic.GCongr
public import Tengoku.Tactic.GRewrite
public import Tengoku.Tactic.GrindAttrs
public import Tengoku.Tactic.GuardGoalNums
public import Tengoku.Tactic.GuardHypNums
public import Tengoku.Tactic.HigherOrder
public import Tengoku.Tactic.Hint
public import Tengoku.Tactic.InferParam
public import Tengoku.Tactic.Inhabit
public import Tengoku.Tactic.IrreducibleDef
public import Tengoku.Tactic.Lift
public import Tengoku.Tactic.Linter
public import Tengoku.Tactic.MkIffOfInductiveProp
-- NormNum imports `Algebra.Order.Invertible`, `Data.Int.Basic`, `Data.Nat.Cast.Commute`
-- import Mathlib.Tactic.NormNum.Basic
public import Tengoku.Tactic.NthRewrite
public import Tengoku.Tactic.Observe
public import Tengoku.Tactic.OfNat
-- `positivity` imports `Data.Nat.Factorial.Basic`, but hopefully this can be rearranged.
-- import Mathlib.Tactic.Positivity
public import Tengoku.Tactic.Push
public import Tengoku.Tactic.RSuffices
public import Tengoku.Tactic.Recover
public import Tengoku.Tactic.Relation.Rfl
public import Tengoku.Tactic.Rename
public import Tengoku.Tactic.RenameBVar
public import Tengoku.Tactic.Says
public import Tengoku.Tactic.ScopedNS
public import Tengoku.Tactic.Set
public import Tengoku.Tactic.SimpIntro
public import Tengoku.Tactic.SimpRw
public import Tengoku.Tactic.Simproc.ExistsAndEq
public import Tengoku.Tactic.Simps
public import Tengoku.Tactic.SplitIfs
public import Tengoku.Tactic.Spread
public import Tengoku.Tactic.Subsingleton
public import Tengoku.Tactic.Substs
public import Tengoku.Tactic.SuccessIfFailWithMsg
public import Tengoku.Tactic.SudoSetOption
public import Tengoku.Tactic.SwapVar
public import Tengoku.Tactic.Tauto
public import Tengoku.Tactic.ToFun
public import Tengoku.Tactic.TermCongr
-- TFAE imports `Mathlib/Data/List/TFAE.lean` and thence `Mathlib/Data/List/Basic.lean`.
-- import Mathlib.Tactic.TFAE
public import Tengoku.Tactic.ToExpr
public import Tengoku.Tactic.ToLevel
public import Tengoku.Tactic.Trace
public import Tengoku.Tactic.UnsetOption
public import Tengoku.Tactic.Use
public import Tengoku.Tactic.Variable
public import Tengoku.Tactic.Widget.Calc
public import Tengoku.Tactic.Widget.CongrM
public import Tengoku.Tactic.Widget.Conv
public import Tengoku.Tactic.Widget.LibraryRewrite
public import Tengoku.Tactic.WLOG
public import Tengoku.Util.CountHeartbeats
public import Tengoku.Util.PrintSorries
public import Tengoku.Util.TransImports
public import Tengoku.Util.WhatsNew
public import Lean.Elab.Tactic.Try
public meta import Lean.Meta.Tactic.Try.Collect

/-!
# Common tactics, linters, and utilities

This file imports all tactics which do not have significant theory imports,
and hence can be imported very low in the theory import hierarchy,
thereby making tactics widely available without needing specific imports.

We include some commented out imports here, with an explanation of their theory requirements,
to save some time for anyone wondering why they are not here.

We also import theory-free linters, commands, and utilities which are useful to have low in the
import hierarchy.
-/

public meta section

/-!
### Register tactics with `hint`. Tactics with larger priority run first.
-/

section Hint

register_hint 1000 trivial
register_hint 1000 split
register_hint 1000 intro
register_hint 1000 decide
register_hint 800 simp_all?
register_hint 600 exact?
register_hint 500 tauto
register_hint 200 grind
register_hint 200 omega
register_hint 200 fun_prop
register_hint 80 aesop

end Hint

/-!
### Register tactics with `try?`. Tactics with larger priority run first.
-/

section Try

register_try?_tactic (priority := 500) tauto
register_try?_tactic (priority := 80) aesop
register_try?_tactic (priority := 200) fun_prop

end Try
