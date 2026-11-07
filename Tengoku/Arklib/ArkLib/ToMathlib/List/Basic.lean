/-
Copyright (c) 2024-2025 ArkLib Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: František Silváši, Julian Sutherland, Ilia Vlasov
-/
module

/-!
# ArkLib.ToMathlib.List.Basic

Definitions and results for this component of ArkLib.
-/

@[expose] public section

/--
@isnad1 id=eq.1h2v.s4.8d029f2ff135 from=translated src=- shape=0ff77681 vocab=63129923
-/
@[simp, grind =]
theorem List.take_one_eq_head.{u} {α : Type u} {l : List α} (h : l ≠ []) :
    l.take 1 = [l.head h] := by grind [cases List]
