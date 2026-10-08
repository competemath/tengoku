/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under MIT license as described in the file Complexitylib/Algebraic/LICENSE.
Authors: Samuel Schlesinger
-/

module
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.Asymptotics
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Defs
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Bisection.Internal.Assembly
public import Tengoku.Complexitylib.Complexitylib.Algebraic.LowerBound.Cutwidth.PathDecomposition.Endpoint

/-!
# Bag bounds from a graph cut

The prescribed-endpoint theorem on each side and the transition between
their boundaries give the finite form of Fomin and Høie's Theorem 5.
-/

@[expose] public section

namespace Algebraic.Cutwidth.PathDecomposition.Internal

open scoped Classical

theorem bisectionBound_coarse : BisectionBound (4 / 3) 0 := by
  intro W _ _ H _ regular _
  obtain ⟨S, _, hS⟩ := Finset.exists_subset_card_eq
    (s := (Finset.univ : Finset W)) (n := Fintype.card W / 2)
    (by simpa only [Finset.card_univ] using Nat.div_le_self (Fintype.card W) 2)
  have hsum := Finset.card_compl_add_card S
  refine ⟨S, by lia, by lia, ?_⟩
  have hcut : (H.cutFinset S).card ≤ H.edgeFinset.card :=
    Finset.card_le_card (fun _ he => H.mem_edgeFinset.mpr ((H.mem_cutFinset).mp he).1)
  have hedges : Fintype.card W * 3 = 2 * H.edgeFinset.card := by
    simpa only [regular.degree_eq, Finset.sum_const, Finset.card_univ, smul_eq_mul] using
      H.sum_degrees_eq_twice_card_edges
  have hcutR : ((H.cutFinset S).card : ℝ) ≤ H.edgeFinset.card := by exact_mod_cast hcut
  have hedgesR : (Fintype.card W : ℝ) * 3 = 2 * H.edgeFinset.card := by
    exact_mod_cast hedges
  linarith

end Algebraic.Cutwidth.PathDecomposition.Internal
