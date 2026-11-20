import Tengoku.Erdos64.Erdos64.TwoPortQuotient

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-!
The ordinary terminal quotient asks that no internal vertex touch both
terminals.  In the balanced two-port configuration the articulation/root can
be a common neighbor.  This file records the sharper degree estimate needed
there: a common neighbor of degree at least four survives identification,
because only the two terminal incidences can merge.
-/

theorem terminalQuotient_minDegree_ge_three_of_common_degree_ge_four
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] {a b : V}
    (hmin : G.minDegree ≥ 3) (_hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hcommon4 : ∀ z, z ≠ a → z ≠ b →
      (G.Adj a z ∧ G.Adj b z) → 4 ≤ G.degree z) :
    (terminalQuotientGraph G a b).minDegree ≥ 3 := by
  classical
  letI : DecidableRel (terminalQuotientGraph G a b).Adj :=
    quotient_decidableRel G a b
  letI : Nonempty (QuotientVertex a b) := ⟨none⟩
  apply SimpleGraph.le_minDegree_of_forall_le_degree
    (terminalQuotientGraph G a b) 3
  intro q
  cases q with
  | none =>
      rw [quotient_root_degree]
      let T := {v : V // v ≠ a ∧ v ≠ b ∧ (G.Adj a v ∨ G.Adj b v)}
      let f : G.neighborSet a → T := fun x =>
        ⟨x.1, by
          have hax : G.Adj a x.1 := (G.mem_neighborSet a x.1).mp x.2
          have hxa : x.1 ≠ a := by
            intro h
            exact G.loopless.irrefl a (by simpa [h] using hax)
          have hxb : x.1 ≠ b := by
            intro h
            exact hnadj (by simpa [h] using hax)
          exact ⟨hxa, hxb, Or.inl hax⟩⟩
      have hf : Function.Injective f := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : T => z.1) hxy
      have hcard : Fintype.card (G.neighborSet a) ≤ Fintype.card T :=
        Fintype.card_le_of_injective f hf
      rw [SimpleGraph.card_neighborSet_eq_degree] at hcard
      exact (degree_ge_three_of_minDegree_ge_three G hmin a).trans hcard
  | some v =>
      let fFull : G.neighborSet v.1 →
          (terminalQuotientGraph G a b).neighborSet (some v) := fun x =>
        if hx : x.1 = a ∨ x.1 = b then
          ⟨none, by
            rcases hx with hxa | hxb
            · exact Or.inl (by simpa [hxa] using x.2)
            · exact Or.inr (by simpa [hxb] using x.2)⟩
        else
          ⟨some ⟨x.1, by
            exact ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩⟩,
            x.2⟩
      have hfFull : ∀ hnot : ¬ (G.Adj a v.1 ∧ G.Adj b v.1),
          Function.Injective fFull := by
        intro hnot x y hxy
        by_cases hx : x.1 = a ∨ x.1 = b
        · by_cases hy : y.1 = a ∨ y.1 = b
          · rcases hx with hxa | hxb <;> rcases hy with hya | hyb
            · apply Subtype.ext
              exact hxa.trans hya.symm
            · exfalso
              apply hnot
              have hax : G.Adj a v.1 := by
                simpa [hxa] using x.2.symm
              have hby : G.Adj b v.1 := by
                simpa [hyb] using y.2.symm
              exact ⟨hax, hby⟩
            · exfalso
              apply hnot
              have hay : G.Adj a v.1 := by
                simpa [hya] using y.2.symm
              have hbx : G.Adj b v.1 := by
                simpa [hxb] using x.2.symm
              exact ⟨hay, hbx⟩
            · apply Subtype.ext
              exact hxb.trans hyb.symm
          · have hval := congrArg Subtype.val hxy
            simp [fFull, hx, hy] at hval
        · by_cases hy : y.1 = a ∨ y.1 = b
          · have hval := congrArg Subtype.val hxy
            simp [fFull, hx, hy] at hval
          · have hval := congrArg Subtype.val hxy
            simp [fFull, hx, hy] at hval
            apply Subtype.ext
            exact hval
      have hdeg : 3 ≤ G.degree v.1 :=
        degree_ge_three_of_minDegree_ge_three G hmin v.1
      have hcardN : Fintype.card (G.neighborSet v.1) = G.degree v.1 :=
        SimpleGraph.card_neighborSet_eq_degree G v.1
      by_cases hboth : G.Adj v.1 a ∧ G.Adj v.1 b
      · let S := {x : G.neighborSet v.1 // x.1 ≠ a}
        let f : S → (terminalQuotientGraph G a b).neighborSet (some v) :=
          fun x =>
            if hx : x.1.1 = a ∨ x.1.1 = b then
              ⟨none, by
                rcases hx with hxa | hxb
                · exact Or.inl (by simpa [hxa] using x.1.2)
                · exact Or.inr (by simpa [hxb] using x.1.2)⟩
            else
              ⟨some ⟨x.1.1, by
                exact ⟨fun h => hx (Or.inl h), fun h => hx (Or.inr h)⟩⟩,
                x.1.2⟩
        have hf : Function.Injective f := by
          intro x y hxy
          by_cases hx : x.1.1 = b
          · by_cases hy : y.1.1 = b
            · apply Subtype.ext
              apply Subtype.ext
              exact hx.trans hy.symm
            · have hval := congrArg Subtype.val hxy
              exfalso
              simpa [f, hx, hy, x.2, y.2] using hval
          · by_cases hy : y.1.1 = b
            · have hval := congrArg Subtype.val hxy
              exfalso
              simpa [f, hx, hy, x.2, y.2] using hval
            · have hval := congrArg Subtype.val hxy
              simp [f, hx, hy, x.2, y.2] at hval
              apply Subtype.ext
              apply Subtype.ext
              exact hval
        have hcardS : Fintype.card S ≤
            Fintype.card ((terminalQuotientGraph G a b).neighborSet (some v)) :=
          Fintype.card_le_of_injective f hf
        rw [SimpleGraph.card_neighborSet_eq_degree] at hcardS
        have hcardS_eq : Fintype.card S =
            Fintype.card (G.neighborSet v.1) -
              Fintype.card {x : G.neighborSet v.1 // x.1 = a} := by
          simpa [S] using
            (Fintype.card_subtype_compl
              (fun x : G.neighborSet v.1 => x.1 = a))
        have hcardA : Fintype.card {x : G.neighborSet v.1 // x.1 = a} = 1 := by
          apply (Fintype.card_eq_one_iff.mpr)
          refine ⟨⟨⟨a, (G.mem_neighborSet v.1 a).mpr hboth.1⟩, rfl⟩, ?_⟩
          intro x
          apply Subtype.ext
          apply Subtype.ext
          exact x.2
        rw [hcardS_eq, hcardA, hcardN] at hcardS
        have hhigh : 4 ≤ G.degree v.1 := by
          apply hcommon4 v.1 v.2.1 v.2.2
          exact ⟨hboth.1.symm, hboth.2.symm⟩
        omega
      · have hnot : ¬ (G.Adj a v.1 ∧ G.Adj b v.1) := by
          intro h
          exact hboth ⟨h.1.symm, h.2.symm⟩
        have hcardFull : Fintype.card (G.neighborSet v.1) ≤
            Fintype.card ((terminalQuotientGraph G a b).neighborSet (some v)) :=
          Fintype.card_le_of_injective fFull (hfFull hnot)
        rw [SimpleGraph.card_neighborSet_eq_degree] at hcardFull
        have hqdeg :
            Fintype.card ((terminalQuotientGraph G a b).neighborSet (some v)) =
              (terminalQuotientGraph G a b).degree (some v) :=
          SimpleGraph.card_neighborSet_eq_degree _ _
        rw [hqdeg] at hcardFull
        exact hdeg.trans hcardFull

/-- Minimality still forces a dyadic quotient cycle when any common internal
neighbor of the terminals has degree at least four.-/
theorem MinimalCounterexample.terminalQuotient_hasPowerOfTwoCycle_of_common_degree_ge_four
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (M : MinimalCounterexample G) {a b : V}
    (hab : a ≠ b) (hnadj : ¬ G.Adj a b)
    (hcommon4 : ∀ z, z ≠ a → z ≠ b →
      (G.Adj a z ∧ G.Adj b z) → 4 ≤ G.degree z) :
    HasPowerOfTwoCycle (terminalQuotientGraph G a b) := by
  classical
  letI : DecidableRel (terminalQuotientGraph G a b).Adj :=
    quotient_decidableRel G a b
  by_contra hno
  have hsmall :
      IsStrictlySmallerCounterexample G (terminalQuotientGraph G a b) := by
    refine ⟨⟨terminalQuotient_minDegree_ge_three_of_common_degree_ge_four
        M.isCounterexample.1 hab hnadj hcommon4, hno⟩, ?_⟩
    exact terminalQuotient_card_lt hab
  exact M.not_exists_strictly_smaller hsmall

end Erdos64
