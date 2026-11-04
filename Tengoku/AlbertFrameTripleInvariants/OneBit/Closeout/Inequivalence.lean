import Tengoku.AlbertFrameTripleInvariants.OneBit.Closeout.Tensor

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# No automorphism carries the first configuration to any relabelling of the second

`tensor_same`: the 27 raw triple traces of the two configurations agree (recovered from
the historical centred ledger equality by adding back the pair terms). `pair_same`: all
pair traces between distinct frames agree, in both orders. `not_equivalent`: if an
automorphism g together with a permutation σ of the frames and permutations πᵣ within
frames carried the first family of nine idempotents to the second, the raw triple tensor
of the first configuration would be fixed by (σ, π); `tensor_stabilizer_trivial` then
forces σ and every πᵣ to be the identity, so g would transport the three encoders, which
`AlbertLean.noUnitalProductAutomorphismTransports` refutes from the two detector values.
The detector is used only after the relabelling has been eliminated.
-/

namespace OneBit.Closeout
open AlbertLean

/-- The existing centred ledger equality implies equality of the raw tensor:
C₀ = T − (P + Q + R)/3 + 2/9.
@isnad1 id=eq.0h1v.s4.c27c06173b76 from=translated src=- shape=aa12bdc6 vocab=e86cee53
-/
theorem tensor_same (a : Fin 3 → Fin 3) : tensor witnessTheta1 a = tensor witnessThetaM a := by
  have hc := congrFun (congrFun (congrFun (congrArg Ledger.C0 witnessSameLedger)
    (a 0)) (a 1)) (a 2)
  have hp := congrFun (congrFun witnessSameP (a 0)) (a 1)
  have hq := congrFun (congrFun witnessSameQ (a 1)) (a 2)
  have hr := congrFun (congrFun witnessSameR (a 2)) (a 0)
  change tensor witnessTheta1 a -
    ((ledger witnessTheta1).P (a 0) (a 1) + (ledger witnessTheta1).Q (a 1) (a 2) +
      (ledger witnessTheta1).R (a 2) (a 0)) / 3 + 2/9 =
    tensor witnessThetaM a -
    ((ledger witnessThetaM).P (a 0) (a 1) + (ledger witnessThetaM).Q (a 1) (a 2) +
      (ledger witnessThetaM).R (a 2) (a 0)) / 3 + 2/9 at hc
  rw [hp,hq,hr] at hc
  linarith

/--
@isnad1 id=eq.0h4v.s9.e872e91f5306 from=translated src=- shape=4b3e9334 vocab=28a23bd2
-/
theorem tripleForm_invariant (g : JordanAut) (x y z : Coord) :
    tripleForm (g x) (g y) (g z) = tripleForm x y z := by
  unfold tripleForm
  rw [← g.map_circle, traceForm_invariant]

/--
@isnad1 id=eq.1h4v.s5.5abd5c4396f4 from=translated src=- shape=6566cacc vocab=f12b3a2a
-/
theorem pair_same (r s i j : Fin 3) (hrs : r ≠ s) :
    pair witnessTheta1 r s i j = pair witnessThetaM r s i j := by
  have hp := congrFun (congrFun witnessSameP i) j
  have hq := congrFun (congrFun witnessSameQ i) j
  have hr := congrFun (congrFun witnessSameR i) j
  have hpt := congrFun (congrFun witnessSameP j) i
  have hqt := congrFun (congrFun witnessSameQ j) i
  have hrt := congrFun (congrFun witnessSameR j) i
  fin_cases r <;> fin_cases s <;> try contradiction
  · exact hp
  · exact (traceForm_symmetric _ _).trans (hrt.trans (traceForm_symmetric _ _))
  · exact (traceForm_symmetric _ _).trans (hpt.trans (traceForm_symmetric _ _))
  · exact hq
  · exact hr
  · exact (traceForm_symmetric _ _).trans (hqt.trans (traceForm_symmetric _ _))

/-- No arbitrary unital rational-linear Jordan automorphism carries the first
nine projectors to any frame/outcome relabelling of the second nine.
@isnad1 id=not.0h0v.s8.648f3ceb75ad from=translated src=- shape=971334c7 vocab=923a9257
-/
theorem not_equivalent :
    ¬ ∃ (g : JordanAut) (σ : Equiv.Perm (Fin 3)) (π : Fin 3 → Equiv.Perm (Fin 3)),
      ∀ r i, g (family witnessTheta1 r i) = family witnessThetaM (σ r) (π r i) := by
  rintro ⟨g,σ,π,hg⟩
  have ht (a : Fin 3 → Fin 3) : tensor witnessTheta1 a = tensor witnessTheta1 (relabel σ π a) := by
    rw [tensor_same (relabel σ π a), tensor_relabel]
    rw [← hg 0 (a 0), ← hg 1 (a 1), ← hg 2 (a 2)]
    exact (tripleForm_invariant g _ _ _).symm
  obtain ⟨hs,hπ⟩ := tensor_stabilizer_trivial σ π ht
  have he (r : Fin 3) : g (AlbertLean.encoder witnessTheta1 r) = AlbertLean.encoder witnessThetaM r := by
    calc
      _ = g (family witnessTheta1 r 2 - family witnessTheta1 r 0) := by
        simp only [family]
        rw [(witnessTheta1Lawful r).2.2.2.2]
      _ = family witnessThetaM r 2 - family witnessThetaM r 0 := by
        change g.toLinearEquiv (_ - _) = _
        rw [map_sub]
        change g (family witnessTheta1 r 2) - g (family witnessTheta1 r 0) = _
        rw [hg, hg, hs, hπ r]
        rfl
      _ = _ := (witnessThetaMLawful r).2.2.2.2
  exact noUnitalProductAutomorphismTransports ⟨g, he 0, he 1, he 2⟩

end OneBit.Closeout
