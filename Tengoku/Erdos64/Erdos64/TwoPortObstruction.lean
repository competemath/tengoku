import Tengoku.Erdos64.Erdos64.Arithmetic
import Tengoku.Erdos64.Erdos64.RootDeletedNoDyadicTransfer
import Tengoku.Erdos64.Erdos64.RootDeletedTwoPortExtraction
import Tengoku.Erdos64.Erdos64.TerminalSpectrumNoDyadic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Erdos64

universe u

/-- The internal graph of a root-deleted component has no dyadic simple cycle
when the ambient graph has no dyadic simple cycle.
@isnad1 id=not.1h4v.s7.c73ab82fb743 from=translated src=- shape=1c561b8e vocab=92e92d36
-/
theorem rootDeletedComponent_internal_noPowerOfTwoCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno : ¬ HasPowerOfTwoCycle G) (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent) :
    ¬ HasPowerOfTwoCycle ((G.induce {v : V | v ≠ r}).induce C.supp) := by
  apply not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle
  exact not_hasPowerOfTwoCycle_induce_of_not_hasPowerOfTwoCycle hno

/-- A two-port root-deleted component has no internal dyadic simple cycle.
@isnad1 id=not.2h4v.s7.4bc139e3a36e from=translated src=- shape=8aa01469 vocab=a00c3b2e
-/
theorem twoPortComponent_internal_noPowerOfTwoCycle
    {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (hno : ¬ HasPowerOfTwoCycle G) (r : V)
    (C : (G.induce {v : V | v ≠ r}).ConnectedComponent)
    (_hports : (rootDeletedComponentAttachments G r C).card = 2) :
    ¬ HasPowerOfTwoCycle ((G.induce {v : V | v ≠ r}).induce C.supp) :=
  rootDeletedComponent_internal_noPowerOfTwoCycle hno r C

/-- With both root edges present, an internal simple path cannot have length
`2^k - 2`, since the two edges complete it to a dyadic simple cycle.
@isnad1 id=ne.8h7v.s6.b5487d8bc909 from=translated src=- shape=3cbe5f55 vocab=cbc4e1e3
-/
theorem twoPort_path_length_ne_pow_two_sub_two
    {V : Type u} {G : SimpleGraph V} {r a b : V}
    {p : G.Walk a b}
    (hno : ¬ HasPowerOfTwoCycle G)
    (hp : p.IsPath)
    (hroot : r ∉ p.support)
    (hra : G.Adj r a)
    (hrb : G.Adj r b)
    (hab : a ≠ b)
    (hlong : 1 < p.length)
    {k : ℕ} (hk : 2 ≤ k) :
    p.length ≠ 2 ^ k - 2 := by
  intro hlen
  have hnot := terminal_path_length_not_dyadic_of_no_powerOfTwoCycle
    hno hp hroot hra hrb hab hlong hk
  apply hnot
  rw [hlen]
  have hpow : 4 ≤ 2 ^ k := four_le_pow_two hk
  omega

/-- A fresh root edge extends an internal path of length `2^k - 2` to a path
of length `2^k - 1`.
@isnad1 id=ex.5h7v.s7.01f7644c02c9 from=translated src=- shape=fb999b4f vocab=8e7f9977
-/
theorem root_edge_completion_path_of_pow_two_sub_two
    {V : Type u} {G : SimpleGraph V} {r a b : V}
    {p : G.Walk a b}
    (hp : p.IsPath)
    (hroot : r ∉ p.support)
    (hra : G.Adj r a)
    {k : ℕ} (hk : 2 ≤ k)
    (hlen : p.length = 2 ^ k - 2) :
    ∃ q : G.Walk r b, q.IsPath ∧ q.length = 2 ^ k - 1 := by
  let q : G.Walk r b := SimpleGraph.Walk.cons hra p
  refine ⟨q, hp.cons hroot, ?_⟩
  simp only [q, SimpleGraph.Walk.length_cons, hlen]
  have hpow : 4 ≤ 2 ^ k := four_le_pow_two hk
  omega

end Erdos64
