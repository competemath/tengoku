import Tengoku.Rank3kum.Rank3KUM.TwoGap.EqualDisjointRest

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Rank3KUM.Version2

open Set
open Rank3KUM.TwoGap

variable {α : Type*}

/--
Paper v2, Lemma 7.20: the common residual-support disjointness argument.

The two target elements `x` and `y` sit in basis triples whose complementary
pairs are `{u,s}` and `{s,v}`.  The bridge triple `{u,s,v}` is also a basis.
If both target symmetric-partner sets are the common singleton `{t}`, while
`D - t + s` is a basis, then the residual supports of `x` and `y` are
disjoint.

This is the single abstract argument instantiated three times in the paper's
table.  It replaces the need to repeat the same closure-intersection proof
for the `(a,c)`, `(a,b)`, and `(b,c)` cases.-/
theorem residualSupport_disjoint_of_shared_bridge
    (M : Matroid α)
    {D : Set α} {x u s v y t : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hX : M.IsBase ({x, u, s} : Set α))
    (hY : M.IsBase ({s, v, y} : Set α))
    (hBridge : M.IsBase ({u, s, v} : Set α))
    (hxD : x ∉ D) (huD : u ∉ D) (hsD : s ∉ D)
    (hvD : v ∉ D) (hyD : y ∉ D)
    (hxu : x ≠ u) (hxs : x ≠ s) (hus : u ≠ s)
    (hsv : s ≠ v) (hys : y ≠ s) (hyv : y ≠ v)
    (htD : t ∈ D)
    (hDts : M.IsBase (exchangeSet D t s))
    (hXsym :
      SymmetricPartners M D ({x, u, s} : Set α) x = {t})
    (hYsym :
      SymmetricPartners M D ({s, v, y} : Set α) y = {t}) :
    Disjoint (ResidualSupport M D t x) (ResidualSupport M D t y) := by
  apply Set.disjoint_left.2
  intro d hdX hdY
  have hdX' := (mem_residualSupport M D t x d).mp hdX
  have hdY' := (mem_residualSupport M D t y d).mp hdY

  have hdD : d ∈ D :=
    ((mem_fundamentalSupport_iff_exchange_isBase M hD
      (hX.subset_ground (by simp)) hxD).mp hdX'.1).1
  have hdx : d ≠ x := by
    intro h
    apply hxD
    rw [← h]
    exact hdD
  have hdu : d ≠ u := by
    intro h
    apply huD
    rw [← h]
    exact hdD
  have hds : d ≠ s := by
    intro h
    apply hsD
    rw [← h]
    exact hdD
  have hdv : d ≠ v := by
    intro h
    apply hvD
    rw [← h]
    exact hdD
  have hdy : d ≠ y := by
    intro h
    apply hyD
    rw [← h]
    exact hdD

  have hdNotX : d ∉ ({x, u, s} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hdx, hdu, hds⟩
  have hdNotY : d ∉ ({s, v, y} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hds, hdv, hdy⟩
  have hdNotXsym :
      d ∉ SymmetricPartners M D ({x, u, s} : Set α) x := by
    rw [hXsym]
    simpa only [Set.mem_singleton_iff] using hdX'.2
  have hdNotYsym :
      d ∉ SymmetricPartners M D ({s, v, y} : Set α) y := by
    rw [hYsym]
    simpa only [Set.mem_singleton_iff] using hdY'.2

  have hOppXNot :
      ¬ M.IsBase (exchangeSet ({x, u, s} : Set α) x d) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hX (by simp) hxD hdNotX hdX'.1 hdNotXsym
  have hOppYNot :
      ¬ M.IsBase (exchangeSet ({s, v, y} : Set α) y d) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hY (by simp) hyD hdNotY hdY'.1 hdNotYsym

  have hDUSNot : ¬ M.IsBase ({d, u, s} : Set α) := by
    rw [exchangeSet_triple_remove_first hxu hxs hdx] at hOppXNot
    exact hOppXNot
  have hUSDNot : ¬ M.IsBase ({u, s, d} : Set α) := by
    intro hbase
    apply hDUSNot
    have hset : ({d, u, s} : Set α) = ({u, s, d} : Set α) := by
      ext z
      simp [or_comm, or_left_comm]
    rw [hset]
    exact hbase
  have hSVDNot : ¬ M.IsBase ({s, v, d} : Set α) := by
    rw [exchangeSet_triple_remove_third hys hyv hdy] at hOppYNot
    exact hOppYNot

  have hUSI : M.Indep ({u, s} : Set α) := by
    apply hBridge.indep.subset
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hSVI : M.Indep ({s, v} : Set α) := by
    apply hBridge.indep.subset
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz ⊢
    rcases hz with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)

  have hdE : d ∈ M.E := hD.subset_ground hdD
  have hdClUS : d ∈ M.closure ({u, s} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank hUSI hdE
      hus hdu.symm hds.symm hUSDNot
  have hdClSV : d ∈ M.closure ({s, v} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank hSVI hdE
      hsv hds.symm hdv.symm hSVDNot
  have hdClS : d ∈ M.closure ({s} : Set α) := by
    rw [← closure_pair_inter_closure_pair_eq M hRank hBridge]
    exact ⟨hdClUS, hdClSV⟩
  have hdNotClS : d ∉ M.closure ({s} : Set α) :=
    not_mem_closure_singleton_of_exchange_isBase
      M hDts htD hdD hsD hdX'.2
  exact hdNotClS hdClS

end Rank3KUM.Version2
