import Tengoku.Rank3kum.Rank3KUM.TwoGap.EqualNonempty

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/--
If `D - t + e` is a basis, every other element `d` of `D` is outside
`cl {e}`.-/
theorem not_mem_closure_singleton_of_exchange_isBase
    (M : Matroid α) {D : Set α} {t e d : α}
    (hEx : M.IsBase (exchangeSet D t e))
    (htD : t ∈ D) (hdD : d ∈ D)
    (heD : e ∉ D) (hdt : d ≠ t) :
    d ∉ M.closure ({e} : Set α) := by
  have het : e ≠ t := by
    intro h
    apply heD
    rw [h]
    exact htD
  have hde : d ≠ e := by
    intro h
    apply heD
    rw [← h]
    exact hdD
  have hpairSub :
      ({e, d} : Set α) ⊆ exchangeSet D t e := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact ⟨by simp, by simpa using het⟩
    · exact ⟨by simp [hdD], by simpa using hdt⟩
  have hpairI : M.Indep ({e, d} : Set α) :=
    hEx.indep.subset hpairSub
  have hdNot : d ∉ M.closure (({e, d} : Set α) \ {d}) :=
    hpairI.notMem_closure_sdiff_of_mem (by simp)
  have hset : ({e, d} : Set α) \ {d} = ({e} : Set α) := by
    ext x
    simp only [Set.mem_sdiff, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    constructor
    · rintro ⟨hx, hxd⟩
      rcases hx with rfl | rfl
      · rfl
      · exact (hxd rfl).elim
    · intro hx
      subst x
      exact ⟨Or.inl rfl, hde.symm⟩
  rwa [hset] at hdNot

/-- The residual supports of `a` and `c` are disjoint in the equal-singleton branch.-/
theorem equal_singleton_residualSupport_a_disjoint_c
    (M : Matroid α) {D : Set α} {a b c t : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hC : M.IsBase ({a, b, c} : Set α))
    (haD : a ∉ D) (hbD : b ∉ D) (hcD : c ∉ D)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (htD : t ∈ D)
    (hDtb : M.IsBase (exchangeSet D t b))
    (hXCa :
      SymmetricPartners M D ({a, b, c} : Set α) a = {t})
    (hXCc :
      SymmetricPartners M D ({a, b, c} : Set α) c = {t}) :
    Disjoint (ResidualSupport M D t a) (ResidualSupport M D t c) := by
  apply Set.disjoint_left.2
  intro d hdA hdC
  have hdA' := (mem_residualSupport M D t a d).mp hdA
  have hdC' := (mem_residualSupport M D t c d).mp hdC
  have hdD :=
    ((mem_fundamentalSupport_iff_exchange_isBase M hD
      (hC.subset_ground (by simp)) haD).mp hdA'.1).1
  have hda : d ≠ a := by
    intro h
    apply haD
    rw [← h]
    exact hdD
  have hdb : d ≠ b := by
    intro h
    apply hbD
    rw [← h]
    exact hdD
  have hdc : d ≠ c := by
    intro h
    apply hcD
    rw [← h]
    exact hdD
  have hdNotC : d ∉ ({a, b, c} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hda, hdb, hdc⟩
  have hdNotXCa :
      d ∉ SymmetricPartners M D ({a, b, c} : Set α) a := by
    rw [hXCa]
    simp only [Set.mem_singleton_iff]
    exact hdA'.2
  have hdNotXCc :
      d ∉ SymmetricPartners M D ({a, b, c} : Set α) c := by
    rw [hXCc]
    simp only [Set.mem_singleton_iff]
    exact hdC'.2

  have hOppANot :
      ¬ M.IsBase (exchangeSet ({a, b, c} : Set α) a d) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hC (by simp) haD hdNotC hdA'.1 hdNotXCa
  have hOppCNot :
      ¬ M.IsBase (exchangeSet ({a, b, c} : Set α) c d) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hC (by simp) hcD hdNotC hdC'.1 hdNotXCc
  have hDBCNot : ¬ M.IsBase ({d, b, c} : Set α) := by
    rw [exchangeSet_triple_remove_first hab hac hda] at hOppANot
    exact hOppANot
  have hABDNot : ¬ M.IsBase ({a, b, d} : Set α) := by
    rw [exchangeSet_triple_remove_third hac.symm hbc.symm hdc] at hOppCNot
    exact hOppCNot
  have hSetDBC :
      ({d, b, c} : Set α) = ({b, c, d} : Set α) := by
    ext x
    simp [or_comm, or_left_comm]
  have hBCDNot : ¬ M.IsBase ({b, c, d} : Set α) := by
    intro hbase
    apply hDBCNot
    rw [hSetDBC]
    exact hbase

  have hbcI : M.Indep ({b, c} : Set α) := by
    apply hC.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have habI : M.Indep ({a, b} : Set α) := by
    apply hC.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hdE : d ∈ M.E := hD.subset_ground hdD
  have hdClBC : d ∈ M.closure ({b, c} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank hbcI hdE
      hbc hdb.symm hdc.symm hBCDNot
  have hdClAB : d ∈ M.closure ({a, b} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank habI hdE
      hab hda.symm hdb.symm hABDNot
  have hdClB : d ∈ M.closure ({b} : Set α) := by
    rw [← closure_pair_inter_closure_pair_eq M hRank hC]
    exact ⟨hdClAB, hdClBC⟩
  have hdNotClB : d ∉ M.closure ({b} : Set α) :=
    not_mem_closure_singleton_of_exchange_isBase
      M hDtb htD hdD hbD hdA'.2
  exact hdNotClB hdClB

end Rank3KUM.TwoGap
