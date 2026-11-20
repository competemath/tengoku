import Tengoku.Rank3kum.Rank3KUM.TwoGap.EqualDisjointAC

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace Rank3KUM.TwoGap

open Set

variable {α : Type*}

/-- The residual supports of `a` and `b` are disjoint in the equal-singleton branch.
@isnad1 id=disjoint.17h8v.s8.c699f3649fb6 from=translated src=- shape=fdfede9e vocab=d48386b6
-/
theorem equal_singleton_residualSupport_a_disjoint_b
    (M : Matroid α) {D : Set α} {a b c q t : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hC : M.IsBase ({a, b, c} : Set α))
    (hQ : M.IsBase ({b, c, q} : Set α))
    (haD : a ∉ D) (hbD : b ∉ D) (hcD : c ∉ D) (hqD : q ∉ D)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hbq : b ≠ q) (hcq : c ≠ q)
    (htD : t ∈ D)
    (hDtc : M.IsBase (exchangeSet D t c))
    (hXCa :
      SymmetricPartners M D ({a, b, c} : Set α) a = {t})
    (hXQ :
      SymmetricPartners M D ({b, c, q} : Set α) b = {t}) :
    Disjoint (ResidualSupport M D t a) (ResidualSupport M D t b) := by
  apply Set.disjoint_left.2
  intro d hdA hdB
  have hdA' := (mem_residualSupport M D t a d).mp hdA
  have hdB' := (mem_residualSupport M D t b d).mp hdB
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
  have hdq : d ≠ q := by
    intro h
    apply hqD
    rw [← h]
    exact hdD
  have hdNotC : d ∉ ({a, b, c} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hda, hdb, hdc⟩
  have hdNotQ : d ∉ ({b, c, q} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hdb, hdc, hdq⟩
  have hdNotXCa :
      d ∉ SymmetricPartners M D ({a, b, c} : Set α) a := by
    rw [hXCa]
    simp only [Set.mem_singleton_iff]
    exact hdA'.2
  have hdNotXQ :
      d ∉ SymmetricPartners M D ({b, c, q} : Set α) b := by
    rw [hXQ]
    simp only [Set.mem_singleton_iff]
    exact hdB'.2

  have hOppANot :
      ¬ M.IsBase (exchangeSet ({a, b, c} : Set α) a d) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hC (by simp) haD hdNotC hdA'.1 hdNotXCa
  have hOppBNot :
      ¬ M.IsBase (exchangeSet ({b, c, q} : Set α) b d) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hQ (by simp) hbD hdNotQ hdB'.1 hdNotXQ
  have hDBCNot : ¬ M.IsBase ({d, b, c} : Set α) := by
    rw [exchangeSet_triple_remove_first hab hac hda] at hOppANot
    exact hOppANot
  have hDCQNot : ¬ M.IsBase ({d, c, q} : Set α) := by
    rw [exchangeSet_triple_remove_first hbc hbq hdb] at hOppBNot
    exact hOppBNot
  have hSetDBC :
      ({d, b, c} : Set α) = ({b, c, d} : Set α) := by
    ext x
    simp [or_comm, or_left_comm]
  have hBCDNot : ¬ M.IsBase ({b, c, d} : Set α) := by
    intro hbase
    apply hDBCNot
    rw [hSetDBC]
    exact hbase
  have hSetDCQ :
      ({d, c, q} : Set α) = ({c, q, d} : Set α) := by
    ext x
    simp [or_comm, or_left_comm]
  have hCQDNot : ¬ M.IsBase ({c, q, d} : Set α) := by
    intro hbase
    apply hDCQNot
    rw [hSetDCQ]
    exact hbase

  have hbcI : M.Indep ({b, c} : Set α) := by
    apply hQ.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have hcqI : M.Indep ({c, q} : Set α) := by
    apply hQ.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hdE : d ∈ M.E := hD.subset_ground hdD
  have hdClBC : d ∈ M.closure ({b, c} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank hbcI hdE
      hbc hdb.symm hdc.symm hBCDNot
  have hdClCQ : d ∈ M.closure ({c, q} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank hcqI hdE
      hcq hdc.symm hdq.symm hCQDNot
  have hdClC : d ∈ M.closure ({c} : Set α) := by
    rw [← closure_pair_inter_closure_pair_eq M hRank hQ]
    exact ⟨hdClBC, hdClCQ⟩
  have hdNotClC : d ∉ M.closure ({c} : Set α) :=
    not_mem_closure_singleton_of_exchange_isBase
      M hDtc htD hdD hcD hdA'.2
  exact hdNotClC hdClC

/-- The residual supports of `b` and `c` are disjoint in the equal-singleton branch.
@isnad1 id=disjoint.17h8v.s8.f294005dc472 from=translated src=- shape=cea11dbe vocab=d48386b6
-/
theorem equal_singleton_residualSupport_b_disjoint_c
    (M : Matroid α) {D : Set α} {p a b c t : α}
    (hRank : M.eRank = 3)
    (hD : M.IsBase D)
    (hP : M.IsBase ({p, a, b} : Set α))
    (hC : M.IsBase ({a, b, c} : Set α))
    (hpD : p ∉ D) (haD : a ∉ D) (hbD : b ∉ D) (hcD : c ∉ D)
    (hpa : p ≠ a) (hpb : p ≠ b) (hab : a ≠ b)
    (hac : a ≠ c) (hbc : b ≠ c)
    (htD : t ∈ D)
    (hDta : M.IsBase (exchangeSet D t a))
    (hXP :
      SymmetricPartners M D ({p, a, b} : Set α) b = {t})
    (hXCc :
      SymmetricPartners M D ({a, b, c} : Set α) c = {t}) :
    Disjoint (ResidualSupport M D t b) (ResidualSupport M D t c) := by
  apply Set.disjoint_left.2
  intro d hdB hdC
  have hdB' := (mem_residualSupport M D t b d).mp hdB
  have hdC' := (mem_residualSupport M D t c d).mp hdC
  have hdD :=
    ((mem_fundamentalSupport_iff_exchange_isBase M hD
      (hP.subset_ground (by simp)) hbD).mp hdB'.1).1
  have hdp : d ≠ p := by
    intro h
    apply hpD
    rw [← h]
    exact hdD
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
  have hdNotP : d ∉ ({p, a, b} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hdp, hda, hdb⟩
  have hdNotC : d ∉ ({a, b, c} : Set α) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    exact ⟨hda, hdb, hdc⟩
  have hdNotXP :
      d ∉ SymmetricPartners M D ({p, a, b} : Set α) b := by
    rw [hXP]
    simp only [Set.mem_singleton_iff]
    exact hdB'.2
  have hdNotXCc :
      d ∉ SymmetricPartners M D ({a, b, c} : Set α) c := by
    rw [hXCc]
    simp only [Set.mem_singleton_iff]
    exact hdC'.2

  have hOppBNot :
      ¬ M.IsBase (exchangeSet ({p, a, b} : Set α) b d) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hP (by simp) hbD hdNotP hdB'.1 hdNotXP
  have hOppCNot :
      ¬ M.IsBase (exchangeSet ({a, b, c} : Set α) c d) :=
    not_other_exchange_isBase_of_mem_fundamentalSupport_not_symmetricPartner
      M hD hC (by simp) hcD hdNotC hdC'.1 hdNotXCc
  have hPADNot : ¬ M.IsBase ({p, a, d} : Set α) := by
    rw [exchangeSet_triple_remove_third hpb.symm hab.symm hdb] at hOppBNot
    exact hOppBNot
  have hABDNot : ¬ M.IsBase ({a, b, d} : Set α) := by
    rw [exchangeSet_triple_remove_third hac.symm hbc.symm hdc] at hOppCNot
    exact hOppCNot

  have hpaI : M.Indep ({p, a} : Set α) := by
    apply hP.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
  have habI : M.Indep ({a, b} : Set α) := by
    apply hP.indep.subset
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with rfl | rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr rfl)
  have hdE : d ∈ M.E := hD.subset_ground hdD
  have hdClPA : d ∈ M.closure ({p, a} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank hpaI hdE
      hpa hdp.symm hda.symm hPADNot
  have hdClAB : d ∈ M.closure ({a, b} : Set α) :=
    mem_closure_pair_of_not_isBase_triple M hRank habI hdE
      hab hda.symm hdb.symm hABDNot
  have hdClA : d ∈ M.closure ({a} : Set α) := by
    rw [← closure_pair_inter_closure_pair_eq M hRank hP]
    exact ⟨hdClPA, hdClAB⟩
  have hdNotClA : d ∉ M.closure ({a} : Set α) :=
    not_mem_closure_singleton_of_exchange_isBase
      M hDta htD hdD haD hdB'.2
  exact hdNotClA hdClA

end Rank3KUM.TwoGap
