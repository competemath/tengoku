import Tengoku.Seed.RingTheory.Valuation.ValuationSubring
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

theorem ValuationSubring.sum_finrank_residueField_le_finrank_of_forall_mem_iff
    {E F : Type*} [Field E] [Field F] [Algebra E F]
    [FiniteDimensional E F]
    (O : ValuationSubring E)
    {ι : Type*} [Fintype ι]
    (O' : ι → ValuationSubring F)
    (hinj : Function.Injective O')
    (hO : ∀ (j : ι) (x : E), algebraMap E F x ∈ O' j ↔ x ∈ O)
    [∀ j, Algebra (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j))]
    (hcompat : ∀ (j : ι) (a : O), algebraMap (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j))
        (IsLocalRing.residue O a) = IsLocalRing.residue (O' j) ⟨algebraMap E F a, (hO j a).mpr a.2⟩) :
    (∀ j, FiniteDimensional (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j))) ∧
      ∑ j, Module.finrank (IsLocalRing.ResidueField O) (IsLocalRing.ResidueField (O' j)) ≤ Module.finrank E F := by exact @_root_.P2MW.S_ValuationSubring_sum_finrank_residueField_le_finrank_of_forall_mem_iff.solution E F _ _ _ _ O ι _ O' hinj hO _ hcompat
