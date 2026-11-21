import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_ValuationSubring_exists_smul_mem_of_transcendental_residue

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_ValuationSubring_exists_smul_mem_of_transcendental_residue.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

/--
@isnad1 id=ex.6h8v.s11.33c43d53f904 from=translated src=- shape=38fdc5ad vocab=3795f674
-/
theorem ValuationSubring.exists_smul_mem_of_transcendental_residue
    {L : Type*} [Field L] [IsAlgClosed L] (A : ValuationSubring L)
    {F : Type*} [Field F] [Algebra L F]
    (O : ValuationSubring F) (hO : ∀ x : L, algebraMap L F x ∈ O ↔ x ∈ A)
    {Fbar : Type*} [Field Fbar] [Algebra (IsLocalRing.ResidueField A) Fbar]
    (ρ : O →+* Fbar) (hker : RingHom.ker ρ = IsLocalRing.maximalIdeal O)
    (hρ : ∀ a : A, ρ ⟨algebraMap L F a, (hO a).mpr a.2⟩ =
      algebraMap (IsLocalRing.ResidueField A) Fbar (IsLocalRing.residue A a))
    (f : F) (hf : f ∈ O)
    (htr : Transcendental (IsLocalRing.ResidueField A) (ρ ⟨f, hf⟩))
    [Algebra.IsAlgebraic (IntermediateField.adjoin L ({f} : Set F)) F]
    (h : F) (hh : h ≠ 0) :
    ∃ c : L, ∃ hc : c • h ∈ O, ρ ⟨c • h, hc⟩ ≠ 0 := by exact @_root_.P2MW.S_ValuationSubring_exists_smul_mem_of_transcendental_residue.solution L _ _ A F _ _ O hO Fbar _ _ ρ hker hρ f hf htr _ h hh
