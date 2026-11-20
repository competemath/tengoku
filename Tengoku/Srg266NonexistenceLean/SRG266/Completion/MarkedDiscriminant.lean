/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Completion.MarkedExtension
import Tengoku.Srg266NonexistenceLean.SRG266.Lattice.AnisotropicDiscriminant

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

theorem exists_lorentzMarked_orthogonal_glue (hG : IsHypothetical G) (x : V)
    (c : IntegralGramLattice G x)
    (hc : (11 : ℤ) • c = integralGramGeneratorSum G x) :
    ∃ P : Submodule ℤ (ratGramSpace G x),
      lorentzMarkedLattice G x c ≤ P ∧ Lattice.IsLattice ℚ P ∧
      Lattice.IsMaximalIntegral (lorentzGramForm G x c) P ∧
      Lattice.IsEven (lorentzGramForm G x c) P ∧
      ∃ (S : Lattice.GlueBasis (lorentzGramForm G x c) P 3)
        (T : Lattice.GlueBasis (lorentzGramForm G x c) P 5),
      (lorentzGramForm G x c).dualSubmodule P =
        P ⊔ Submodule.span ℤ (Set.range S.vec ∪ Set.range T.vec) := by
  obtain ⟨P, hle, hlat, hmax, heven, hden⟩ :=
    exists_lorentzMarked_maximal_even_extension G hG x c hc
  have hsplit : (lorentzGramForm G x c).dualSubmodule P =
      Lattice.torsionPart (lorentzGramForm G x c) P 3 ⊔
      Lattice.torsionPart (lorentzGramForm G x c) P 5 :=
    Lattice.dual_eq_torsionPart_sup (by norm_num) (by simpa using hden)
  have : Fact (Nat.Prime 3) := ⟨by decide⟩
  have : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨S⟩ := Lattice.exists_orthogonal_glue_basis (B := lorentzGramForm G x c)
    (Ñ := P) (p := 3) (by norm_num) (lorentzGramForm_isSymm G x c)
    (lorentzGramForm_nondegenerate G hG x c hc) hlat hmax (by norm_num) hsplit
  obtain ⟨T⟩ := Lattice.exists_orthogonal_glue_basis (B := lorentzGramForm G x c)
    (Ñ := P) (p := 5) (q := 3) (by norm_num) (lorentzGramForm_isSymm G x c)
    (lorentzGramForm_nondegenerate G hG x c hc) hlat hmax (by norm_num)
    (hsplit.trans (sup_comm _ _))
  exact ⟨P, hle, hlat, hmax, heven, S, T, Lattice.dual_eq_sup_span_glue S T hsplit⟩

theorem exists_lorentzMarked_discriminant_from_graph (hG : IsHypothetical G) (x : V) :
    ∃ (c : IntegralGramLattice G x) (P : Submodule ℤ (ratGramSpace G x)),
      (11 : ℤ) • c = integralGramGeneratorSum G x ∧
      gramLattice G x ≤ P ∧ lorentzWeylVector G x c ∈ P ∧
      Lattice.IsLattice ℚ P ∧ Lattice.IsMaximalIntegral (lorentzGramForm G x c) P ∧
      Lattice.IsEven (lorentzGramForm G x c) P ∧
      ∃ (S : Lattice.GlueBasis (lorentzGramForm G x c) P 3)
        (T : Lattice.GlueBasis (lorentzGramForm G x c) P 5),
      (lorentzGramForm G x c).dualSubmodule P =
        P ⊔ Submodule.span ℤ (Set.range S.vec ∪ Set.range T.vec) := by
  obtain ⟨c, hc⟩ := exists_integral_centroid G hG x
  obtain ⟨P, hle, hlat, hmax, heven, S, T, hdual⟩ :=
    exists_lorentzMarked_orthogonal_glue G hG x c hc
  exact ⟨c, P, hc, (gramLattice_le_lorentzMarkedLattice G x c).trans hle,
    hle (lorentzWeylVector_mem_markedLattice G x c), hlat, hmax, heven, S, T, hdual⟩

end SRG266
