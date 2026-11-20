import Tengoku.Seed.Combinatorics.SimpleGraph.Hasse
import Tengoku.Seed.Data.Fintype.Powerset
import Tengoku.Seed.Data.Finset.SymmDiff
import Tengoku.Seed.Data.Finset.Sort

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Token graphs

This file formalizes the token-graph definition used in
`materials/burning_path_token_graphs/problem.tex`.
-/

open scoped symmDiff

namespace BurningPath

/-- A configuration of `k` indistinguishable tokens on `V` is a `k`-element finset.-/
abbrev Configuration (V : Type*) (k : ℕ) := {s : Finset V // s.card = k}

/--
On a linearly ordered vertex type, a configuration is equivalently its increasing list of
occupied vertices.-/
noncomputable def configurationEquivOrderEmbedding (V : Type*) [LinearOrder V] (k : ℕ) :
    Configuration V k ≃ (Fin k ↪o V) where
  toFun A := A.1.orderEmbOfFin A.2
  invFun f := ⟨Finset.univ.map f.toEmbedding, by simp⟩
  left_inv A := by
    apply Subtype.ext
    exact A.1.map_orderEmbOfFin_univ A.2
  right_inv f := by
    symm
    apply Finset.orderEmbOfFin_unique'
    intro i
    simp

/--
@isnad1 id=eq.0h3v.s7.bc9e2ce875f9 from=translated src=- shape=0a0544dc vocab=f2383216
-/
@[simp]
theorem configurationEquivOrderEmbedding_apply (V : Type*) [LinearOrder V] (k : ℕ)
    (A : Configuration V k) :
    configurationEquivOrderEmbedding V k A = A.1.orderEmbOfFin A.2 :=
  rfl

/-- The nontrivial token-count range `1 ≤ k ≤ |V| - 1`.-/
def ValidTokenCount (V : Type*) [Fintype V] (k : ℕ) : Prop :=
  1 ≤ k ∧ k < Fintype.card V

/--
The `k`-token graph of a simple graph. Two configurations are adjacent exactly when their
symmetric difference is the pair of endpoints of an edge of the original graph.-/
noncomputable def tokenGraph {V : Type*} (G : SimpleGraph V) (k : ℕ) :
    SimpleGraph (Configuration V k) := by
  classical
  exact
    { Adj := fun A B ↦
        ∃ u v, G.Adj u v ∧ (A.1 : Set V) ∆ (B.1 : Set V) = ({u, v} : Set V)
      symm :=
        { symm := by
            rintro A B ⟨u, v, huv, hAB⟩
            exact ⟨u, v, huv, by simpa [symmDiff_comm] using hAB⟩ }
      loopless :=
        { irrefl := by
            rintro A ⟨u, v, huv, hAA⟩
            have hu := congrArg (fun s : Set V ↦ u ∈ s) hAA
            simp at hu } }

/--
@isnad1 id=iff.0h5v.s6.8f5d2cd4ab08 from=translated src=- shape=1520f544 vocab=b977e7b4
-/
@[simp]
theorem tokenGraph_adj {V : Type*} (G : SimpleGraph V) (k : ℕ)
    (A B : Configuration V k) :
    (tokenGraph G k).Adj A B ↔
      ∃ u v, G.Adj u v ∧ (A.1 : Set V) ∆ (B.1 : Set V) = ({u, v} : Set V) := by
  rfl

/-- The token graph of the path on `n` vertices.-/
noncomputable abbrev pathTokenGraph (n k : ℕ) :=
  tokenGraph (SimpleGraph.pathGraph n) k

/--
@isnad1 id=iff.0h4v.s7.1d585776e04c from=translated src=- shape=51f7581d vocab=807c33a8
-/
@[simp, nolint simpNF]
theorem pathTokenGraph_adj (n k : ℕ) (A B : Configuration (Fin n) k) :
    (pathTokenGraph n k).Adj A B ↔
      ∃ u v, (u.val + 1 = v.val ∨ v.val + 1 = u.val) ∧
        (A.1 : Set (Fin n)) ∆ (B.1 : Set (Fin n)) = ({u, v} : Set (Fin n)) := by
  rw [tokenGraph_adj]
  simp only [SimpleGraph.pathGraph_adj]

/-- There are `choose |V| k` configurations of `k` tokens on a finite vertex set.
@isnad1 id=eq.0h2v.s5.e2660499d855 from=translated src=- shape=588bfa65 vocab=45114229
-/
@[simp, nolint simpNF]
theorem card_configuration (V : Type*) [Fintype V] (k : ℕ) :
    Fintype.card (Configuration V k) = Nat.choose (Fintype.card V) k :=
  Fintype.card_finset_len k

/-- In particular, `F_k(P_n)` has `choose n k` vertices.
@isnad1 id=eq.0h2v.s5.d3ddf9b08450 from=translated src=- shape=3c32c445 vocab=555603a6
-/
@[simp, nolint simpNF]
theorem card_pathTokenConfiguration (n k : ℕ) :
    Fintype.card (Configuration (Fin n) k) = Nat.choose n k := by
  simp

/-- A `k`-token configuration exists whenever the finite vertex type has at least `k` elements.
@isnad1 id=nonempty.1h2v.s4.fc75eec5d797 from=translated src=- shape=7e4cc14d vocab=1cd4051c
-/
theorem nonempty_configuration_of_le (V : Type*) [Fintype V] {k : ℕ}
    (hk : k ≤ Fintype.card V) :
    Nonempty (Configuration V k) := by
  rw [← Fintype.card_pos_iff]
  simpa using Nat.choose_pos hk

end BurningPath
