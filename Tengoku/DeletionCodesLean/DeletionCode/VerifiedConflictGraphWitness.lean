import Tengoku.DeletionCodesLean.DeletionCode.ConflictGraphWitness
import Tengoku.DeletionCodesLean.DeletionCode.BubbleCatalogue
import Tengoku.DeletionCodesLean.DeletionCode.SeparatedTraceCoverage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms listLetters_ofFn` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms unique_zero_length` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms empty_catalogue` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms separated_coverage` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms edge_catalogue` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms edge_surviving` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms bounded_witness` (it only prints; the queue checks the axioms of every declaration). -/

/-!
The concrete separated-trace theorem discharges the coverage interface for
the manuscript's actual conflict graph. The zero-length degeneracy is handled
explicitly, so coverage itself has no added positivity assumption on k.
-/
namespace DeletionCode.VerifiedConflictGraphWitness

open Windows HeaderRecovery CatalogueWords AlignmentTrace
open ConflictGraphWitness SignedSupport SignedRuleCount RuleSetGraph WitnessCases

/--
@isnad1 id=eq.0h2v.s3.0b1b0dc93cec from=translated src=- shape=fa8eabd7 vocab=550859d8
-/
theorem listLetters_ofFn {n : ℕ} (x : Bits n) :
    listLetters (List.ofFn x) = padBits x := by
  funext i
  by_cases hi : i < n
  · simp [listLetters, padBits, hi, List.getD]
  · simp [listLetters, padBits, hi, List.getD]

/--
@isnad1 id=eq.1h2v.s4.eb1a151b86ab from=translated src=- shape=10c4331a vocab=e4f5e6a5
-/
theorem unique_zero_length {n : ℕ} {x : Letters} (hx : KUnique x n 0) : n = 0 := by
  by_contra hn
  have heq : 0 = 1 := hx 0 1 (by omega) (by omega) (by intro i hi; omega)
  omega

/--
@isnad1 id=catalogu.0h1v.s5.fc9e6d635807 from=translated src=- shape=310f83fe vocab=468f87b2
-/
theorem empty_catalogue (k : ℕ) : ConnectedBlocks.CatalogueRule 0 k 0 := by
  have h := BubbleCatalogue.catalogueRule (k := k) (t := 0) (fun i => Fin.elim0 i)
    (fun b => Fin.elim0 b) (fun b => Fin.elim0 b) (fun a => Fin.elim0 a)
    (by simp) (by simp)
  simpa using h

/-- Full separated coverage, including the degenerate k = 0 case. There is
no target uniqueness, catalogue presentation, or spectrum-sum premise.
@isnad1 id=separate.0h3v.s3.5046a09600b5 from=translated src=- shape=32b70efe vocab=d3df92a0
-/
theorem separated_coverage (t k n : ℕ) : SeparatedCoverage t k n := by
  intro x y hx trace hs ht hd hi hsep
  by_cases hk : 1 ≤ k
  · have hx' : KUnique (listLetters trace.source) trace.source.length k := by
      simpa only [hs, List.length_ofFn, listLetters_ofFn] using hx
    have h := SeparatedTraceCoverage.catalogueRule trace t k hk hx' hsep hd hi
    simpa only [hs, ht, List.length_ofFn, listLetters_ofFn, spectrum] using h
  · have hk0 : k = 0 := by omega
    subst k
    have hn := unique_zero_length hx
    have hlen : trace.source.length = n := by rw [hs, List.length_ofFn]
    have hc := trace.source_length
    have ht0 : t = 0 := by omega
    rw [ht0]
    subst n
    have hxy : x = y := Subsingleton.elim _ _
    rw [hxy, sub_self]
    exact empty_catalogue 0

/-- Every edge of the actual retained conflict graph is a catalogue rule;
coverage is proved internally.
@isnad1 id=catalogu.1h7v.s7.e322f22c18de from=translated src=- shape=08c1b64c vocab=1294b1eb
-/
theorem edge_catalogue {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    ConnectedBlocks.CatalogueRule t k (spectrum k y.val - spectrum k x.val) :=
  ConflictGraphWitness.edge_catalogue (separated_coverage t k n) hxy

/--
@isnad1 id=mem.2h7v.s7.a7bf3325850a from=translated src=- shape=dc28f96f vocab=e37a3c5a
-/
theorem edge_surviving {t k n Q : ℕ} {H : Spectrum k →+ UnitAddCircle}
    (hQ : 2 ≤ Q) {x y : Vertex (n := n) t Q H} (hxy : (graph t Q H).Adj x y) :
    spectrum k y.val - spectrum k x.val ∈ surviving t Q H :=
  ConflictGraphWitness.edge_surviving hQ (separated_coverage t k n) hxy

/-- The manuscript's complete deterministic bounded-witness lemma on the
actual finite conflict graph, with its explicit exceptional set and hash.
No earlier coverage lemma is left as an assumption.
@isnad1 id=ex.3h6v.s8.5f1b8adad272 from=translated src=- shape=8970d47f vocab=e4816c78
-/
theorem bounded_witness {t k n Q : ℕ} (ht : 2 ≤ t) (hQ : 2 ≤ Q)
    (H : Spectrum k →+ UnitAddCircle) (x : Vertex (n := n) t Q H)
    (hnot : ¬ ((graph t Q H).connectedComponentMk x).toSimpleGraph.Colorable 2) :
    ∃ U : RuleSet k,
      Witness t k (spectrum k x.val) (surviving t Q H) U ∧
      ManuscriptCounting.GeneratingSet t (padBits x.val) n k U.card (componentCount U) U :=
  ConflictGraphWitness.bounded_witness_of_coverage ht hQ H (separated_coverage t k n) x hnot

end DeletionCode.VerifiedConflictGraphWitness
