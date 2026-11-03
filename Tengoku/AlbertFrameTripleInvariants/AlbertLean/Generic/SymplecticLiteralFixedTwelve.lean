import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticThreePairCoverage

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms ofFn_scheduleOfLengthTwelve` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms fixedTwelveMap_scheduleOfLengthTwelve` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_literal_fixed_twelve_triple_alignment` (it only prints; the queue checks the axioms of every declaration). -/

noncomputable section
namespace AlbertLean.Generic.SymplecticTransvection

universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

def scheduleOfLengthTwelve
    (word : List (Step (K := K) (V := V))) (hlen : word.length = 12) :
    FixedTwelveSchedule (K := K) (V := V) :=
  fun i => word[i.val]'(by simpa [hlen] using i.isLt)

/--
@isnad1 id=eq.1h3v.s6.0fbdfa2d0b43 from=translated src=- shape=5a91e762 vocab=7a558a77
-/
theorem ofFn_scheduleOfLengthTwelve
    (word : List (Step (K := K) (V := V))) (hlen : word.length = 12) :
    List.ofFn (scheduleOfLengthTwelve word hlen) = word := by
  unfold scheduleOfLengthTwelve
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen.symm
  · intro i hi₁ hi₂
    rw [List.getElem_ofFn]

/--
@isnad1 id=eq.1h4v.s6.7a89be33d2de from=translated src=- shape=0e3fff3f vocab=5ed00c37
-/
theorem fixedTwelveMap_scheduleOfLengthTwelve
    (omega : BilinForm (K := K) (V := V))
    (word : List (Step (K := K) (V := V))) (hlen : word.length = 12) :
    fixedTwelveMap omega (scheduleOfLengthTwelve word hlen) = wordMap omega word := by
  rw [fixedTwelveMap, ofFn_scheduleOfLengthTwelve]

/--
@isnad1 id=ex.5h7v.s9.43e57c6ef220 from=translated src=- shape=27f6c062 vocab=d5d41718
-/
theorem exists_literal_fixed_twelve_triple_alignment
    (omega : BilinForm (K := K) (V := V)) (halt : ∀ x, omega x x = 0)
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (u v e f : Fin 3 → V) (hsrc : HyperbolicTriple omega u v)
    (htgt : HyperbolicTriple omega e f) :
    ∃ schedule : FixedTwelveSchedule (K := K) (V := V),
      (∀ i, fixedTwelveMap omega schedule (u i) = e i) ∧
      (∀ i, fixedTwelveMap omega schedule (v i) = f i) := by
  obtain ⟨word, hlen, hu, hv⟩ := exists_fixed_twelve_triple_alignment
    omega halt hleft hright u v e f hsrc htgt
  refine ⟨scheduleOfLengthTwelve word hlen, ?_, ?_⟩
  · intro i
    rw [fixedTwelveMap_scheduleOfLengthTwelve]
    exact hu i
  · intro i
    rw [fixedTwelveMap_scheduleOfLengthTwelve]
    exact hv i

end AlbertLean.Generic.SymplecticTransvection
