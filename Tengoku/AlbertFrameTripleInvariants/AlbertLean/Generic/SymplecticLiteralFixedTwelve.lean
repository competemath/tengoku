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

theorem ofFn_scheduleOfLengthTwelve
    (word : List (Step (K := K) (V := V))) (hlen : word.length = 12) :
    List.ofFn (scheduleOfLengthTwelve word hlen) = word := by
  unfold scheduleOfLengthTwelve
  apply List.ext_getElem
  · simpa only [List.length_ofFn] using hlen.symm
  · intro i hi₁ hi₂
    rw [List.getElem_ofFn]

theorem fixedTwelveMap_scheduleOfLengthTwelve
    (omega : BilinForm (K := K) (V := V))
    (word : List (Step (K := K) (V := V))) (hlen : word.length = 12) :
    fixedTwelveMap omega (scheduleOfLengthTwelve word hlen) = wordMap omega word := by
  rw [fixedTwelveMap, ofFn_scheduleOfLengthTwelve]

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
