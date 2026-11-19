import Tengoku.MagicSquaresFieldsLean.MagicSquares.NormalizedSearch

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares

variable {F : Type*} [Field F]

/-- A negative certificate needs only finite supersets of the powers and
of the possible center-one offsets. Every supplied inclusion and every
remaining collision must be proved; the lists themselves are untrusted data.
@isnad1 id=isnparke.4h4v.s8.3907776acdd6 from=translated src=- shape=f3872aca vocab=7c22f03e
-/
theorem isNParker_of_finite_supersets (n : ℕ) (powers offsets : List F)
    (hpowers : ∀ x : F, x ^ n ∈ powers)
    (hoffsets : ∀ u : F, 1 + u ∈ powers → 1 - u ∈ powers → u ∈ offsets)
    (hzero : (-1 : F) ∈ powers → ∀ x ∈ powers, x - 1 ∈ powers → x + 1 ∈ powers →
      ¬ (Square3.centerZero x).PairwiseDistinct)
    (hone : ∀ u ∈ offsets, ∀ v ∈ offsets, u + v ∈ offsets → u - v ∈ offsets →
      ¬ (Square3.centerOne u v).PairwiseDistinct) : IsNParker F n := by
  have hmem {x : F} (hx : IsNthPower n x) : x ∈ powers := by
    obtain ⟨y, rfl⟩ := hx
    exact hpowers y
  rw [isNParker_iff_normalized_fail]
  constructor
  · intro x hx
    have hneg : (-1 : F) ∈ powers := by
      simpa [Square3.entries] using hmem (hx.2.2 (6 : Fin 9))
    apply hzero hneg x
    · simpa [Square3.entries] using hmem (hx.2.2 (0 : Fin 9))
    · simpa [Square3.entries] using hmem (hx.2.2 (5 : Fin 9))
    · simpa [Square3.entries] using hmem (hx.2.2 (7 : Fin 9))
    · exact hx.2.1
  · intro u v h
    have h0 := hmem (h.2.2 (0 : Fin 9))
    have h1 := hmem (h.2.2 (1 : Fin 9))
    have h2 := hmem (h.2.2 (2 : Fin 9))
    have h3 := hmem (h.2.2 (3 : Fin 9))
    have h5 := hmem (h.2.2 (5 : Fin 9))
    have h6 := hmem (h.2.2 (6 : Fin 9))
    have h7 := hmem (h.2.2 (7 : Fin 9))
    have h8 := hmem (h.2.2 (8 : Fin 9))
    change 1 + u ∈ powers at h0
    change 1 - u - v ∈ powers at h1
    change 1 + v ∈ powers at h2
    change 1 - u + v ∈ powers at h3
    change 1 + u - v ∈ powers at h5
    change 1 - v ∈ powers at h6
    change 1 + u + v ∈ powers at h7
    change 1 - u ∈ powers at h8
    apply hone u (hoffsets u h0 h8) v (hoffsets v h2 h6)
    · apply hoffsets
      · simpa only [← add_assoc] using h7
      · simpa only [sub_add_eq_sub_sub] using h1
    · apply hoffsets
      · simpa only [add_sub_assoc] using h5
      · have heq : (1 : F) - (u - v) = 1 - u + v := by ring
        simpa only [heq] using h3
    · exact h.2.1

/-- Boolean list folds force the finite certificate checker to visit only the
supplied parameters, rather than all pairs of field elements.
@isnad1 id=isnparke.4h4v.s10.67aac3ff2d21 from=translated src=- shape=6d554ed6 vocab=a6f4da3d
-/
theorem isNParker_of_finite_supersets_bool [DecidableEq F]
    (n : ℕ) (powers offsets : List F)
    (hpowers : ∀ x : F, x ^ n ∈ powers)
    (hoffsets : ∀ u : F, 1 + u ∈ powers → 1 - u ∈ powers → u ∈ offsets)
    (hzero : powers.all (fun x => decide ((-1 : F) ∈ powers →
      x - 1 ∈ powers → x + 1 ∈ powers →
        ¬ Function.Injective (Square3.centerZero x).entries)) = true)
    (hone : offsets.all (fun u => offsets.all (fun v => decide
      (u + v ∈ offsets → u - v ∈ offsets →
        ¬ Function.Injective (Square3.centerOne u v).entries))) = true) : IsNParker F n := by
  apply isNParker_of_finite_supersets n powers offsets hpowers hoffsets
  · intro hneg x hx hm hp
    have hc := List.all_eq_true.mp hzero x hx
    exact (of_decide_eq_true hc) hneg hm hp
  · intro u hu v hv hs hd
    have hc := List.all_eq_true.mp (List.all_eq_true.mp hone u hu) v hv
    exact (of_decide_eq_true hc) hs hd

end MagicSquares
