import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SymplecticActualProjectorExtraction

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms wordMap_injective` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms intertwines_of_spanning_target` (it only prints; the queue checks the axioms of every declaration). -/
/-! Tengoku repair: removed `#print axioms exists_twelve_actual_frame_alignment` (it only prints; the queue checks the axioms of every declaration). -/

/-! Fixed twelve-step conjugacy of actual projector frames. The only basis
input describes the fixed target; no basis or rank is supplied for the frame
being normalized. The grouped standard coordinates instantiate this target. -/
noncomputable section
namespace AlbertLean.Generic.SymplecticProjectorFrame

open SymplecticTransvection
universe u v
variable {K : Type u} [Field K] [CharZero K]
variable {V : Type v} [AddCommGroup V] [Module K V]

theorem wordMap_injective
    (omega : BilinForm (K := K) (V := V)) (halt : ∀ x, omega x x = 0)
    (word : List (Step (K := K) (V := V))) :
    Function.Injective (wordMap omega word) := by
  induction word with
  | nil => exact fun _ _ h => h
  | cons step word ih =>
    rcases step with ⟨d, t⟩
    intro x y h
    apply ih
    apply (equiv omega halt d t).injective
    exact h

/-- A map aligning six projector eigenvectors with a spanning target already
intertwines the projectors. No source dimension/rank calculation is needed.-/
theorem intertwines_of_spanning_target
    (L : V →ₗ[K] V) (hL : Function.Injective L)
    (P Q : Fin 3 → V →ₗ[K] V) (u v e f : Fin 3 → V)
    (hLu : ∀ j, L (u j) = e j) (hLv : ∀ j, L (v j) = f j)
    (hPu : ∀ i j, P i (u j) = if i = j then u j else 0)
    (hPv : ∀ i j, P i (v j) = if i = j then v j else 0)
    (hQe : ∀ i j, Q i (e j) = if i = j then e j else 0)
    (hQf : ∀ i j, Q i (f j) = if i = j then f j else 0)
    (hspan : ∀ z : V, ∃ a b : Fin 3 → K,
      z = (∑ j, a j • e j) + ∑ j, b j • f j) :
    ∀ i, L.comp (P i) = (Q i).comp L := by
  classical
  intro i
  apply LinearMap.ext
  intro x
  obtain ⟨a, b, hx⟩ := hspan (L x)
  have hx' : x = (∑ j, a j • u j) + ∑ j, b j • v j := by
    apply hL
    simpa only [map_add, map_sum, map_smul, hLu, hLv] using hx
  simp only [LinearMap.comp_apply]
  rw [hx']
  simp only [map_add, map_sum, map_smul, hPu, hPv, hLu, hLv,
    hQe, hQf, apply_ite, map_zero]

/-- Actual complete nonzero self-adjoint projector frames are normalized by
exactly twelve transvections over the original field. All target hypotheses
are fixed standard-coordinate identities, independent of the input frame.-/
theorem exists_twelve_actual_frame_alignment
    (omega : BilinForm (K := K) (V := V)) (halt : ∀ x, omega x x = 0)
    (hleft : IsLeftNondegenerate omega) (hright : IsRightNondegenerate omega)
    (P : Fin 3 → V →ₗ[K] V)
    (hidem : ∀ i, IsIdempotent (P i))
    (hself : ∀ i, IsSelfAdjoint omega (P i)) (hne : ∀ i, P i ≠ 0)
    (hsum : P 0 + P 1 + P 2 = LinearMap.id)
    (Q : Fin 3 → V →ₗ[K] V) (e f : Fin 3 → V)
    (htgt : HyperbolicTriple omega e f)
    (hQe : ∀ i j, Q i (e j) = if i = j then e j else 0)
    (hQf : ∀ i j, Q i (f j) = if i = j then f j else 0)
    (hspan : ∀ z : V, ∃ a b : Fin 3 → K,
      z = (∑ j, a j • e j) + ∑ j, b j • f j) :
    ∃ word : List (Step (K := K) (V := V)), word.length = 12 ∧
      ∀ i, (wordMap omega word).comp (P i) = (Q i).comp (wordMap omega word) := by
  obtain ⟨u, v, huv, hPu, hPv⟩ :=
    exists_hyperbolicTriple_of_complete_frame omega hright P hidem hself hne hsum
  obtain ⟨word, hlen, hu, hv⟩ :=
    exists_fixed_twelve_triple_alignment omega halt hleft hright u v e f huv htgt
  exact ⟨word, hlen, intertwines_of_spanning_target (wordMap omega word)
    (wordMap_injective omega halt word) P Q u v e f hu hv hPu hPv hQe hQf hspan⟩

end AlbertLean.Generic.SymplecticProjectorFrame
