import Tengoku.EgzFormalProof.EGZ.Decomposition.Mass

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace EGZ

/--
@isnad1 id=le.1h4v.s5.a83f665c4c54 from=translated src=- shape=89345f11 vocab=b408db43
-/
theorem natMassOn_mono_set {α : Type*} [Fintype α] (w : α → ℕ)
    {S T : Set α} (h : S ⊆ T) : natMassOn w S ≤ natMassOn w T := by
  classical
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a ∈ S
  · simp only [ite_eq_left ha, ite_eq_left (h ha)]
    exact le_rfl
  · simp only [ite_eq_right ha]
    exact Nat.zero_le _

/--
@isnad1 id=le.1h5v.s7.9a43ea041c98 from=translated src=- shape=ead5012b vocab=cc093bd9
-/
theorem slab_mono {p d K T : ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p}
    (h : K ≤ T) : slab ξ K ⊆ slab ξ T := by
  rintro v ⟨z, hz, hmod⟩
  exact ⟨z, hz.trans h, hmod⟩

/--
@isnad1 id=isthinal.2h7v.s7.4cafaaefc00b from=translated src=- shape=f7b54526 vocab=a34624c8
-/
theorem IsThinAlong.mono_width {p d K T : ℕ} [NeZero p]
    {w : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p} {δ : ℝ}
    (hw : IsThinAlong w ξ K δ) (h : K ≤ T) : IsThinAlong w ξ T δ := by
  rw [isThinAlong_iff_natMass] at hw ⊢
  exact hw.trans (by exact_mod_cast natMassOn_mono_set w (slab_mono h))

/--
@isnad1 id=isthicka.2h7v.s7.d90e42b86896 from=translated src=- shape=0e3f99e1 vocab=b55eaeaa
-/
theorem IsThickAlong.mono_width {p d K T : ℕ} [NeZero p]
    {w : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p} {δ : ℝ}
    (hw : IsThickAlong w ξ T δ) (h : K ≤ T) : IsThickAlong w ξ K δ :=
  fun hthin ↦ hw (hthin.mono_width h)

/--
@isnad1 id=isthinal.2h7v.s7.644fff2f9c6d from=translated src=- shape=2714da5e vocab=a34624c8
-/
theorem IsThinAlong.mono_error {p d K : ℕ} [NeZero p]
    {w : FpCoord p d → ℕ} {ξ : FpCoord p d →ᵃ[ZMod p] ZMod p} {δ δ' : ℝ}
    (hw : IsThinAlong w ξ K δ) (h : δ ≤ δ') : IsThinAlong w ξ K δ' := by
  rw [isThinAlong_iff_natMass] at hw ⊢
  exact (mul_le_mul_of_nonneg_right (sub_le_sub_left h 1) (Nat.cast_nonneg _)).trans hw

/--
@isnad1 id=iscomple.2h8v.s5.16bb22b68820 from=translated src=- shape=f143b045 vocab=f9007e5d
-/
theorem FlagDecomposition.IsCompleteElement.mono_width {p d K T : ℕ} [NeZero p]
    {f : FpCoord p d → ℕ} {Φ : FlagDecomposition p d f} {x : Φ.flag.Node} {δ : ℝ}
    (hw : Φ.IsCompleteElement x T δ) (h : K ≤ T) : Φ.IsCompleteElement x K δ :=
  fun ξ hξ ↦ (hw ξ hξ).mono_width h

end EGZ
