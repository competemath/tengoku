import Tengoku.SquarefreeFugledeLean.FugledeAudit.SquarefreeClosure

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

set_option autoImplicit false

namespace FugledeAudit

open Matrix

/--
@isnad1 id=eq.1h3v.s5.5f8e61e8618f from=translated src=- shape=b138d9b4 vocab=11aef550
-/
theorem exact_tiling_cardinality
    {G : Type*} [AddGroup G] [Fintype G] (A T : Finset G)
    (h : IsExactTilingPair A T) : A.card * T.card = Fintype.card G := by
  classical
  let f : {a // a ∈ A} × {t // t ∈ T} → G := fun p => p.1.val + p.2.val
  have hf : Function.Bijective f := by
    constructor
    · intro p r he
      obtain ⟨w, _, hw⟩ := h (f p)
      exact (hw p rfl).trans (hw r he.symm).symm
    · intro x
      obtain ⟨p, hp, _⟩ := h x
      exact ⟨p, hp⟩
  simpa only [Fintype.card_prod, Fintype.card_coe] using
    Fintype.card_congr (Equiv.ofBijective f hf)

/--
@isnad1 id=dvd.1h2v.s5.4c6a47169205 from=translated src=- shape=1c32c009 vocab=50265e29
-/
theorem tile_cardinality_dvd_order
    (N : ℕ) [NeZero N] (A : Finset (ZMod N))
    (h : IsTranslationalTile A) : A.card ∣ N := by
  obtain ⟨T, hT⟩ := h
  exact ⟨T.card, by simpa only [ZMod.card] using (exact_tiling_cardinality A T hT).symm⟩

/--
@isnad1 id=iff.0h3v.s9.5ee1564e3cff from=translated src=- shape=5587a984 vocab=6fd793c2
-/
theorem restricted_hadamard_iff_spectral_pair
    (N : ℕ) [NeZero N] (A Λ : Finset (ZMod N)) :
    IsCyclicSpectralPair A Λ ↔
      A.Nonempty ∧ A.card = Λ.card ∧
      restrictedFourierMatrix A Λ * (restrictedFourierMatrix A Λ)ᴴ = (A.card : ℂ) • 1 := by
  classical
  refine ⟨fun h => ⟨h.1, h.2.1, spectral_pair_row_gram A Λ h⟩, ?_⟩
  rintro ⟨hne, hcard, hgram⟩
  refine ⟨hne, hcard, ?_⟩
  intro ξ hξ μ hμ hne'
  let ξ' : Λ := ⟨ξ, hξ⟩
  let μ' : Λ := ⟨μ, hμ⟩
  have hnm : ξ' ≠ μ' := fun he => hne' (congrArg Subtype.val he)
  have hg := congrArg (fun M : Matrix Λ Λ ℂ => M ξ' μ') hgram
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, restrictedFourierMatrix,
    fourier_entry_product_star, Matrix.smul_apply, Matrix.one_apply, ite_eq_right hnm,
    smul_zero] at hg
  exact (Finset.sum_coe_sort A (fun a => cyclicFourierEntry a (ξ - μ))).symm.trans hg

end FugledeAudit
