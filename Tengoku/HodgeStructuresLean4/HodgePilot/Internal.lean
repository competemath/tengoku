import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Internal direct sums with small support

General-purpose helpers: a family of submodules that vanishes away from one
(resp. two) indices is an internal direct sum iff the surviving member is `⊤`
(resp. the surviving pair is complementary). Stated over an arbitrary `Ring R`
and index type; these complement Mathlib's
`DirectSum.isInternal_submodule_iff_isCompl` (which requires the index TYPE to
have exactly two elements) and `DirectSum.isInternal_ne_bot_iff`. -/

namespace HodgePilot

variable {R : Type*} [Ring R] {M : Type*} [AddCommGroup M] [Module R M]
variable {ι : Type*} [DecidableEq ι]

/-- A family of submodules that is `⊥` away from `i₀` and `⊤` at `i₀` is an
internal direct sum.
@isnad1 id=isintern.2h5v.s7.d9fe0293644b from=translated src=- shape=f14a441a vocab=ffe91a88
-/
theorem isInternal_of_eq_bot {A : ι → Submodule R M} {i₀ : ι}
    (hbot : ∀ i, i ≠ i₀ → A i = ⊥) (htop : A i₀ = ⊤) :
    DirectSum.IsInternal A := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro i
    by_cases h0 : i = i₀
    · subst h0
      have hrest : (⨆ (j : ι) (_ : j ≠ i), A j) = ⊥ :=
        iSup_eq_bot.mpr fun j => iSup_eq_bot.mpr fun hj => hbot j hj
      rw [hrest]
      exact disjoint_bot_right
    · rw [hbot i h0]
      exact disjoint_bot_left
  · refine eq_top_iff.mpr ?_
    rw [← htop]
    exact le_iSup A i₀

/-- A family of submodules that is `⊥` away from two indices carrying
complementary submodules is an internal direct sum.
@isnad1 id=isintern.3h6v.s7.54d0b44e8fbc from=translated src=- shape=e3e8e496 vocab=ed40c457
-/
theorem isInternal_of_isCompl_of_eq_bot {A : ι → Submodule R M} {i₀ i₁ : ι}
    (hne : i₀ ≠ i₁) (hbot : ∀ i, i ≠ i₀ → i ≠ i₁ → A i = ⊥)
    (hcompl : IsCompl (A i₀) (A i₁)) :
    DirectSum.IsInternal A := by
  rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top]
  constructor
  · intro i
    by_cases h0 : i = i₀
    · subst h0
      have hrest : (⨆ (j : ι) (_ : j ≠ i), A j) ≤ A i₁ := by
        refine iSup₂_le fun j hj => ?_
        by_cases h1 : j = i₁
        · exact h1 ▸ le_rfl
        · rw [hbot j hj h1]
          exact bot_le
      exact hcompl.disjoint.mono_right hrest
    · by_cases h1 : i = i₁
      · subst h1
        have hrest : (⨆ (j : ι) (_ : j ≠ i), A j) ≤ A i₀ := by
          refine iSup₂_le fun j hj => ?_
          by_cases h0' : j = i₀
          · exact h0' ▸ le_rfl
          · rw [hbot j h0' hj]
            exact bot_le
        exact hcompl.symm.disjoint.mono_right hrest
      · rw [hbot i h0 h1]
        exact disjoint_bot_left
  · refine eq_top_iff.mpr ?_
    rw [← codisjoint_iff.mp hcompl.codisjoint]
    exact sup_le (le_iSup A i₀) (le_iSup A i₁)

omit [DecidableEq ι] in
/-- For an **independent** family of submodules, the spans of two subfamilies
intersect inside the span of the common subfamily:
`(⨆ i ∈ P, A i) ⊓ (⨆ i ∈ Q, A i) ≤ ⨆ i ∈ P ∩ Q, A i`.

Mathlib has this only for *disjoint* index sets
(`iSupIndep.disjoint_biSup_biSup`) or in distributive lattices
(`biSup_inter_of_pairwise_disjoint`, which needs `Frame`); submodule lattices
are merely modular, so independence has to do the work: every element has a
unique `DFinsupp` decomposition, and a decomposition supported in `P` that
equals one supported in `Q` is supported in both.
@isnad1 id=le.1h6v.s8.b17337637c1e from=translated src=- shape=b1277101 vocab=6f7d7a3e
-/
theorem biSup_inf_biSup_le_of_iSupIndep {A : ι → Submodule R M}
    (hA : iSupIndep A) (P Q : ι → Prop) :
    (⨆ (i) (_ : P i), A i) ⊓ (⨆ (i) (_ : Q i), A i) ≤
      ⨆ (i) (_ : P i ∧ Q i), A i := by
  classical
  intro x hx
  obtain ⟨hxP, hxQ⟩ := Submodule.mem_inf.mp hx
  rw [Submodule.mem_biSup_iff_exists_dfinsupp] at hxP hxQ
  obtain ⟨f, hf⟩ := hxP
  obtain ⟨g, hg⟩ := hxQ
  have hfg : f.filter P = g.filter Q :=
    (iSupIndep_iff_dfinsupp_lsum_injective A).mp hA (hf.trans hg.symm)
  rw [Submodule.mem_biSup_iff_exists_dfinsupp]
  refine ⟨f.filter P, ?_⟩
  have hkey : (f.filter P).filter (fun i => P i ∧ Q i) = f.filter P := by
    ext i
    by_cases hPQ : P i ∧ Q i
    · simp [DFinsupp.filter_apply, hPQ]
    · rcases not_and_or.mp hPQ with hP | hQ
      · simp [DFinsupp.filter_apply, hP]
      · rw [hfg]
        simp [DFinsupp.filter_apply, hQ]
  rw [hkey]
  exact hf

omit [DecidableEq ι] in
/-- Equality form of `biSup_inf_biSup_le_of_iSupIndep`: for an independent
family, `(⨆ i ∈ P, A i) ⊓ (⨆ i ∈ Q, A i) = ⨆ i ∈ P ∩ Q, A i`.
@isnad1 id=eq.1h6v.s8.354656a0be1b from=translated src=- shape=b1277101 vocab=961028bf
-/
theorem biSup_inf_biSup_of_iSupIndep {A : ι → Submodule R M}
    (hA : iSupIndep A) (P Q : ι → Prop) :
    (⨆ (i) (_ : P i), A i) ⊓ (⨆ (i) (_ : Q i), A i) =
      ⨆ (i) (_ : P i ∧ Q i), A i :=
  le_antisymm (biSup_inf_biSup_le_of_iSupIndep hA P Q)
    (le_inf
      (iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : P i) => A i) i hi.1)
      (iSup₂_le fun i hi => le_iSup₂ (f := fun i (_ : Q i) => A i) i hi.2))

end HodgePilot
