/-
Copyright (c) 2026 FrenzyMath. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.AndersonConjecture.Anderson.AdicLocal
import Tengoku.AndersonConjecture.Anderson.AdicNoetherian
import Tengoku.AndersonConjecture.Anderson.QuasiCompleteRing.Complete
import Tengoku

open scoped Pointwise

/-!
# Anderson's Characterisations of Quasi-Complete Rings

Two results from Anderson (2014). Theorem 4: a Noetherian local
ring R is weakly quasi-complete iff every nonzero prime of its
completion contracts to a nonzero ideal of R. Theorem 5: R is
quasi-complete iff every quotient R/I is weakly quasi-complete.
-/

/-
## Anderson Corollary 2, Part 1 (= Farley Prop 1)

For a Noetherian local domain R:
  R is WQC ↔ for every nonzero prime P of the completion R̂,
  the contraction P ∩ R ≠ ⊥.

Here R̂ = AdicCompletion (IsLocalRing.maximalIdeal R) R,
and contraction = Ideal.comap (algebraMap R R̂).
-/

/-
## Anderson Corollary 2, Part 2

A weakly quasi-complete Noetherian local domain is analytically irreducible.

Proof idea: If R̂ is not a domain, take a minimal prime P of R̂.
Then P ⊆ Z(R̂). But P ∩ R ≠ 0 (WQC), so pick 0 ≠ r ∈ P ∩ R.
Then r ∈ Z(R̂) but r ∉ Z(R) (domain), contradicting flatness of R̂ over R.
-/

/-
## Anderson Corollary 2, Part 3

For a 1-dimensional Noetherian local domain:
  QC ↔ WQC ↔ analytically irreducible.

We state this as two implications + the general QC → WQC.
-/

theorem dim1_qc_iff_wqc
    (R : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] [IsDomain R]
    (hdim : ringKrullDim R = 1) :
    IsQuasiComplete R ↔ IsWeaklyQuasiComplete R := by
  constructor
  · exact IsQuasiComplete.isWeaklyQuasiComplete R
  · intro hwqc A hA k
    set I := ⨅ n, A n with hI_def
    by_cases hI_top : I = ⊤
    · exact ⟨0, by
        rw [hI_top]
        simp⟩
    by_cases hI_bot : I = ⊥
    · obtain ⟨s, hs⟩ := hwqc A hA hI_bot k
      exact ⟨s, fun x hx => Submodule.mem_sup.mpr
        ⟨0, Submodule.zero_mem _, x, hs hx, zero_add x⟩⟩
    · -- ⨅ A ≠ ⊥, ≠ ⊤: R/I is Artinian (dim 0), so chain stabilizes mod I
      have hI_ne_bot : ∃ r ∈ I, r ≠ (0 : R) := by
        by_contra h
        push_neg at h
        exact hI_bot (eq_bot_iff.mpr (fun x hx => Ideal.mem_bot.mpr (h x hx)))
      obtain ⟨r, hrI, hrne⟩ := hI_ne_bot
      have hr_nzd : r ∈ nonZeroDivisors R := mem_nonZeroDivisors_of_ne_zero hrne
      have hle_span : Ideal.span {r} ≤ I :=
        Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrI)
      have hdim_span : ringKrullDim (R ⧸ Ideal.span {r}) + 1 ≤ (1 : WithBot ℕ∞) :=
        (ringKrullDim_quotient_succ_le_of_nonZeroDivisor hr_nzd).trans (le_of_eq hdim)
      have hdim_span_le : ringKrullDim (R ⧸ Ideal.span {r}) ≤ 0 := by
        by_contra hc
        push_neg at hc
        have h1 : (1 : WithBot ℕ∞) ≤ ringKrullDim (R ⧸ Ideal.span {r}) :=
          Order.succ_le_of_lt hc
        have h3 : (1 : WithBot ℕ∞) + 1 ≤ (1 : WithBot ℕ∞) := by
          have h2 : (1 : WithBot ℕ∞) + 1 ≤ ringKrullDim (R ⧸ Ideal.span {r}) + 1 :=
            add_le_add_left h1 1
          exact h2.trans hdim_span
        norm_num at h3
      have hdim_I : ringKrullDim (R ⧸ I) ≤ 0 :=
        (ringKrullDim_le_of_surjective (Ideal.Quotient.factor hle_span)
          (Ideal.Quotient.factor_surjective hle_span)).trans hdim_span_le
      haveI : Nontrivial (R ⧸ I) := Ideal.Quotient.nontrivial_iff.mpr hI_top
      haveI : IsLocalRing (R ⧸ I) :=
        IsLocalRing.of_surjective' (Ideal.Quotient.mk I) Ideal.Quotient.mk_surjective
      haveI : Ring.KrullDimLE 0 (R ⧸ I) := Ring.krullDimLE_iff.mpr hdim_I
      haveI : IsArtinianRing (R ⧸ I) := IsNoetherianRing.isArtinianRing_of_krullDimLE_zero
      set mk := Ideal.Quotient.mk I
      set B : ℕ → Ideal (R ⧸ I) := fun n => Ideal.map mk (A n)
      have hB_anti : Antitone B := fun _ _ hmn => Ideal.map_mono (hA hmn)
      let B' : ℕ →o (Submodule (R ⧸ I) (R ⧸ I))ᵒᵈ :=
        ⟨fun n => OrderDual.toDual (B n), fun _ _ h => hB_anti h⟩
      have hWF : WellFoundedGT (Submodule (R ⧸ I) (R ⧸ I))ᵒᵈ :=
        (wellFoundedGT_dual_iff _).mpr inferInstance
      obtain ⟨N, hN⟩ := hWF.monotone_chain_condition B'
      have hstab : ∀ m, N ≤ m → B N = B m := fun m hm => hN m hm
      have hBinf : ⨅ n, B n = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        rw [Submodule.mem_iInf] at hx
        obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
        suffices y ∈ I by exact Ideal.Quotient.eq_zero_iff_mem.mpr this
        rw [hI_def, Submodule.mem_iInf]
        intro n
        have hyn : mk y ∈ B n := hx n
        obtain ⟨z, hz, hzy⟩ := (Ideal.mem_map_iff_of_surjective mk
          Ideal.Quotient.mk_surjective).mp hyn
        have h_diff : z - y ∈ I := Ideal.Quotient.eq.mp hzy
        have h_diff_An : z - y ∈ A n := iInf_le (A ·) n h_diff
        have := (A n).sub_mem hz h_diff_An
        rwa [sub_sub_cancel] at this
      have hBN_eq : B N = ⨅ n, B n := le_antisymm
        (le_iInf fun n => by
          rcases le_or_gt N n with hle | hlt
          · exact (hstab n hle) ▸ le_refl _
          · exact hB_anti hlt.le)
        (iInf_le _ N)
      have hBN_bot : B N = ⊥ := hBN_eq.trans hBinf
      refine ⟨N, fun x hx => ?_⟩
      have hmkx : mk x ∈ B N := Ideal.mem_map_of_mem mk hx
      rw [hBN_bot, Ideal.mem_bot] at hmkx
      have hxI : x ∈ I := Ideal.Quotient.eq_zero_iff_mem.mp hmkx
      exact Submodule.mem_sup.mpr ⟨x, hxI, 0, Submodule.zero_mem _, add_zero x⟩

/-
## Anderson Theorem 5, Item 3

A Noetherian local ring R is QC ↔ every homomorphic image R/I is WQC.

The forward direction is in Basic.lean (IsQuasiComplete.quotient_isWeaklyQuasiComplete).
Here we state the full iff.
-/
