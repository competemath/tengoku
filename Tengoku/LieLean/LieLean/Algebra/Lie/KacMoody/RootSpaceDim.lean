/-
Copyright (c) 2026 Alex Ellis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex Ellis
-/
import Tengoku.Seed.Data.List.Count
import Tengoku.Seed.Data.Set.Finite.List
import Tengoku.LieLean.LieLean.Algebra.Lie.KacMoody.RootSpace
import Tengoku.LieLean.LieLean.Algebra.Lie.Subalgebra

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Root spaces of `𝔤̃(A)`: spanning sets, finite-dimensionality, simple roots

For `α ∈ Q₊ \ {0}`, the root space `𝔤̃_α` is spanned by the iterated brackets
`[e_{i₁}, [e_{i₂}, ⋯ [e_{iₖ}, e_j] ⋯]]` with `α_{i₁} + ⋯ + α_{iₖ} + α_j = α` ([Kac] Thm. 1.2 (b),
(d) and its proof).

## Main definitions

* `Matrix.Realization.AuxLieAlgebra.posSpan`: the span of the iterated brackets
  `[e_{i₁}, [⋯ [e_{iₖ}, e_j] ⋯]]` of weight `μ`.

## Main results

* `Matrix.Realization.AuxLieAlgebra.rootSpace_le_posSpan`: `𝔤̃_α` is spanned by iterated brackets
  of weight `α`.
* `Matrix.Realization.AuxLieAlgebra.finiteDimensional_rootSpace`: `dim 𝔤̃_α < ∞` for `α ≠ 0`.
* `Matrix.Realization.AuxLieAlgebra.rootSpace_nsmul_root_eq_bot`: `𝔤̃_{k αᵢ} = 0` for `k ≥ 2`.
* `Matrix.Realization.AuxLieAlgebra.rootSpace_root`: `𝔤̃_{αᵢ} = K eᵢ`.
* Negative versions via the Chevalley involution.

## References

* [Kac] V. G. Kac, *Infinite dimensional Lie algebras*, 3rd ed., CUP 1990, Thm. 1.2, (1.3.3)
  (stated over `ℂ`).
-/

open FreeLieAlgebra Module LieModule LieAlgebra

noncomputable section

namespace Matrix.Realization

variable {ι K H : Type*} [Fintype ι] [DecidableEq ι] [Field K] [AddCommGroup H] [Module K H]
  {A : Matrix ι ι ℤ} (P : Realization A K H)

namespace AuxLieAlgebra

/-- The letter counts of a word, as an element of the root lattice.-/
def counts (w : List ι) : ι → ℤ := fun i ↦ (w.count i : ℤ)

omit [Fintype ι] in
/--
@isnad1 id=eq.0h1v.s5.5a2ed9b7f415 from=translated src=- shape=b7e5311c vocab=0086dc43
-/
@[simp] lemma counts_nil : counts ([] : List ι) = 0 := by ext; simp [counts]

omit [Fintype ι] in
/--
@isnad1 id=eq.0h3v.s6.bdd204721125 from=translated src=- shape=fb640fb4 vocab=7a016eab
-/
@[simp] lemma counts_cons (j : ι) (w : List ι) : counts (j :: w) = Pi.single j 1 + counts w := by
  ext i
  simp only [counts, List.count_cons, Pi.add_apply, Pi.single_apply, beq_iff_eq]
  split_ifs <;> subst_vars <;> simp_all; ring

/--
@isnad1 id=eq.0h6v.s8.f0a1748f1cf7 from=translated src=- shape=3e66f58f vocab=51b47820
-/
lemma wordWt_eq_rootOf (w : List ι) : wordWt P w = P.rootOf (counts w) := by
  induction w with
  | nil => simp
  | cons j w ih => simp [ih, map_add]

omit [Fintype ι] in
/--
@isnad1 id=eq.0h2v.s5.1f86236a0559 from=translated src=- shape=72f5f1d6 vocab=a819f667
-/
lemma sum_counts (w : List ι) [Fintype ι] : ∑ i, counts w i = w.length := by
  induction w with
  | nil => simp
  | cons j w ih => simp [Finset.sum_add_distrib, ih, Pi.single_apply]; ring

/-- The span of the iterated brackets `[e_{i₁}, [⋯ [e_{iₖ}, e_j] ⋯]]` of weight `μ`.-/
def posSpan (μ : Dual K H) : Submodule K P.AuxLieAlgebra :=
  Submodule.span K {x | ∃ (j : ι) (l : List ι), wordWt P (j :: l) = μ ∧
    x = adProd (l.map (e P)) (e P j)}

/--
@isnad1 id=mem.0h7v.s9.2200707d59f1 from=translated src=- shape=f3e5a88a vocab=4ed249cb
-/
lemma adProd_mem_rootSpace (j : ι) (l : List ι) :
    adProd (l.map (e P)) (e P j) ∈ rootSpace P (wordWt P (j :: l)) := by
  induction l with
  | nil => simpa using e_mem_rootSpace P j
  | cons i l ih =>
    rw [List.map_cons, adProd_cons]
    have := lie_mem_rootSpace P (e_mem_rootSpace P i) ih
    convert this using 2
    simp only [wordWt_cons]
    abel

/--
@isnad1 id=le.0h6v.s10.6871586d29bb from=translated src=- shape=bc4f0a97 vocab=226a0d68
-/
lemma posSpan_le (μ : Dual K H) : posSpan P μ ≤ rootSpace P μ := by
  rw [posSpan, Submodule.span_le]
  rintro _ ⟨j, l, rfl, rfl⟩
  exact adProd_mem_rootSpace P j l

/--
@isnad1 id=mem.0h6v.s9.e6fa58ae4467 from=translated src=- shape=be27443a vocab=90ec014c
-/
lemma eHom_mem_lieSpan (z : FreeLieAlgebra K ι) :
    eHom P z ∈ LieSubalgebra.lieSpan K P.AuxLieAlgebra (Set.range (e P)) := by
  induction z using FreeLieAlgebra.induction_on with
  | of i => exact LieSubalgebra.subset_lieSpan ⟨i, (eHom_of P i).symm⟩
  | zero => simp
  | add y z hy hz => rw [map_add]; exact add_mem hy hz
  | smul c y hy => rw [map_smul]; exact LieSubalgebra.smul_mem _ c hy
  | lie y z hy hz => rw [LieHom.map_lie]; exact LieSubalgebra.lie_mem _ hy hz

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=ex.1h4v.s5.57192449cb29 from=translated src=- shape=62c39ab0 vocab=0c2c4bc5
-/
lemma _root_.List.exists_map_eq_of_forall_mem_range {α β : Type*} {f : α → β} {l : List β}
    (hl : ∀ y ∈ l, y ∈ Set.range f) : ∃ l' : List α, l'.map f = l := by
  induction l with
  | nil => exact ⟨[], rfl⟩
  | cons y l ih =>
    obtain ⟨a, rfl⟩ := hl y (List.mem_cons_self ..)
    obtain ⟨l', rfl⟩ := ih fun z hz ↦ hl z (List.mem_cons_of_mem _ hz)
    exact ⟨a :: l', rfl⟩

/--
@isnad1 id=mem.0h6v.s11.fddfedcf4b5e from=translated src=- shape=eab75e53 vocab=d46bc140
-/
lemma eHom_mem_iSup_posSpan (z : FreeLieAlgebra K ι) : eHom P z ∈ ⨆ μ, posSpan P μ := by
  have hz : eHom P z ∈ (LieSubalgebra.lieSpan K P.AuxLieAlgebra (Set.range (e P))).toSubmodule :=
    eHom_mem_lieSpan P z
  rw [LieSubalgebra.lieSpan_toSubmodule_eq_span_adProd] at hz
  refine (Submodule.span_le.mpr ?_) hz
  rintro _ ⟨l, hl, _, ⟨j, rfl⟩, rfl⟩
  obtain ⟨l', rfl⟩ := List.exists_map_eq_of_forall_mem_range hl
  exact Submodule.mem_iSup_of_mem (wordWt P (j :: l'))
    (Submodule.subset_span ⟨j, l', rfl, rfl⟩)

variable [CharZero K]

/-- For `α ∈ Q₊ \ {0}`, the root space `𝔤̃_α` is spanned by the iterated brackets
`[e_{i₁}, [⋯ [e_{iₖ}, e_j] ⋯]]` of weight `α`.
@isnad1 id=le.1h6v.s10.9e951c63c068 from=translated src=- shape=88939665 vocab=e64b8116
-/
theorem rootSpace_le_posSpan {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    rootSpace P μ ≤ posSpan P μ := by
  intro x hx
  obtain ⟨z, rfl⟩ : ∃ z, eHom P z = x := rootSpace_pos_le P hμ hx
  exact mem_of_mem_iSup_of_le (h P) (posSpan P) (posSpan_le P) hx (eHom_mem_iSup_posSpan P z)

omit [DecidableEq ι] in
/--
@isnad1 id=finite.0h6v.s8.db2293cd680b from=translated src=- shape=945152dd vocab=8f1afe75
-/
lemma finite_setOf_wordWt_eq (k : ι → ℤ) :
    {w : ι × List ι | wordWt P (w.1 :: w.2) = P.rootOf k}.Finite := by
  classical
  refine (Set.finite_univ.prod (List.finite_length_eq ι ((∑ i, k i).toNat - 1))).subset ?_
  rintro ⟨j, l⟩ hw
  simp only [Set.mem_ofPred_eq, wordWt_eq_rootOf, P.rootOf_injective.eq_iff] at hw
  have := sum_counts (j :: l)
  rw [hw] at this
  simp only [Set.mem_prod, Set.mem_univ, Set.mem_ofPred_eq, true_and]
  simp only [List.length_cons] at this
  omega

/-- The root spaces `𝔤̃_α`, `α ∈ Q₊ \ {0}`, are finite-dimensional ([Kac] Thm. 1.2 (d)).
@isnad1 id=finitedi.1h6v.s10.b03bd1302cc1 from=translated src=- shape=3bcd7590 vocab=3293475e
-/
theorem finiteDimensional_rootSpace {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    FiniteDimensional K (rootSpace P μ) := by
  obtain ⟨k, hk, rfl⟩ := hμ
  have hfin : (posSpan P (P.rootOf k) : Submodule K P.AuxLieAlgebra).FG := by
    rw [posSpan]
    refine Submodule.fg_def.mpr ⟨_, ((finite_setOf_wordWt_eq P k).image
      fun w ↦ adProd (w.2.map (e P)) (e P w.1)), ?_⟩
    congr 1
    ext x
    simp only [Set.mem_image, Set.mem_ofPred_eq, Prod.exists]
    constructor
    · rintro ⟨j, l, h, rfl⟩; exact ⟨j, l, h, rfl⟩
    · rintro ⟨j, l, h, rfl⟩; exact ⟨j, l, h, rfl⟩
  have : FiniteDimensional K (posSpan P (P.rootOf k)) :=
    Module.Finite.iff_fg.mpr hfin
  exact Submodule.finiteDimensional_of_le (rootSpace_le_posSpan P ⟨k, hk, rfl⟩)

omit [Fintype ι] [DecidableEq ι] in
/--
@isnad1 id=eq.0h3v.s5.bde5beb40a57 from=translated src=- shape=89bbb5b6 vocab=0403ef10
-/
lemma adProd_replicate_self {L : Type*} [LieRing L] (x : L) (m : ℕ) :
    adProd (List.replicate (m + 1) x) x = 0 := by
  induction m with
  | zero => simp
  | succ m ih => rw [List.replicate_succ, adProd_cons, ih, lie_zero]

omit [Fintype ι] in
lemma eq_replicate_of_counts_eq {j : ι} {l : List ι} {i : ι} {n : ℕ}
    (h : counts (j :: l) = n • Pi.single i 1) : j = i ∧ l = List.replicate (n - 1) i := by
  have hmem : ∀ b ∈ j :: l, b = i := by
    intro b hb
    by_contra hbi
    have := congr_fun h b
    simp only [counts, Pi.smul_apply, Pi.single_apply, hbi, ite_false, smul_zero,
      Nat.cast_eq_zero, List.count_eq_zero] at this
    exact this hb
  have hlen := congr_fun h i
  simp only [counts, Pi.smul_apply, Pi.single_eq_same, nsmul_eq_mul, mul_one] at hlen
  rw [List.count_eq_length.mpr fun b hb ↦ (hmem b hb).symm] at hlen
  refine ⟨hmem j (List.mem_cons_self ..), List.eq_replicate_iff.mpr ⟨?_, fun b hb ↦
    hmem b (List.mem_cons_of_mem _ hb)⟩⟩
  simp only [List.length_cons] at hlen
  omega

/-- `𝔤̃_{k αᵢ} = 0` for `k ≥ 2` ([Kac] (1.3.3), stated there for `𝔤(A)`; the same
argument applies to `𝔤̃(A)`).
@isnad1 id=eq.1h7v.s9.63a94377edce from=translated src=- shape=d62db246 vocab=ece422c2
-/
theorem rootSpace_nsmul_root_eq_bot (i : ι) {n : ℕ} (hn : 2 ≤ n) :
    rootSpace P (n • P.root i) = ⊥ := by
  have hw : n • P.root i = P.rootOf (n • Pi.single i 1) := by rw [map_nsmul, rootOf_single]
  have hpos : n • P.root i ∈ P.posWeights := by
    refine ⟨n • Pi.single i 1, ⟨fun m ↦ ?_, fun h ↦ ?_⟩, hw.symm⟩
    · by_cases hm : m = i
      · subst hm; simp
      · simp [hm]
    · have := congr_fun h i; simp at this; omega
  refine eq_bot_iff.mpr ((rootSpace_le_posSpan P hpos).trans ?_)
  rw [posSpan, Submodule.span_le]
  rintro _ ⟨j, l, hjl, rfl⟩
  rw [hw, wordWt_eq_rootOf, P.rootOf_injective.eq_iff] at hjl
  obtain ⟨rfl, rfl⟩ := eq_replicate_of_counts_eq hjl
  obtain ⟨m, hm⟩ : ∃ m, n - 1 = m + 1 := ⟨n - 2, by omega⟩
  rw [hm, List.map_replicate, adProd_replicate_self]
  exact Submodule.zero_mem _

/-- `𝔤̃_{αᵢ} = K eᵢ` ([Kac] (1.3.3), stated there for `𝔤(A)`; the same argument
applies to `𝔤̃(A)`).
@isnad1 id=eq.0h6v.s9.3d50e2e573a9 from=translated src=- shape=6fa6e196 vocab=22bac41f
-/
theorem rootSpace_root (i : ι) : rootSpace P (P.root i) = K ∙ e P i := by
  refine le_antisymm ?_ ((Submodule.span_singleton_le_iff_mem _ _).mpr (e_mem_rootSpace P i))
  have hw : P.root i = P.rootOf (Pi.single i 1) := by simp
  have hpos : P.root i ∈ P.posWeights := P.root_mem_posWeights i
  refine (rootSpace_le_posSpan P hpos).trans ?_
  rw [posSpan, Submodule.span_le]
  rintro _ ⟨j, l, hjl, rfl⟩
  rw [hw, wordWt_eq_rootOf, P.rootOf_injective.eq_iff, ← one_nsmul (Pi.single i 1)] at hjl
  obtain ⟨rfl, rfl⟩ := eq_replicate_of_counts_eq hjl
  exact Submodule.mem_span_singleton_self _

/-! ### Negative root spaces -/

omit [CharZero K] in
/--
@isnad1 id=mem.1h7v.s11.e17f6f42309d from=translated src=- shape=18f48415 vocab=a32631c3
-/
lemma chevalleyInvolution_mem_rootSpace {μ : Dual K H} {x : P.AuxLieAlgebra}
    (hx : x ∈ rootSpace P μ) : chevalleyInvolution P x ∈ rootSpace P (-μ) := by
  intro a
  have := congr_arg (chevalleyInvolution P) (hx (-a))
  simp only [LieHom.map_lie, map_neg, chevalleyInvolution_h, neg_neg, map_smul] at this
  rw [this, LinearMap.neg_apply, neg_smul]

omit [CharZero K] in
/-- `𝔤̃_{-μ} = ω(𝔤̃_μ)`, where `ω` is the Chevalley involution.
@isnad1 id=eq.0h6v.s9.8beb17b065c4 from=translated src=- shape=fc646f97 vocab=8bcb75a9
-/
lemma rootSpace_neg_eq_map (μ : Dual K H) :
    rootSpace P (-μ) = (rootSpace P μ).map (chevalleyInvolution P).toLinearMap := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · refine ⟨chevalleyInvolution P x, ?_, by simp⟩
    simpa using chevalleyInvolution_mem_rootSpace P hx
  · rintro _ ⟨x, hx, rfl⟩
    exact chevalleyInvolution_mem_rootSpace P hx

/-- The root spaces `𝔤̃_{-α}`, `α ∈ Q₊ \ {0}`, are finite-dimensional.
@isnad1 id=finitedi.1h6v.s10.0a4cdbbe851c from=translated src=- shape=50d616bd vocab=bc289494
-/
theorem finiteDimensional_rootSpace_neg {μ : Dual K H} (hμ : μ ∈ P.posWeights) :
    FiniteDimensional K (rootSpace P (-μ)) := by
  have := finiteDimensional_rootSpace P hμ
  rw [rootSpace_neg_eq_map]
  infer_instance

/-- `𝔤̃_{-k αᵢ} = 0` for `k ≥ 2`.
@isnad1 id=eq.1h7v.s9.4011a60ac5f7 from=translated src=- shape=d488a44a vocab=4f518c2f
-/
theorem rootSpace_neg_nsmul_root_eq_bot (i : ι) {n : ℕ} (hn : 2 ≤ n) :
    rootSpace P (-(n • P.root i)) = ⊥ := by
  rw [rootSpace_neg_eq_map, rootSpace_nsmul_root_eq_bot P i hn, Submodule.map_bot]

/-- `𝔤̃_{-αᵢ} = K fᵢ`.
@isnad1 id=eq.0h6v.s9.b5dcc32f7eaa from=translated src=- shape=72f69298 vocab=2d863add
-/
theorem rootSpace_neg_root (i : ι) : rootSpace P (-P.root i) = K ∙ f P i := by
  rw [rootSpace_neg_eq_map, rootSpace_root, Submodule.map_span, Set.image_singleton,
    LieHom.coe_toLinearMap, chevalleyInvolution_e, ← Set.neg_singleton, Submodule.span_neg]

end AuxLieAlgebra

end Matrix.Realization

end
