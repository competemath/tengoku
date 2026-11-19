/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.GeneralFlagProductShuffle
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.ProductFlagProjection
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.ProductLinearFlagCard
import Lean.Elab.Tactic.Omega

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Recovering the shuffle code of an arbitrary finite product flag
-/

namespace HansenCograph

universe u v

namespace Flag

/-- Read the two coordinate ranks of a maximal chain in a product of finite
nonempty linear orders.  The product cardinality theorem makes the domain have
exactly the length required of a shuffle path.-/
noncomputable def toShufflePath
    {P : Type u} {Q : Type v}
    [LinearOrder P] [Finite P] [Nonempty P]
    [LinearOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) {n m : ℕ}
    (hP : Nat.card P = n + 1) (hQ : Nat.card Q = m + 1) :
    ShufflePath n m := by
  classical
  let _ : Fintype P := Fintype.ofFinite P
  let _ : Fintype Q := Fintype.ofFinite Q
  let _ : BoundedOrder P := Fintype.toBoundedOrder P
  let _ : BoundedOrder Q := Fintype.toBoundedOrder Q
  let _ : Fintype s := Fintype.ofFinite s
  have hcard : Nat.card s = n + m + 1 := prod_card_eq_of_card s hP hQ
  have hcard' : Fintype.card s = n + m + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hP' : Fintype.card P = n + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hP
  have hQ' : Fintype.card Q = m + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hQ
  let e : Fin (n + m + 1) ≃o s := Fintype.orderIsoFinOfCardEq s hcard'
  let eP : Fin (n + 1) ≃o P := Fintype.orderIsoFinOfCardEq P hP'
  let eQ : Fin (m + 1) ≃o Q := Fintype.orderIsoFinOfCardEq Q hQ'
  let left : Fin (n + m + 1) → Fin (n + 1) :=
    fun k ↦ eP.symm (e k).1.1
  let right : Fin (n + m + 1) → Fin (m + 1) :=
    fun k ↦ eQ.symm (e k).1.2
  refine
    { left := left
      right := right
      left_zero := ?_
      right_zero := ?_
      left_last := ?_
      right_last := ?_
      step := ?_
      left_surjective := ?_
      right_surjective := ?_ }
  · have he0 := congrArg Subtype.val e.map_bot
    apply eP.injective
    dsimp [left]
    rw [eP.apply_symm_apply]
    calc
      (e 0).1.1 = (⊥ : P) := congrArg Prod.fst he0
      _ = eP 0 := eP.map_bot.symm
  · have he0 := congrArg Subtype.val e.map_bot
    apply eQ.injective
    dsimp [right]
    rw [eQ.apply_symm_apply]
    calc
      (e 0).1.2 = (⊥ : Q) := congrArg Prod.snd he0
      _ = eQ 0 := eQ.map_bot.symm
  · have helast := congrArg Subtype.val e.map_top
    apply eP.injective
    dsimp [left]
    rw [eP.apply_symm_apply]
    calc
      (e (Fin.last (n + m))).1.1 = (⊤ : P) := congrArg Prod.fst helast
      _ = eP (Fin.last n) := eP.map_top.symm
  · have helast := congrArg Subtype.val e.map_top
    apply eQ.injective
    dsimp [right]
    rw [eQ.apply_symm_apply]
    calc
      (e (Fin.last (n + m))).1.2 = (⊤ : Q) := congrArg Prod.snd helast
      _ = eQ (Fin.last m) := eQ.map_top.symm
  · intro k
    have hkFin : (k.castSucc : Fin (n + m + 1)) ⋖ k.succ := by
      rw [Fin.covBy_iff, Nat.covBy_iff_add_one_eq]
      rfl
    have hkSub : e k.castSucc ⋖ e k.succ :=
      (apply_covBy_apply_iff e).mpr hkFin
    have hk : (e k.castSucc).1 ⋖ (e k.succ).1 :=
      Flag.coe_covBy_coe.mpr hkSub
    rcases Prod.covBy_iff.mp hk with hkP | hkQ
    · exact Or.inl
        ⟨(apply_covBy_apply_iff eP.symm).mpr hkP.1,
         congrArg eQ.symm hkP.2⟩
    · exact Or.inr
        ⟨(apply_covBy_apply_iff eQ.symm).mpr hkQ.1,
         congrArg eP.symm hkQ.2⟩
  · intro i
    have hi : eP i ∈ fstProjection s :=
      (Flag.mem_iff_forall_le_or_ge).2 fun _ _ ↦ le_total _ _
    obtain ⟨z, hz, hzP⟩ := (mem_fstProjection_iff s (eP i)).mp hi
    obtain ⟨k, hk⟩ := e.surjective ⟨z, hz⟩
    refine ⟨k, ?_⟩
    apply eP.injective
    rw [eP.apply_symm_apply]
    calc
      (e k).1.1 = z.1 := congrArg Prod.fst (congrArg Subtype.val hk)
      _ = eP i := hzP
  · intro i
    have hi : eQ i ∈ sndProjection s :=
      (Flag.mem_iff_forall_le_or_ge).2 fun _ _ ↦ le_total _ _
    obtain ⟨z, hz, hzQ⟩ := (mem_sndProjection_iff s (eQ i)).mp hi
    obtain ⟨k, hk⟩ := e.surjective ⟨z, hz⟩
    refine ⟨k, ?_⟩
    apply eQ.injective
    rw [eQ.apply_symm_apply]
    calc
      (e k).1.2 = z.2 := congrArg Prod.snd (congrArg Subtype.val hk)
      _ = eQ i := hzQ

/-- Recover the shuffle path after restricting an arbitrary product flag to
its two projected (and hence linearly ordered) factor flags.-/
noncomputable def projectionShufflePath
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) {n m : ℕ}
    (hP : Nat.card (fstProjection s) = n + 1)
    (hQ : Nat.card (sndProjection s) = m + 1) : ShufflePath n m := by
  classical
  let _ : Nonempty (fstProjection s) :=
    ((fstProjection s).maxChain.nonempty_iff.mp inferInstance).to_subtype
  let _ : Nonempty (sndProjection s) :=
    ((sndProjection s).maxChain.nonempty_iff.mp inferInstance).to_subtype
  exact toShufflePath (restrictToProjections s) hP hQ

/-- Shuffling the projected factor chains with the path recovered from the
restricted chain reconstructs the original product flag.-/
theorem productShuffle_toShufflePath
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q]
    (s : Flag (P × Q)) {n m : ℕ}
    (hP : Nat.card (fstProjection s) = n + 1)
    (hQ : Nat.card (sndProjection s) = m + 1) :
    productShuffle (fstProjection s) (sndProjection s) hP hQ
      (projectionShufflePath s hP hQ) = s := by
  classical
  let _ : Nonempty (fstProjection s) :=
    ((fstProjection s).maxChain.nonempty_iff.mp inferInstance).to_subtype
  let _ : Nonempty (sndProjection s) :=
    ((sndProjection s).maxChain.nonempty_iff.mp inferInstance).to_subtype
  let _ : Fintype (fstProjection s) := Fintype.ofFinite (fstProjection s)
  let _ : Fintype (sndProjection s) := Fintype.ofFinite (sndProjection s)
  let _ : Fintype (restrictToProjections s) :=
    Fintype.ofFinite (restrictToProjections s)
  have hcard : Nat.card (restrictToProjections s) = n + m + 1 :=
    prod_card_eq_of_card (restrictToProjections s) hP hQ
  have hcard' : Fintype.card (restrictToProjections s) = n + m + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hcard
  have hP' : Fintype.card (fstProjection s) = n + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hP
  have hQ' : Fintype.card (sndProjection s) = m + 1 := by
    simpa only [Nat.card_eq_fintype_card] using hQ
  let e : Fin (n + m + 1) ≃o restrictToProjections s :=
    Fintype.orderIsoFinOfCardEq (restrictToProjections s) hcard'
  let eP : Fin (n + 1) ≃o fstProjection s :=
    Fintype.orderIsoFinOfCardEq (fstProjection s) hP'
  let eQ : Fin (m + 1) ≃o sndProjection s :=
    Fintype.orderIsoFinOfCardEq (sndProjection s) hQ'
  apply Flag.ext
  ext z
  change z ∈ Set.range (fun k : Fin (n + m + 1) ↦
      ((eP ((projectionShufflePath s hP hQ).left k)).1,
       (eQ ((projectionShufflePath s hP hQ).right k)).1)) ↔ z ∈ s
  constructor
  · rintro ⟨k, rfl⟩
    have hk : (e k).1 ∈ restrictToProjections s := (e k).2
    change ((e k).1.1.1, (e k).1.2.1) ∈ s at hk
    have hleft :
        (eP ((projectionShufflePath s hP hQ).left k)).1 =
          (e k).1.1.1 := by
      simp [projectionShufflePath, toShufflePath, eP, e]
    have hright :
        (eQ ((projectionShufflePath s hP hQ).right k)).1 =
          (e k).1.2.1 := by
      simp [projectionShufflePath, toShufflePath, eQ, e]
    simpa [hleft, hright] using hk
  · intro hz
    let z' : fstProjection s × sndProjection s :=
      (⟨z.1, (mem_fstProjection_iff s z.1).2 ⟨z, hz, rfl⟩⟩,
       ⟨z.2, (mem_sndProjection_iff s z.2).2 ⟨z, hz, rfl⟩⟩)
    have hz' : z' ∈ restrictToProjections s := by
      simpa [z'] using hz
    obtain ⟨k, hk⟩ := e.surjective ⟨z', hz'⟩
    refine ⟨k, ?_⟩
    have hk' := congrArg Subtype.val hk
    have hleft :
        (eP ((projectionShufflePath s hP hQ).left k)).1 =
          (e k).1.1.1 := by
      simp [projectionShufflePath, toShufflePath, eP, e]
    have hright :
        (eQ ((projectionShufflePath s hP hQ).right k)).1 =
          (e k).1.2.1 := by
      simp [projectionShufflePath, toShufflePath, eQ, e]
    apply Prod.ext
    · calc
        (eP ((projectionShufflePath s hP hQ).left k)).1 =
            (e k).1.1.1 := hleft
        _ = z.1 := by
          simpa [z'] using congrArg (fun w ↦ w.1.1) hk'
    · calc
        (eQ ((projectionShufflePath s hP hQ).right k)).1 =
            (e k).1.2.1 := hright
        _ = z.2 := by
          simpa [z'] using congrArg (fun w ↦ w.2.1) hk'

/-- A complete code for a maximal chain in a product of nonempty finite
partial orders.-/
structure ProductShuffleCode
    (P : Type u) (Q : Type v)
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q] where
  n : ℕ
  m : ℕ
  leftFlag : Flag P
  rightFlag : Flag Q
  left_card : Nat.card leftFlag = n + 1
  right_card : Nat.card rightFlag = m + 1
  path : ShufflePath n m

/-- Decode a factor-chain pair and its lattice path as a product flag.-/
noncomputable def ProductShuffleCode.decode
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q] :
    ProductShuffleCode P Q → Flag (P × Q) := fun c ↦
  productShuffle c.leftFlag c.rightFlag c.left_card c.right_card c.path

/-- Every finite product flag is represented by the existing
`Flag.productShuffle` construction.-/
theorem ProductShuffleCode.decode_surjective
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q] :
    Function.Surjective
      (ProductShuffleCode.decode : ProductShuffleCode P Q → Flag (P × Q)) := by
  intro s
  let n := Nat.card (fstProjection s) - 1
  let m := Nat.card (sndProjection s) - 1
  let _ : Nonempty (fstProjection s) :=
    ((fstProjection s).maxChain.nonempty_iff.mp inferInstance).to_subtype
  let _ : Nonempty (sndProjection s) :=
    ((sndProjection s).maxChain.nonempty_iff.mp inferInstance).to_subtype
  have hfpos : 0 < Nat.card (fstProjection s) := Nat.card_pos
  have hgpos : 0 < Nat.card (sndProjection s) := Nat.card_pos
  have hf : Nat.card (fstProjection s) = n + 1 := by
    dsimp [n]
    omega
  have hg : Nat.card (sndProjection s) = m + 1 := by
    dsimp [m]
    omega
  let code : ProductShuffleCode P Q :=
    { n := n
      m := m
      leftFlag := fstProjection s
      rightFlag := sndProjection s
      left_card := hf
      right_card := hg
      path := projectionShufflePath s hf hg }
  refine ⟨code, ?_⟩
  exact productShuffle_toShufflePath s hf hg

/-- The projections recover both factor flags, and then the fixed-factor
injectivity theorem recovers the path.-/
theorem ProductShuffleCode.decode_injective
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q] :
    Function.Injective
      (ProductShuffleCode.decode : ProductShuffleCode P Q → Flag (P × Q)) := by
  rintro ⟨n, m, f, g, hf, hg, p⟩ ⟨n', m', f', g', hf', hg', p'⟩ h
  change productShuffle f g hf hg p =
    productShuffle f' g' hf' hg' p' at h
  have hff : f = f' := by
    apply Flag.ext
    calc
      (f : Set P) = Prod.fst ''
          (productShuffle f g hf hg p).carrier :=
        (productShuffle_fst_range f g hf hg p).symm
      _ = Prod.fst '' (productShuffle f' g' hf' hg' p').carrier := by
        rw [h]
      _ = (f' : Set P) := productShuffle_fst_range f' g' hf' hg' p'
  have hgg : g = g' := by
    apply Flag.ext
    calc
      (g : Set Q) = Prod.snd ''
          (productShuffle f g hf hg p).carrier :=
        (productShuffle_snd_range f g hf hg p).symm
      _ = Prod.snd '' (productShuffle f' g' hf' hg' p').carrier := by
        rw [h]
      _ = (g' : Set Q) := productShuffle_snd_range f' g' hf' hg' p'
  subst f'
  subst g'
  have hn : n = n' := by omega
  have hm : m = m' := by omega
  subst n'
  subst m'
  have hp : p = p' := by
    apply productShuffle_injective_fixed f g hf hg
    change productShuffle f g hf hg p =
      productShuffle f g hf' hg' p' at h
    simpa using h
  subst p'
  rfl

/-- Exact classification of maximal chains in a product of nonempty finite
partial orders by their two projected flags and a shuffle path.-/
noncomputable def productShuffleEquiv
    {P : Type u} {Q : Type v}
    [PartialOrder P] [Finite P] [Nonempty P]
    [PartialOrder Q] [Finite Q] [Nonempty Q] :
    ProductShuffleCode P Q ≃ Flag (P × Q) :=
  Equiv.ofBijective ProductShuffleCode.decode
    ⟨ProductShuffleCode.decode_injective,
     ProductShuffleCode.decode_surjective⟩

end Flag

end HansenCograph
