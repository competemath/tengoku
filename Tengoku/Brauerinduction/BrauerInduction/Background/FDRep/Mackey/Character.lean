import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Mackey.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Basic
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Orthogonality
import Tengoku.Brauerinduction.BrauerInduction.Background.FDRep.Character.Induced
import Tengoku.Brauerinduction.BrauerInduction.Background.Fintype.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! # Character computation for Mackey Hom terms

This file computes the dimensions of the Mackey Hom terms introduced in
`FDRep.Mackey.Basic` using character inner products.

The final result expresses

`finrank End(Ind_I^G σ)`

as a sum over double cosets of the dimensions of the corresponding Mackey Hom
terms. -/

open CategoryTheory BigOperators

universe u v

namespace FDRep

variable {k : Type u} [Field k]
variable {G : Type v} [Group G]

/--
The character of the left Mackey restriction is the restriction of `σ.character`
through the left inclusion into `I`.-/
@[simp] lemma char_mackeyLeftRes
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (g : G)
    (h : mackeyIntersection I g) :
    (mackeyLeftRes (k := k) I σ g).character h
      =
    σ.character ⟨(h : G), h.2.1⟩ := by
  rfl

/--
The Mackey Hom-term dimension formula with the two restricted characters
expanded explicitly in terms of `σ.character`.-/
@[simp] lemma char_mackeyConjRes
    [Finite G]
    (I : Subgroup G) (σ : FDRep k I) (g : G)
    (h : mackeyIntersection I g) :
    (mackeyConjRes (k := k) I σ g).character h
      =
    σ.character
      (((MulAut.conj g).subgroupMap I).symm
        ⟨(h : G), h.2.2⟩) := by
  change
    (FDRep.conjMap (k := k) I g σ).character
      ⟨(h : G), h.2.2⟩
      =
    σ.character
      (((MulAut.conj g).subgroupMap I).symm
        ⟨(h : G), h.2.2⟩)
  rfl

/--
For fixed `g : G` and `(a, b) : I × I`, the inner summation condition in the
double-coset parameterization is equivalent to membership in the Mackey
intersection `I ∩ gIg⁻¹`.-/
noncomputable def mackeyParameterizationInnerEquiv
    (I : Subgroup G)
    (g : G)
    (p : I × I) :
    { i : I //
        DoubleCoset.parameterization I g p * (i : G) *
          (DoubleCoset.parameterization I g p)⁻¹ ∈ I }
      ≃
    mackeyIntersection I g := by
  rcases p with ⟨a, b⟩
  let H : Subgroup G := mackeyIntersection I g
  refine
    { toFun := ?toFun
      invFun := ?invFun
      left_inv := ?left_inv
      right_inv := ?right_inv }
  · intro i
    let hG : G := g * (b : G)⁻¹ * (i.1 : G)⁻¹ * (b : G) * g⁻¹
    have hI : hG ∈ I := by
      have hi :
          ((a : G)⁻¹ * g * (b : G)⁻¹ * (i.1 : G) *
            (b : G) * g⁻¹ * (a : G)) ∈ I := by
        simpa [DoubleCoset.parameterization, mul_assoc] using i.2
      have hi_inv :
          (((a : G)⁻¹ * g * (b : G)⁻¹ * (i.1 : G) *
            (b : G) * g⁻¹ * (a : G))⁻¹) ∈ I :=
        I.inv_mem hi
      have hconj :
          (a : G) *
            (((a : G)⁻¹ * g * (b : G)⁻¹ * (i.1 : G) *
              (b : G) * g⁻¹ * (a : G))⁻¹) *
            (a : G)⁻¹ ∈ I :=
        I.mul_mem (I.mul_mem a.2 hi_inv) (I.inv_mem a.2)
      simpa [hG, mul_assoc] using hconj
    have hIg : hG ∈ I.map (MulAut.conj g).toMonoidHom := by
      refine (Subgroup.mem_map).2 ?_
      refine ⟨(b : G)⁻¹ * (i.1 : G)⁻¹ * (b : G),
        I.mul_mem (I.mul_mem (I.inv_mem b.2) (I.inv_mem i.1.2)) b.2, ?_⟩
      simp [hG, MulAut.conj_apply, mul_assoc]
    exact ⟨hG, ⟨hI, hIg⟩⟩
  · intro h
    let iG : G := (b : G) * g⁻¹ * (h : G)⁻¹ * g * (b : G)⁻¹
    have hi_mem : iG ∈ I := by
      have hhIg : (h : G) ∈ I.map (MulAut.conj g).toMonoidHom := h.2.2
      have hpre :
          (MulAut.conj g).symm (h : G) ∈ I :=
        (Subgroup.mem_map_equiv
          (f := MulAut.conj g) (K := I) (x := (h : G))).1 hhIg
      have hpre_inv :
          ((MulAut.conj g).symm (h : G))⁻¹ ∈ I :=
        I.inv_mem hpre
      have hpre_inv' : g⁻¹ * (h : G)⁻¹ * g ∈ I := by
        simpa [MulAut.conj_symm_apply, mul_assoc] using hpre_inv
      have hleft :
          (b : G) * (g⁻¹ * (h : G)⁻¹ * g) ∈ I :=
        I.mul_mem b.2 hpre_inv'
      simpa [iG, mul_assoc] using
        I.mul_mem hleft (I.inv_mem b.2)
    refine ⟨⟨iG, hi_mem⟩, ?_⟩
    have hhI : (h : G) ∈ I := h.2.1
    have hcond :
        (a : G)⁻¹ * (h : G)⁻¹ * (a : G) ∈ I :=
      I.mul_mem (I.mul_mem (I.inv_mem a.2) (I.inv_mem hhI)) a.2
    simpa [DoubleCoset.parameterization, iG, mul_assoc] using hcond
  · intro i
    apply Subtype.ext
    apply Subtype.ext
    simp [DoubleCoset.parameterization, mul_assoc]
  · intro h
    apply Subtype.ext
    simp [mul_assoc]

/--
Under `mackeyParameterizationInnerEquiv`, the inner summand in the double-coset
parameterization agrees with the expanded Mackey Hom-term summand.-/
lemma mackey_parameterization_inner_summand_eq_expanded
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G)
    (p : I × I)
    (i :
      {i : I //
        DoubleCoset.parameterization I g p * (i : G) *
          (DoubleCoset.parameterization I g p)⁻¹ ∈ I}) :
    let h : mackeyIntersection I g :=
      (mackeyParameterizationInnerEquiv
        (I := I) (g := g) (p := p)) i
    σ.character
        ⟨DoubleCoset.parameterization I g p * (i.1 : G) *
          (DoubleCoset.parameterization I g p)⁻¹, i.2⟩ *
      σ.character i.1⁻¹
      =
    σ.character
        (((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩)
      *
      σ.character
        (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩) := by
  intro h
  rcases p with ⟨a, b⟩
  have h_val : (h : G) = g * (b : G)⁻¹ * (i.1 : G)⁻¹ * (b : G) * g⁻¹ := by
    dsimp [h, mackeyParameterizationInnerEquiv]
  have h_left :
      (⟨DoubleCoset.parameterization I g (a, b) * (i.1 : G) *
        (DoubleCoset.parameterization I g (a, b))⁻¹, i.2⟩ : I)
        =
      a⁻¹ * ⟨(h : G)⁻¹, I.inv_mem h.2.1⟩ * a := by
    ext
    dsimp [DoubleCoset.parameterization]
    rw [h_val]
    group
  have h_right :
      (((MulAut.conj g).subgroupMap I).symm ⟨(h : G), h.2.2⟩)
        =
      b⁻¹ * i.1⁻¹ * b := by
    ext
    change (MulAut.conj g).symm (h : G) = (b : G)⁻¹ * (i.1 : G)⁻¹ * (b : G)
    rw [h_val]
    simp [MulAut.conj_symm_apply]
    group
  rw [h_left, h_right]
  have h_char_a :
      σ.character (a⁻¹ * ⟨(h : G)⁻¹, I.inv_mem h.2.1⟩ * a)
        =
      σ.character ⟨(h : G)⁻¹, I.inv_mem h.2.1⟩ := by
    simpa [mul_assoc] using FDRep.char_conj σ ⟨(h : G)⁻¹, I.inv_mem h.2.1⟩ a⁻¹

  have h_char_b :
      σ.character (b⁻¹ * i.1⁻¹ * b)
        =
      σ.character i.1⁻¹ := by
    simpa [mul_assoc] using FDRep.char_conj σ i.1⁻¹ b⁻¹
  rw [h_char_a, h_char_b, mul_comm]

open Classical in
/--
The inner sum over `I` in the double-coset parameterization is equal to the
expanded character sum over the Mackey intersection.-/
lemma mackey_parameterization_inner_sum_eq_expanded
    [Fintype G]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G)
    (p : I × I) :
    let H : Subgroup G := mackeyIntersection I g
    (∑ i : I,
      if h : DoubleCoset.parameterization I g p * (i : G) *
          (DoubleCoset.parameterization I g p)⁻¹ ∈ I
      then
        σ.character
          ⟨DoubleCoset.parameterization I g p * (i : G) *
            (DoubleCoset.parameterization I g p)⁻¹, h⟩ *
          σ.character i⁻¹
      else 0)
    =
    (∑ h : H,
      σ.character
        (((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩)
      *
      σ.character
        (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩)) := by
  intro H

  let P : I → Prop := fun i =>
    DoubleCoset.parameterization I g p * (i : G) *
      (DoubleCoset.parameterization I g p)⁻¹ ∈ I

  let T : {i : I // P i} → k := fun i =>
    σ.character
        ⟨DoubleCoset.parameterization I g p * (i.1 : G) *
          (DoubleCoset.parameterization I g p)⁻¹, i.2⟩ *
      σ.character i.1⁻¹

  let U : H → k := fun h =>
    σ.character
        (((MulAut.conj g).subgroupMap I).symm
          ⟨(h : G), h.2.2⟩)
      *
      σ.character
        (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩)

  let e : {i : I // P i} ≃ H := by
    simpa [H, P] using
      (mackeyParameterizationInnerEquiv
        (I := I) (g := g) (p := p))

  have hsplit :
      (∑ i : I,
        if h : P i
        then
          σ.character
            ⟨DoubleCoset.parameterization I g p * (i : G) *
              (DoubleCoset.parameterization I g p)⁻¹, h⟩ *
            σ.character i⁻¹
        else 0)
        =
      ∑ i : {i : I // P i}, T i := by
    simpa [T, P] using
      (Fintype.sum_dite_eq_sum_subtype
        (P := P)
        (f := fun i h =>
          σ.character
            ⟨DoubleCoset.parameterization I g p * (i : G) *
              (DoubleCoset.parameterization I g p)⁻¹, h⟩ *
            σ.character i⁻¹))

  have hpoint :
      ∀ i : {i : I // P i}, T i = U (e i) := by
    intro i
    dsimp [T, U, e]
    simpa [P, H] using
      (mackey_parameterization_inner_summand_eq_expanded
        (I := I) (σ := σ) (g := g) (p := p) i)

  calc
    (∑ i : I,
      if h : DoubleCoset.parameterization I g p * (i : G) *
          (DoubleCoset.parameterization I g p)⁻¹ ∈ I
      then
        σ.character
          ⟨DoubleCoset.parameterization I g p * (i : G) *
            (DoubleCoset.parameterization I g p)⁻¹, h⟩ *
          σ.character i⁻¹
      else 0)
        =
      ∑ i : {i : I // P i}, T i := by
        simpa [P] using hsplit
    _ =
      ∑ h : H, U h := by
        exact Fintype.sum_equiv e T U hpoint
    _ =
      ∑ h : H,
        σ.character
          (((MulAut.conj g).subgroupMap I).symm
            ⟨(h : G), h.2.2⟩)
        *
        σ.character
          (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩) := by
        rfl

open Classical in
/--
The product sum over `I × I` associated to a double-coset representative is
`|I|²` times the expanded Mackey-intersection character sum.-/
lemma mackey_product_sum_eq_card_sq_mul_expanded_sum
    [Fintype G]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) :
    let H : Subgroup G := mackeyIntersection I g
    let F : G → k := fun x =>
      ∑ i : I,
        if h : x * (i : G) * x⁻¹ ∈ I
        then σ.character ⟨x * (i : G) * x⁻¹, h⟩ * σ.character i⁻¹
        else 0
    ∑ p : I × I, F (DoubleCoset.parameterization I g p)
      =
    (Nat.card I : k) * (Nat.card I : k) *
      ∑ h : H,
        σ.character
          (((MulAut.conj g).subgroupMap I).symm
            ⟨(h : G), h.2.2⟩)
        *
        σ.character
          (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩) := by
  intro H F
  have hpoint :
      ∀ p : I × I,
        F (DoubleCoset.parameterization I g p)
          =
        ∑ h : H,
          σ.character
            (((MulAut.conj g).subgroupMap I).symm
              ⟨(h : G), h.2.2⟩)
          *
          σ.character
            (⟨(h⁻¹ : G), I.inv_mem h.2.1⟩) := by
    intro p
    simpa [F, H] using
      (mackey_parameterization_inner_sum_eq_expanded
        (I := I) (σ := σ) (g := g) p)
  simp only [hpoint, MulEquiv.subgroupMap_symm_apply, MulAut.conj_symm_apply, Finset.sum_const,
    Finset.card_univ, Fintype.card_prod, nsmul_eq_mul, Nat.cast_mul, Nat.card_eq_fintype_card]

/--
The inner character sum appearing in the Mackey character computation. For fixed
`x : G`, this is the sum over `i : I` occurring inside the double-coset element
sum.-/
noncomputable def mackeyCharacterInnerSum
    [Finite G]
    (I : Subgroup G)
    (σ : FDRep k I)
    (x : G) : k := by
  letI : Fintype G := Fintype.ofFinite G
  classical
  exact
    ∑ i : I,
      if h : x * (i : G) * x⁻¹ ∈ I
      then σ.character ⟨x * (i : G) * x⁻¹, h⟩ * σ.character i⁻¹
      else 0

/--
The explicit element sum over the double coset of a representative `g`.-/
noncomputable def mackeyDoubleCosetElementSum
    [Finite G]
    (I : Subgroup G)
    (σ : FDRep k I)
    (g : G) : k := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  exact
    ∑ x ∈ (DoubleCoset.doubleCoset g I I).toFinset,
      mackeyCharacterInnerSum I σ x

/--
By Frobenius reciprocity, the endomorphism dimension of `Ind_I^G σ` agrees with
the dimension of `Hom(σ, Res_I^G Ind_I^G σ)`.-/
lemma finrank_end_ind_eq_hom_res_ind
    {G : Type u} [Group G] [Finite G]
    (I : Subgroup G)
    (σ : FDRep k I) :
    Module.finrank k (FDRep.ind I σ ⟶ FDRep.ind I σ)
      =
    Module.finrank k
      (σ ⟶ FDRep.res (FDRep.ind I σ) I) := by
  let τ : FDRep k G := FDRep.ind I σ
  exact LinearEquiv.finrank_eq
    (FDRep.indResEquiv I σ τ)

end FDRep
