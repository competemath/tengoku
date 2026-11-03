import Tengoku.MagnitudeConjecture.MagnitudeConjecture.Combinatorics.PosetSpaceRealization

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Support chains for selectable reverse enumerations

This file transports the support-prefix chain and Schur-detour arithmetic from
the package's canonical reverse extension to an arbitrary selectable reverse
enumeration.
-/

set_option autoImplicit false

noncomputable section

namespace MagnitudeConjecture.PosetSpace

universe u

open CategoryTheory
open CategoryTheory.Limits

variable (k T : Type u) [Field k] [PartialOrder T] [Fintype T]

/-- The upper support consisting of the first `j` elements of the selected
reverse enumeration.-/
def supportAtFor (R : ReverseEnumeration T)
    (j : Fin (Fintype.card T + 1)) : Set T :=
  {t | (ReverseEnumeration.index T R t).val < j.val}

/-- Every selected support prefix is an upper set in the original poset.
@isnad1 id=isuppers.0h3v.s5.7ef73b8c4ad4 from=translated src=- shape=63c5e0f2 vocab=68320b5b
-/
theorem supportAtFor_isUpperSet (R : ReverseEnumeration T)
    (j : Fin (Fintype.card T + 1)) :
    IsUpperSet (supportAtFor T R j) := by
  intro s t hst hs
  have hindex : ReverseEnumeration.index T R t ≤
      ReverseEnumeration.index T R s :=
    R.index_anti hst
  change (ReverseEnumeration.index T R s).val < j.val at hs
  have hindex_val : (ReverseEnumeration.index T R t).val ≤
      (ReverseEnumeration.index T R s).val := hindex
  exact lt_of_le_of_lt hindex_val hs

/-- Selected support prefixes are monotone in their length.
@isnad1 id=le.1h4v.s6.bd33c8f2a41a from=translated src=- shape=a46db81f vocab=45c7a014
-/
theorem supportAtFor_mono (R : ReverseEnumeration T)
    {i j : Fin (Fintype.card T + 1)} (hij : i ≤ j) :
    supportAtFor T R i ⊆ supportAtFor T R j := by
  intro t ht
  change (ReverseEnumeration.index T R t).val < i.val at ht
  exact lt_of_lt_of_le ht hij

/-- Consecutive selected support prefixes are strictly increasing.
@isnad1 id=lt.0h3v.s5.b2ad26402d15 from=translated src=- shape=a38eb48a vocab=77988c47
-/
theorem supportAtFor_strictMono (R : ReverseEnumeration T)
    (j : Fin (Fintype.card T)) :
    supportAtFor T R j.castSucc ⊂ supportAtFor T R j.succ := by
  constructor
  · intro t ht
    exact Nat.lt_trans ht (Nat.lt_succ_self j.val)
  · intro hEq
    have hmem : R.equiv j ∈ supportAtFor T R j.succ := by
      simp [supportAtFor, ReverseEnumeration.index_equiv]
    have hnot : R.equiv j ∉ supportAtFor T R j.castSucc := by
      simp [supportAtFor, ReverseEnumeration.index_equiv]
    exact hnot (hEq hmem)

/-- The one-dimensional poset space at a selected support prefix.-/
abbrev supportLineFor (R : ReverseEnumeration T)
    (j : Fin (Fintype.card T + 1)) : Obj k T :=
  line k T (supportAtFor T R j) (supportAtFor_isUpperSet T R j)

/-- A consecutive map in the selected support chain.-/
abbrev supportLineStepFor (R : ReverseEnumeration T)
    (j : Fin (Fintype.card T)) :
    supportLineFor k T R j.castSucc ⟶ supportLineFor k T R j.succ :=
  lineHom k T
    (hU := supportAtFor_isUpperSet T R j.castSucc)
    (hV := supportAtFor_isUpperSet T R j.succ)
    (supportAtFor_strictMono T R j).1

/--
@isnad1 id=ne.0h4v.s7.53a199580ac3 from=translated src=- shape=5ba4c447 vocab=189b6c8f
-/
theorem supportLineStepFor_ne_zero (R : ReverseEnumeration T)
    (j : Fin (Fintype.card T)) :
    supportLineStepFor k T R j ≠ 0 :=
  lineHom_ne_zero k T (supportAtFor_strictMono T R j).1

/--
@isnad1 id=not.0h4v.s6.7946edf67f49 from=translated src=- shape=2801c5b3 vocab=c41ad1a5
-/
theorem supportLineStepFor_not_isIso (R : ReverseEnumeration T)
    (j : Fin (Fintype.card T)) :
    ¬IsIso (supportLineStepFor k T R j) :=
  lineHom_not_isIso k T (supportAtFor_strictMono T R j)

/-- Along any selected support chain, a Schur-positive grading grows by at
least the difference of support indices.
@isnad1 id=le.1h7v.s7.b5499398ffef from=translated src=- shape=a9782d27 vocab=0fa470d1
-/
theorem supportLineFor_level_add_index_le
    (R : ReverseEnumeration T) {L : ℕ}
    (G : PositiveGrading (Obj k T) (IsSchur k T) L)
    {i j : Fin (Fintype.card T + 1)} (hij : i ≤ j) :
    G.level (supportLineFor k T R i) + j.val ≤
      G.level (supportLineFor k T R j) + i.val := by
  rcases i with ⟨i, hi⟩
  rcases j with ⟨j, hj⟩
  change i ≤ j at hij
  simp only
  induction j, hij using Nat.le_induction with
  | base => simp
  | succ j _ ih =>
      specialize ih (Nat.lt_of_succ_lt hj)
      let r : Fin (Fintype.card T) := ⟨j, by omega⟩
      have hstep :
          G.level (supportLineFor k T R r.castSucc) <
            G.level (supportLineFor k T R r.succ) :=
        G.lt_of_nonzero_not_isIso (supportLineStepFor k T R r)
          (line_isSchur k T (supportAtFor T R r.castSucc)
            (supportAtFor_isUpperSet T R r.castSucc))
          (line_isSchur k T (supportAtFor T R r.succ)
            (supportAtFor_isUpperSet T R r.succ))
          (supportLineStepFor_ne_zero k T R r)
          (supportLineStepFor_not_isIso k T R r)
      change G.level (supportLineFor k T R ⟨j, by omega⟩) <
        G.level (supportLineFor k T R ⟨j + 1, hj⟩) at hstep
      omega

/-- A two-step Schur detour replacing one inclusion in a selected support
chain.-/
structure SelectableSchurDetour (R : ReverseEnumeration T)
    (q : ℕ) (hq : q + 2 < Fintype.card T) where
  middle : Obj k T
  middle_schur : IsSchur k T middle
  inMap :
    supportLineFor k T R
      ⟨q + 1, Nat.lt_succ_iff.mpr (Nat.le_of_lt (lt_trans (by omega) hq))⟩ ⟶
      middle
  outMap : middle ⟶
    supportLineFor k T R
      ⟨q + 2, Nat.lt_succ_iff.mpr (Nat.le_of_lt hq)⟩
  inMap_ne_zero : inMap ≠ 0
  outMap_ne_zero : outMap ≠ 0
  inMap_not_isIso : ¬IsIso inMap
  outMap_not_isIso : ¬IsIso outMap

/-- Splicing a two-step Schur detour into any selected support chain forces
the strict realization bound `|T|+1 ≤ L`.
@isnad1 id=le.1h7v.s6.d61accd8a1fa from=translated src=- shape=5df00773 vocab=62700dd4
-/
theorem card_add_one_le_of_selectableSchurDetour
    (R : ReverseEnumeration T) {L q : ℕ}
    (G : PositiveGrading (Obj k T) (IsSchur k T) L)
    {hq : q + 2 < Fintype.card T}
    (D : SelectableSchurDetour k T R q hq) :
    Fintype.card T + 1 ≤ L := by
  let iq1 : Fin (Fintype.card T + 1) :=
    ⟨q + 1, Nat.lt_succ_iff.mpr (by omega)⟩
  let iq2 : Fin (Fintype.card T + 1) :=
    ⟨q + 2, Nat.lt_succ_iff.mpr (by omega)⟩
  let ilast : Fin (Fintype.card T + 1) := Fin.last (Fintype.card T)
  have hprefix := supportLineFor_level_add_index_le k T R G
    (i := (0 : Fin (Fintype.card T + 1))) (j := iq1) (Fin.zero_le _)
  have hin : G.level (supportLineFor k T R iq1) < G.level D.middle :=
    G.lt_of_nonzero_not_isIso D.inMap
      (line_isSchur k T (supportAtFor T R iq1)
        (supportAtFor_isUpperSet T R iq1))
      D.middle_schur D.inMap_ne_zero D.inMap_not_isIso
  have hout : G.level D.middle < G.level (supportLineFor k T R iq2) :=
    G.lt_of_nonzero_not_isIso D.outMap D.middle_schur
      (line_isSchur k T (supportAtFor T R iq2)
        (supportAtFor_isUpperSet T R iq2))
      D.outMap_ne_zero D.outMap_not_isIso
  change G.level (supportLineFor k T R iq1) < G.level D.middle at hin
  change G.level D.middle < G.level (supportLineFor k T R iq2) at hout
  have hsuffix := supportLineFor_level_add_index_le k T R G
    (i := iq2) (j := ilast) (by
      change q + 2 ≤ Fintype.card T
      exact Nat.le_of_lt hq)
  have htop := G.level_le (supportLineFor k T R ilast)
    (line_isSchur k T (supportAtFor T R ilast)
      (supportAtFor_isUpperSet T R ilast))
  have hprefix' : q + 1 ≤ G.level (supportLineFor k T R iq1) := by
    dsimp [iq1] at hprefix ⊢
    omega
  have hdetour : G.level (supportLineFor k T R iq1) + 2 ≤
      G.level (supportLineFor k T R iq2) := by
    omega
  have hsuffix' : G.level (supportLineFor k T R iq2) + Fintype.card T ≤
      G.level (supportLineFor k T R ilast) + (q + 2) := by
    change G.level (supportLineFor k T R iq2) + Fintype.card T ≤
      G.level (supportLineFor k T R ilast) + (q + 2) at hsuffix
    exact hsuffix
  change G.level (supportLineFor k T R ilast) ≤ L at htop
  dsimp [iq1, iq2, ilast] at hprefix' hdetour hsuffix' htop
  omega

end MagnitudeConjecture.PosetSpace
