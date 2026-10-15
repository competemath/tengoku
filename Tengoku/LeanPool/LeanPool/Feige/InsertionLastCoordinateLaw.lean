/-
Copyright (c) 2026 Zhengqing Zhou and contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Zhengqing Zhou, GPT-5.6 Pro
-/
module

public import Tengoku.LeanPool.LeanPool.Feige.InsertionCommonLaw
public import Tengoku.LeanPool.LeanPool.Feige.ChainInsertion

/-!
# Splitting off the newly inserted coordinate

The old signed-exponential state law is exactly the common law obtained in
the enlarged system after deleting its last coordinate.  Consequently, the
lower and upper enlarged states are respectively the positive and negative
exponential shifts of the old law.  These are the dimension-change
identifications used at every chain-insertion edge.
-/

@[expose] public section

open MeasureTheory

namespace Feige

noncomputable section

/-- The complete list of signed factors on `Fin n`, embedded by
`Fin.castSucc`, is a permutation of the enlarged factor list with the last
coordinate erased.
@isnad1 id=perm.2h4v.s8.93c0abce6667 from=translated src=- shape=5232dba9 vocab=5754167b
-/
theorem stateFactorList_castSucc_perm {n : ℕ}
    (γ β : Fin (n + 1) → ℝ)
    (hγ : ∀ i, 0 < γ i) (hβ : ∀ i, 0 < β i)
    (S : Finset (Fin n)) :
    (Finset.univ.toList.map
        (LikelihoodRatio.stateFactor
          (fun i : Fin n ↦ γ i.castSucc)
          (fun i : Fin n ↦ β i.castSucc)
          (fun i ↦ hγ i.castSucc) (fun i ↦ hβ i.castSucc) S)).Perm
      ((Finset.univ.erase (Fin.last n)).toList.map
        (LikelihoodRatio.stateFactor γ β hγ hβ
          (liftChainState S))) := by
  have hpIndex :
      ((Finset.univ : Finset (Fin n)).toList.map Fin.castSucc).Perm
        ((Finset.univ.erase (Fin.last n) :
          Finset (Fin (n + 1))).toList) := by
    apply (List.perm_ext_iff_of_nodup
      ((Finset.nodup_toList _).map (Fin.castSucc_injective n))
      (Finset.nodup_toList _)).2
    intro x
    constructor
    · intro hx
      obtain ⟨i, _hi, rfl⟩ := List.mem_map.mp hx
      simp
    · intro hx
      have hxErase :
          x ∈ (Finset.univ.erase (Fin.last n) :
            Finset (Fin (n + 1))) := by
        simpa only [Finset.mem_toList] using hx
      have hne : x ≠ Fin.last n := (Finset.mem_erase.mp hxErase).1
      obtain ⟨i, rfl⟩ := Fin.exists_castSucc_eq.mpr hne
      simp
  have hp := hpIndex.map
    (LikelihoodRatio.stateFactor γ β hγ hβ (liftChainState S))
  have hfactor : ∀ i : Fin n,
      LikelihoodRatio.stateFactor γ β hγ hβ
          (liftChainState S) i.castSucc =
        LikelihoodRatio.stateFactor
          (fun k : Fin n ↦ γ k.castSucc)
          (fun k : Fin n ↦ β k.castSucc)
          (fun k ↦ hγ k.castSucc) (fun k ↦ hβ k.castSucc) S i := by
    intro i
    unfold LikelihoodRatio.stateFactor
    simp
  have hleft :
      (((Finset.univ : Finset (Fin n)).toList.map Fin.castSucc).map
        (LikelihoodRatio.stateFactor γ β hγ hβ
          (liftChainState S))) =
        (Finset.univ.toList.map
          (LikelihoodRatio.stateFactor
            (fun k : Fin n ↦ γ k.castSucc)
            (fun k : Fin n ↦ β k.castSucc)
            (fun k ↦ hγ k.castSucc) (fun k ↦ hβ k.castSucc) S)) := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i hi
    exact hfactor i
  rw [hleft] at hp
  exact hp

end

end Feige
