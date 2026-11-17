import Tengoku
import Tengoku.LeanEvalPlatonicClassification.Submission.FlagAdiacente

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open Set

noncomputable section

namespace LeanEval.Geometry.PlatonicClassification

open ConvexPolytope

variable {n : ℕ}

/-- Rimonta simultaneamente due ranghi consecutivi di una bandiera.  Il
rimontaggio simultaneo e necessario: nessuna delle due sostituzioni singole
deve, in generale, essere gia una bandiera.-/
noncomputable def sostituisci_due (P : ConvexPolytope n) (F : P.Flag)
    (i ip : Fin n) (hip : (i : ℕ) + 1 = (ip : ℕ))
    (C D : Set (E n)) (hC : P.IsFace C) (hD : P.IsFace D)
    (hdC : faceDim C = (i : ℕ)) (hdD : faceDim D = (ip : ℕ))
    (hsotto : ∀ j : Fin n, j < i → F.face j ⊂ C)
    (hCD : C ⊂ D)
    (hsopra : ∀ j : Fin n, ip < j → D ⊂ F.face j) : P.Flag where
  face := Function.update (Function.update F.face i C) ip D
  isFace := by
    intro k
    have hi_ne_ip : i ≠ ip := by
      intro h
      have := congrArg Fin.val h
      omega
    by_cases hk_ip : k = ip
    · subst k
      rw [Function.update_self]
      exact hD
    · by_cases hk_i : k = i
      · subst k
        rw [Function.update_of_ne hi_ne_ip, Function.update_self]
        exact hC
      · rw [Function.update_of_ne hk_ip, Function.update_of_ne hk_i]
        exact F.isFace k
  dim_eq := by
    intro k
    have hi_ne_ip : i ≠ ip := by
      intro h
      have := congrArg Fin.val h
      omega
    by_cases hk_ip : k = ip
    · subst k
      rw [Function.update_self]
      exact hdD
    · by_cases hk_i : k = i
      · subst k
        rw [Function.update_of_ne hi_ne_ip, Function.update_self]
        exact hdC
      · rw [Function.update_of_ne hk_ip, Function.update_of_ne hk_i]
        exact F.dim_eq k
  strict_mono := by
    intro j k hjk
    have hi_ne_ip : i ≠ ip := by
      intro h
      have := congrArg Fin.val h
      omega
    by_cases hj_ip : j = ip
    · subst j
      have hk_ip : k ≠ ip := ne_of_gt hjk
      have hk_i : k ≠ i := by
        intro h
        subst k
        rw [Fin.lt_def] at hjk
        omega
      rw [Function.update_self, Function.update_of_ne hk_ip,
        Function.update_of_ne hk_i]
      exact hsopra k hjk
    · by_cases hj_i : j = i
      · subst j
        by_cases hk_ip : k = ip
        · subst k
          rw [Function.update_of_ne hi_ne_ip, Function.update_self,
            Function.update_self]
          exact hCD
        · have hk_i : k ≠ i := ne_of_gt hjk
          have hipk : ip < k := by
            rw [Fin.lt_def] at hjk ⊢
            omega
          rw [Function.update_of_ne hi_ne_ip, Function.update_self,
            Function.update_of_ne hk_ip, Function.update_of_ne hk_i]
          exact hCD.trans (hsopra k hipk)
      · by_cases hk_i : k = i
        · subst k
          rw [Function.update_of_ne hj_ip, Function.update_of_ne hj_i,
            Function.update_of_ne hi_ne_ip, Function.update_self]
          exact hsotto j hjk
        · by_cases hk_ip : k = ip
          · subst k
            have hji : j < i := by
              rw [Fin.lt_def] at hjk ⊢
              have hj_ne_i : (j : ℕ) ≠ (i : ℕ) := by
                intro h
                exact hj_i (Fin.ext h)
              omega
            rw [Function.update_of_ne hj_ip, Function.update_of_ne hj_i,
              Function.update_self]
            exact (hsotto j hji).trans hCD
          · rw [Function.update_of_ne hj_ip, Function.update_of_ne hj_i,
              Function.update_of_ne hk_ip, Function.update_of_ne hk_i]
            exact F.strict_mono j k hjk

end LeanEval.Geometry.PlatonicClassification
