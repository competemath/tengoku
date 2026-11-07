/-
Copyright (c) 2026 TNLean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: TNLean contributors
-/
import Tengoku.Tnlean.TNLean.MPS.ParentHamiltonian.Decorrelation
import Tengoku.Seed.Tactic.Abel

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# RFP decorrelation theory — commuting idempotent algebra

This file develops the algebraic theory of commuting idempotent endomorphisms
needed for the decorrelation ↔ commuting parent Hamiltonian equivalence
(Proposition D.3, arXiv:1606.00608 Appendix D).

Building on the backward direction proved in
`TNLean.MPS.ParentHamiltonian.Decorrelation`, this file:
1. Uses the product algebra of commuting idempotents directly in the
   commuting-parent-Hamiltonian consequences below.
2. Extends the `HasCommutingParentHam` properties with absorption, reverse-product,
   complement commutativity, and a ground-space membership characterisation.

All results are fully proved (no `sorry`).

## Main results

### Frustration-free algebra

* `LinearMap.frustration_free_ham_eq` — `(1−P) + (1−Q) − (1−P)∘(1−Q) =
  1 − P∘Q`

### `Decorrelation.HasCommutingParentHam` properties

* `pK_idem` — `P_K ∘ P_K = P_K`
* `pAX_comp_pK` — `P_AX ∘ P_K = P_K`
* `pK_comp_pXB` — `P_K ∘ P_XB = P_K`
* `pXB_comp_pK` — `P_XB ∘ P_K = P_K`
* `pK_comp_pAX` — `P_K ∘ P_AX = P_K`
* `reverse_product` — `P_XB ∘ P_AX = P_K`
* `complement_comm` — `(id − P_AX) ∘ (id − P_XB) = (id − P_XB) ∘ (id − P_AX)`
* `mem_ground_iff` — `P_K v = v ↔ P_AX v = v ∧ P_XB v = v`

## References

* arXiv:1606.00608, Appendix D, Section D.2 (Definitions D.1–D.2, Proposition D.3)
-/

section FrustrationFreeIdentity

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

namespace LinearMap

/-- The frustration-free Hamiltonian identity:
`(1 − P) + (1 − Q) − (1 − P) ∘ (1 − Q) = 1 − P ∘ Q`.

For commuting parent Hamiltonians, this shows that the "Hamiltonian"
`Q_AX + Q_XB − Q_AX ∘ Q_XB` (with `Q = 1 − P`) equals `1 − P_K`.
See arXiv:1606.00608, Appendix D, Section D.2.
@isnad1 id=eq.0h3v.s9.ff3d5a18c9c4 from=translated src=- shape=e8b13040 vocab=8c75df68
-/
theorem frustration_free_ham_eq {P Q : E →ₗ[ℂ] E} :
    (id - P) + (id - Q) - (id - P) ∘ₗ (id - Q) = id - P ∘ₗ Q := by
  simp only [comp_sub, sub_comp, comp_id, id_comp]
  abel

end LinearMap

end FrustrationFreeIdentity

/-!
### Extended `HasCommutingParentHam` properties

Absorption, reverse-product, and ground-space characterisation lemmas
for the commuting parent Hamiltonian structure.
-/

section HasCommutingParentHamProperties

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

namespace Decorrelation

/-- `P_K` is idempotent.
@isnad1 id=eq.0h3v.s6.385499507978 from=translated src=- shape=809d6dd2 vocab=a499c6a5
-/
theorem HasCommutingParentHam.pK_idem {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    P_K ∘ₗ P_K = P_K := by
  change IsIdempotentElem P_K
  simpa [h.hK, Module.End.mul_eq_comp] using
    (IsIdempotentElem.mul_of_commute h.hcomm h.hAX_idem h.hXB_idem)

/-- `P_AX ∘ P_K = P_K`: the AX-projector absorbs `P_K` from the left.
@isnad1 id=eq.0h3v.s6.c1e566dea5de from=translated src=- shape=213e0f84 vocab=ac1690c6
-/
theorem HasCommutingParentHam.pAX_comp_pK {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    h.P_AX ∘ₗ P_K = P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  have hAX : P_AX ∘ₗ P_AX = P_AX := h.hAX_idem
  change P_AX ∘ₗ P_K = P_K
  rw [← hK, ← LinearMap.comp_assoc, hAX, hK]

/-- `P_K ∘ P_XB = P_K`: `P_K` absorbs the XB-projector on the right.
@isnad1 id=eq.0h3v.s6.50170dc88f48 from=translated src=- shape=9539b580 vocab=e65558df
-/
theorem HasCommutingParentHam.pK_comp_pXB {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    P_K ∘ₗ h.P_XB = P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  have hXB : P_XB ∘ₗ P_XB = P_XB := h.hXB_idem
  change P_K ∘ₗ P_XB = P_K
  rw [← hK, LinearMap.comp_assoc, hXB, hK]

/-- `P_XB ∘ P_K = P_K`: the XB-projector absorbs `P_K` from the left.
@isnad1 id=eq.0h3v.s6.46dc37180028 from=translated src=- shape=213e0f84 vocab=e65558df
-/
theorem HasCommutingParentHam.pXB_comp_pK {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    h.P_XB ∘ₗ P_K = P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  have hXB : P_XB ∘ₗ P_XB = P_XB := h.hXB_idem
  have hcomm : P_AX ∘ₗ P_XB = P_XB ∘ₗ P_AX := h.hcomm
  change P_XB ∘ₗ P_K = P_K
  rw [← hK, ← LinearMap.comp_assoc, ← hcomm, LinearMap.comp_assoc, hXB, hK]

/-- `P_K ∘ P_AX = P_K`: `P_K` absorbs the AX-projector on the right.
@isnad1 id=eq.0h3v.s6.a6a10fb5d3c5 from=translated src=- shape=9539b580 vocab=ac1690c6
-/
theorem HasCommutingParentHam.pK_comp_pAX {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    P_K ∘ₗ h.P_AX = P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  have hAX : P_AX ∘ₗ P_AX = P_AX := h.hAX_idem
  have hcomm : P_AX ∘ₗ P_XB = P_XB ∘ₗ P_AX := h.hcomm
  change P_K ∘ₗ P_AX = P_K
  rw [← hK, LinearMap.comp_assoc, ← hcomm, ← LinearMap.comp_assoc, hAX, hK]

/-- The reverse product equals `P_K`: `P_XB ∘ P_AX = P_K`.
Follows from `hK : P_AX ∘ P_XB = P_K` and commutativity.
@isnad1 id=eq.0h3v.s6.3dbabe92e40a from=translated src=- shape=dcdfc140 vocab=00130cd4
-/
theorem HasCommutingParentHam.reverse_product {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    h.P_XB ∘ₗ h.P_AX = P_K := by
  simpa [h.hK] using h.hcomm.symm

/-- The complements `Q_AX = id − P_AX` and `Q_XB = id − P_XB` commute.
@isnad1 id=eq.0h3v.s9.604e40c11c7b from=translated src=- shape=fdbfc77a vocab=be50203d
-/
theorem HasCommutingParentHam.complement_comm {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    (LinearMap.id - h.P_AX) ∘ₗ (LinearMap.id - h.P_XB) =
      (LinearMap.id - h.P_XB) ∘ₗ (LinearMap.id - h.P_AX) :=
  by
    have hcomm : Commute h.P_AX h.P_XB := by
      change h.P_AX * h.P_XB = h.P_XB * h.P_AX
      simpa [Module.End.mul_eq_comp] using h.hcomm
    have hP_comp : Commute h.P_AX (LinearMap.id - h.P_XB) :=
      (Commute.one_right h.P_AX).sub_right hcomm
    have hcomp : Commute (LinearMap.id - h.P_AX) (LinearMap.id - h.P_XB) :=
      (Commute.one_left (LinearMap.id - h.P_XB)).sub_left hP_comp
    simpa [Module.End.mul_eq_comp] using hcomp.eq

/-- The frustration-free Hamiltonian identity for a commuting parent
Hamiltonian: `Q_AX + Q_XB − Q_AX ∘ Q_XB = id − P_K`.
@isnad1 id=eq.0h3v.s9.2faff55804b5 from=translated src=- shape=1f9958d9 vocab=1f3b98a6
-/
theorem HasCommutingParentHam.hamiltonian_eq {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) :
    (LinearMap.id - h.P_AX) + (LinearMap.id - h.P_XB) -
      (LinearMap.id - h.P_AX) ∘ₗ (LinearMap.id - h.P_XB) =
      LinearMap.id - P_K := by
  let P_AX := h.P_AX
  let P_XB := h.P_XB
  have hK : P_AX ∘ₗ P_XB = P_K := h.hK
  change (LinearMap.id - P_AX) + (LinearMap.id - P_XB) -
      (LinearMap.id - P_AX) ∘ₗ (LinearMap.id - P_XB) =
    LinearMap.id - P_K
  simpa [hK] using (LinearMap.frustration_free_ham_eq (P := P_AX) (Q := P_XB))

/-- Ground-space membership: `P_K v = v` iff both `P_AX v = v` and
`P_XB v = v`. This is the algebraic form of
`K_{AXB} = (K_{AX} ⊗ H_B) ∩ (H_A ⊗ K_{XB})`
from arXiv:1606.00608, equation (D.2).
@isnad1 id=iff.0h4v.s7.bde5d6e34081 from=translated src=- shape=47475738 vocab=0fcbc9ba
-/
theorem HasCommutingParentHam.mem_ground_iff {P_K : E →ₗ[ℂ] E}
    (h : HasCommutingParentHam P_K) (v : E) :
    P_K v = v ↔ h.P_AX v = v ∧ h.P_XB v = v := by
  constructor
  · intro hv
    constructor
    · have : h.P_AX (P_K v) = P_K v := by
        rw [← LinearMap.comp_apply, h.pAX_comp_pK]
      rwa [hv] at this
    · have : h.P_XB (P_K v) = P_K v := by
        rw [← LinearMap.comp_apply, h.pXB_comp_pK]
      rwa [hv] at this
  · rintro ⟨hAX, hXB⟩
    have : (h.P_AX ∘ₗ h.P_XB) v = v := by
      simp only [LinearMap.comp_apply]; rw [hXB, hAX]
    rwa [h.hK] at this

end Decorrelation

end HasCommutingParentHamProperties
