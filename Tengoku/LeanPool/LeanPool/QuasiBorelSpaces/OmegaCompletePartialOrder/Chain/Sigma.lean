/-
Copyright (c) 2026 Anthony Vandikas, Kiarash Sotoudeh. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthony Vandikas, Kiarash Sotoudeh
-/
module

public import Tengoku

/-!
# LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Sigma

Imported Lean Pool material for `LeanPool.QuasiBorelSpaces.OmegaCompletePartialOrder.Chain.Sigma`.
-/

@[expose] public section

namespace OmegaCompletePartialOrder.Chain.Sigma

variable {I : Type*} {P : I → Type*} [∀ i, Preorder (P i)]

/-- Injects a chain into a chain of coproducts. -/
def inj {i} (c : Chain (P i)) : Chain ((i : I) × P i) where
  toFun n := ⟨i, c n⟩
  monotone' n₁ n₂ hn := by
    simp only [Sigma.mk_le_mk_iff]
    apply c.monotone' hn

/--
@isnad1 id=eq.0h5v.s6.419471015db7 from=translated src=- shape=5673b307 vocab=706e6b7f
-/
@[simp]
lemma inj_coe {i} (c : Chain (P i)) (n : ℕ) : inj c n = ⟨i, c n⟩ := rfl

/-- Converts a chain of coproducts into a coproduct of chains. -/
def distrib (c : Chain ((i : I) × P i)) : (i : I) × Chain (P i) where
  fst := (c 0).fst
  snd.toFun n :=
    have : (c 0).fst = (c n).fst := by
      have := c.monotone (Nat.zero_le n)
      rw [Sigma.le_def] at this
      exact this.choose
    this ▸ (c n).snd
  snd.monotone' i₁ i₂ hi := by
    have h₁ := c.monotone hi
    dsimp only [Lean.Elab.WF.paramLet]
    generalize_proofs h₂
    generalize c i₁ = ci₁, c i₂ = ci₂ at *
    rcases h₁ with ⟨i, _, _, h₁⟩
    dsimp at h₂
    subst h₂
    exact h₁

/--
@isnad1 id=eq.0h4v.s5.07ca2fb5dbae from=translated src=- shape=62a1e449 vocab=a4ae287d
-/
@[simp]
lemma distrib_inj {i} (c : Chain (P i)) : distrib (inj c) = ⟨i, c⟩ := rfl

/--
@isnad1 id=eq.0h3v.s6.5ecca3a21c2e from=translated src=- shape=7b0c9837 vocab=a55582f2
-/
@[simp]
lemma inj_distrib (c : Chain (Sigma P)) : inj (distrib c).snd = c := by
  apply Chain.ext
  funext n
  change (⟨(c 0).fst, _⟩ : Sigma P) = c n
  have hfst : (c 0).fst = (c n).fst := by
    have := (OrderHomClass.mono c) (Nat.zero_le n)
    rw [Sigma.le_def] at this
    exact this.choose
  refine Sigma.ext hfst ?_
  exact eqRec_heq _ _

/--
@isnad1 id=var.0h5v.s5.0c336891fc52 from=translated src=- shape=eaae9d8e vocab=d4b2b9e8
-/
@[elab_as_elim]
lemma distrib_cases
    {p : Chain ((i : I) × P i) → Prop}
    (mk : ∀ {i} (c : Chain (P i)), p (inj c))
    (c : Chain ((i : I) × P i)) : p c := by
  rw [← inj_distrib c]
  apply mk

end OmegaCompletePartialOrder.Chain.Sigma
