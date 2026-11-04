import Tengoku.Seed.Algebra.MvPolynomial.CommRing
import Tengoku.Seed.Algebra.MvPolynomial.Eval
import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/
/-! Semialgebraic sets are finite Boolean combinations of real polynomial
inequalities. No closure under projection or geometric triviality is assumed. -/

namespace DuistermaatVanDerKallen
noncomputable section

/-- Finite Boolean combinations of real polynomial weak inequalities.-/
inductive IsSemialgebraic (ι : Type*) : Set (ι → ℝ) → Prop
  | nonneg (p : MvPolynomial ι ℝ) : IsSemialgebraic ι {x | 0 ≤ MvPolynomial.eval x p}
  | inter {s t : Set (ι → ℝ)} : IsSemialgebraic ι s → IsSemialgebraic ι t →
      IsSemialgebraic ι (s ∩ t)
  | union {s t : Set (ι → ℝ)} : IsSemialgebraic ι s → IsSemialgebraic ι t →
      IsSemialgebraic ι (s ∪ t)
  | compl {s : Set (ι → ℝ)} : IsSemialgebraic ι s → IsSemialgebraic ι sᶜ

namespace IsSemialgebraic
variable {ι : Type*}

/--
@isnad1 id=issemial.0h1v.s3.54c034c20497 from=translated src=- shape=498ece3d vocab=45976ff2
-/
theorem univ : IsSemialgebraic ι Set.univ := by
  simpa using nonneg (0 : MvPolynomial ι ℝ)

/--
@isnad1 id=issemial.0h2v.s6.4c604d0a759a from=translated src=- shape=769316ef vocab=1f4aea5f
-/
theorem zeroSet (p : MvPolynomial ι ℝ) : IsSemialgebraic ι {x | MvPolynomial.eval x p = 0} := by
  have he : {x : ι → ℝ | MvPolynomial.eval x p = 0} =
      {x | 0 ≤ MvPolynomial.eval x p} ∩ {x | 0 ≤ MvPolynomial.eval x (-p)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, map_neg, neg_nonneg]
    exact ⟨fun h => ⟨h ▸ le_rfl, h ▸ le_rfl⟩, fun h => le_antisymm h.2 h.1⟩
  rw [he]
  exact inter (nonneg p) (nonneg (-p))

/--
@isnad1 id=issemial.1h4v.s6.f7d2efe24a37 from=translated src=- shape=a6a4f9f8 vocab=2b332030
-/
theorem finite_forall {κ : Type*} (S : Finset κ) (f : κ → Set (ι → ℝ))
    (hf : ∀ k ∈ S, IsSemialgebraic ι (f k)) :
    IsSemialgebraic ι {x | ∀ k ∈ S, x ∈ f k} := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (univ (ι := ι))
  | @insert k S hk ih =>
    have he : {x | ∀ j ∈ insert k S, x ∈ f j} = f k ∩ {x | ∀ j ∈ S, x ∈ f j} := by
      ext x
      simp
    rw [he]
    exact inter (hf k (by simp)) (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/--
@isnad1 id=issemial.0h3v.s7.7e7941df34ab from=translated src=- shape=581a9574 vocab=1f4aea5f
-/
theorem eq (p q : MvPolynomial ι ℝ) :
    IsSemialgebraic ι {x | MvPolynomial.eval x p = MvPolynomial.eval x q} := by
  simpa only [map_sub, sub_eq_zero] using zeroSet (p - q)

/--
@isnad1 id=issemial.0h3v.s7.b102772d5c64 from=translated src=- shape=581a9574 vocab=8b9898d3
-/
theorem le (p q : MvPolynomial ι ℝ) :
    IsSemialgebraic ι {x | MvPolynomial.eval x p ≤ MvPolynomial.eval x q} := by
  simpa only [map_sub, sub_nonneg] using nonneg (q - p)

/--
@isnad1 id=issemial.0h3v.s7.9c0d68c7709b from=translated src=- shape=581a9574 vocab=88610420
-/
theorem lt (p q : MvPolynomial ι ℝ) :
    IsSemialgebraic ι {x | MvPolynomial.eval x p < MvPolynomial.eval x q} := by
  simpa only [Set.compl_ofPred, not_le] using (le q p).compl

/--
@isnad1 id=issemial.1h3v.s5.c537543981bd from=translated src=- shape=a8022d8e vocab=c03caa43
-/
theorem forall_finite {κ : Type*} [Finite κ] (f : κ → Set (ι → ℝ))
    (hf : ∀ k, IsSemialgebraic ι (f k)) : IsSemialgebraic ι {x | ∀ k, x ∈ f k} := by
  let := Fintype.ofFinite κ
  simpa using finite_forall Finset.univ f (fun k _ => hf k)

/--
@isnad1 id=issemial.1h3v.s5.9c92735a9862 from=translated src=- shape=b00c9ec4 vocab=c03caa43
-/
theorem exists_finite {κ : Type*} [Finite κ] (f : κ → Set (ι → ℝ))
    (hf : ∀ k, IsSemialgebraic ι (f k)) : IsSemialgebraic ι {x | ∃ k, x ∈ f k} := by
  simpa [Set.compl_ofPred] using (forall_finite (fun k => (f k)ᶜ) (fun k => (hf k).compl)).compl

/-- Polynomial substitution preserves finite Boolean combinations of signs.
This is a preimage theorem, with no assertion about projection or images.
@isnad1 id=issemial.1h4v.s6.e0911cbca1f4 from=translated src=- shape=f0cb1b31 vocab=7cb5cad6
-/
theorem polynomial_preimage {κ : Type*} {s : Set (ι → ℝ)} (hs : IsSemialgebraic ι s)
    (g : ι → MvPolynomial κ ℝ) :
    IsSemialgebraic κ ((fun x i => MvPolynomial.eval x (g i)) ⁻¹' s) := by
  induction hs with
  | nonneg p =>
    convert nonneg (MvPolynomial.eval₂ MvPolynomial.C g p) using 1
    ext x
    have hc : (MvPolynomial.eval x).comp (MvPolynomial.C : ℝ →+* MvPolynomial κ ℝ) = RingHom.id ℝ := by
      ext a
      simp
    simp [MvPolynomial.eval_eval₂, hc]
  | inter _ _ ih₁ ih₂ => exact inter ih₁ ih₂
  | union _ _ ih₁ ih₂ => exact union ih₁ ih₂
  | compl _ ih => exact compl ih

end IsSemialgebraic
end
end DuistermaatVanDerKallen
