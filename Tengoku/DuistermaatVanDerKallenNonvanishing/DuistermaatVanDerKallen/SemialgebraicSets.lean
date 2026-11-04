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

theorem univ : IsSemialgebraic ι Set.univ := by
  simpa using nonneg (0 : MvPolynomial ι ℝ)

theorem zeroSet (p : MvPolynomial ι ℝ) : IsSemialgebraic ι {x | MvPolynomial.eval x p = 0} := by
  have he : {x : ι → ℝ | MvPolynomial.eval x p = 0} =
      {x | 0 ≤ MvPolynomial.eval x p} ∩ {x | 0 ≤ MvPolynomial.eval x (-p)} := by
    ext x
    simp only [Set.mem_ofPred_eq, Set.mem_inter_iff, map_neg, neg_nonneg]
    exact ⟨fun h => ⟨h ▸ le_rfl, h ▸ le_rfl⟩, fun h => le_antisymm h.2 h.1⟩
  rw [he]
  exact inter (nonneg p) (nonneg (-p))

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

theorem eq (p q : MvPolynomial ι ℝ) :
    IsSemialgebraic ι {x | MvPolynomial.eval x p = MvPolynomial.eval x q} := by
  simpa only [map_sub, sub_eq_zero] using zeroSet (p - q)

theorem le (p q : MvPolynomial ι ℝ) :
    IsSemialgebraic ι {x | MvPolynomial.eval x p ≤ MvPolynomial.eval x q} := by
  simpa only [map_sub, sub_nonneg] using nonneg (q - p)

theorem lt (p q : MvPolynomial ι ℝ) :
    IsSemialgebraic ι {x | MvPolynomial.eval x p < MvPolynomial.eval x q} := by
  simpa only [Set.compl_ofPred, not_le] using (le q p).compl

theorem forall_finite {κ : Type*} [Finite κ] (f : κ → Set (ι → ℝ))
    (hf : ∀ k, IsSemialgebraic ι (f k)) : IsSemialgebraic ι {x | ∀ k, x ∈ f k} := by
  let := Fintype.ofFinite κ
  simpa using finite_forall Finset.univ f (fun k _ => hf k)

theorem exists_finite {κ : Type*} [Finite κ] (f : κ → Set (ι → ℝ))
    (hf : ∀ k, IsSemialgebraic ι (f k)) : IsSemialgebraic ι {x | ∃ k, x ∈ f k} := by
  simpa [Set.compl_ofPred] using (forall_finite (fun k => (f k)ᶜ) (fun k => (hf k).compl)).compl

/-- Polynomial substitution preserves finite Boolean combinations of signs.
This is a preimage theorem, with no assertion about projection or images.-/
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
