import Tengoku.OpenaiMath.OAI.AlgebraicGeometry.CommutingDerivations.DerivationOperations
import Tengoku

namespace OAI

/-! The actual polynomial coordinate partials: commuting, locally nilpotent,
linearly independent over the polynomial ring, and with exact constant common
kernel in characteristic zero. No localization equivalence is assumed here. -/
noncomputable section
namespace AbhyankarSathaye.CommutingDerivations
open MvPolynomial

variable {B σ : Type*} [CommRing B]

/-- Vanishing of all coefficients at exponent at least n implies annihilation
by the nth partial iterate. This works over every commutative ring.
@isnad1 id=eq.1h5v.s8.7095aa327b65 from=translated src=- shape=6cfe1994 vocab=4c473b69
-/
theorem coordinate_partial_iterate_eq_zero (i : σ) (n : ℕ) (p : MvPolynomial σ B)
    (hp : ∀ m : σ →₀ ℕ, n ≤ m i → p.coeff m = 0) :
    (pderiv i : MvPolynomial σ B → MvPolynomial σ B)^[n] p = 0 := by
  classical
  induction n generalizing p with
  | zero =>
      apply MvPolynomial.ext
      intro m
      simpa using hp m (Nat.zero_le _)
  | succ n ih =>
      rw [Function.iterate_succ_apply]
      apply ih
      intro m hm
      rw [coeff_pderiv]
      have hz : p.coeff (m + Finsupp.single i 1) = 0 := by
        apply hp
        simpa using Nat.succ_le_succ hm
      rw [hz, zero_mul]

/-- An explicit pointwise bound: one more than the largest exponent of i
among the finitely many supported monomials.
@isnad1 id=eq.0h4v.s8.14c8b1fe8d4f from=translated src=- shape=30509fa4 vocab=837fe50d
-/
theorem coordinate_partial_nilpotence_bound (i : σ) (p : MvPolynomial σ B) :
    (pderiv i : MvPolynomial σ B → MvPolynomial σ B)^[
      p.support.sup (fun m => m i) + 1] p = 0 := by
  classical
  apply coordinate_partial_iterate_eq_zero
  intro m hm
  by_contra hc
  have hmem : m ∈ p.support := mem_support_iff.mpr hc
  have hle : m i ≤ p.support.sup (fun a => a i) :=
    Finset.le_sup (f := fun a : σ →₀ ℕ => a i) hmem
  exact (Nat.not_succ_le_self _) (hm.trans hle)

/--
@isnad1 id=locallyn.0h3v.s6.6c7570e3d8d2 from=translated src=- shape=9bccde56 vocab=f9632dcd
-/
theorem coordinate_partial_locallyNilpotent (i : σ) :
    LocallyNilpotent (pderiv i : Derivation B (MvPolynomial σ B) (MvPolynomial σ B)) := by
  intro p
  exact ⟨p.support.sup (fun m => m i) + 1, coordinate_partial_nilpotence_bound i p⟩

/--
@isnad1 id=linearin.0h2v.s8.8b2317f0bf27 from=translated src=- shape=6198acaa vocab=4f724ff2
-/
theorem coordinate_partials_linearIndependent [Fintype σ] :
    LinearIndependent (MvPolynomial σ B)
      (fun i : σ => (pderiv i : Derivation B (MvPolynomial σ B) (MvPolynomial σ B))) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro a ha j
  let ev : Derivation B (MvPolynomial σ B) (MvPolynomial σ B) →+ MvPolynomial σ B :=
    { toFun := fun D => D (X j)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have he := congrArg ev ha
  rw [map_sum, map_zero] at he
  simpa [ev, Derivation.smul_apply, smul_eq_mul, pderiv_X, Pi.single_apply] using he

end AbhyankarSathaye.CommutingDerivations

end

end OAI
