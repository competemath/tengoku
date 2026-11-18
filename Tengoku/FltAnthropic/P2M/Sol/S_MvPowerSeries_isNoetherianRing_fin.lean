import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_MvPowerSeries_isNoetherianRing_fin.lean`: wrote out 8 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 8 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_MvPowerSeries_isNoetherianRing_fin

set_option autoImplicit false

namespace W2MV
open MvPowerSeries

open Finset.HasAntidiagonal (antidiagonal mem_antidiagonal)

noncomputable section

namespace MvPowerSeries

section IndexBijection

variable {α β : Type*}

theorem Finsupp.sumElim_injective2 :
    Function.Injective2 (Finsupp.sumElim : (α →₀ ℕ) → (β →₀ ℕ) → (α ⊕ β →₀ ℕ)) := by
  intro a a' b b' h
  constructor
  · simpa [Finsupp.comapDomain_inl_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inl d Sum.inl_injective.injOn) h
  · simpa [Finsupp.comapDomain_inr_sumElim] using
      congrArg (fun d => Finsupp.comapDomain Sum.inr d Sum.inr_injective.injOn) h

end IndexBijection

section SumRingEquiv

variable (α β : Type*) {R : Type*} [CommSemiring R]

def sumToFun (f : MvPowerSeries (α ⊕ β) R) : MvPowerSeries α (MvPowerSeries β R) :=
  fun a => fun b => f (a.sumElim b)

def sumInvFun (g : MvPowerSeries α (MvPowerSeries β R)) : MvPowerSeries (α ⊕ β) R :=
  fun d => g (d.comapDomain Sum.inl Sum.inl_injective.injOn)
    (d.comapDomain Sum.inr Sum.inr_injective.injOn)

variable {α β}

@[scoped simp]
theorem coeff_sumToFun (f : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff b (coeff a (sumToFun α β f)) = coeff (a.sumElim b) f :=
  rfl

theorem coeff_mul_sumElim [DecidableEq α] [DecidableEq β]
    (f g : MvPowerSeries (α ⊕ β) R) (a : α →₀ ℕ) (b : β →₀ ℕ) :
    coeff (a.sumElim b) (f * g) =
      ∑ q ∈ antidiagonal a, ∑ r ∈ antidiagonal b,
        coeff (q.1.sumElim r.1) f * coeff (q.2.sumElim r.2) g := by
  classical
  rw [coeff_mul, ← Finsupp.image_sumElim_product_antidiagonal, Finset.sum_image,
    Finset.sum_product]

  rintro ⟨⟨q₁, q₂⟩, ⟨r₁, r₂⟩⟩ - ⟨⟨q₁', q₂'⟩, ⟨r₁', r₂'⟩⟩ - h
  simp only [Prod.mk.injEq] at h ⊢
  obtain ⟨h₁, h₂⟩ := h
  obtain ⟨hq₁, hr₁⟩ := Finsupp.sumElim_injective2 h₁
  obtain ⟨hq₂, hr₂⟩ := Finsupp.sumElim_injective2 h₂
  exact ⟨⟨hq₁, hq₂⟩, ⟨hr₁, hr₂⟩⟩

variable (α β) (R) in

def sumRingEquiv : MvPowerSeries (α ⊕ β) R ≃+* MvPowerSeries α (MvPowerSeries β R) where
  toFun := sumToFun α β
  invFun := sumInvFun α β
  left_inv f := by
    ext d
    rw [show coeff d (sumInvFun α β (sumToFun α β f)) =
        coeff ((d.comapDomain Sum.inl Sum.inl_injective.injOn).sumElim
          (d.comapDomain Sum.inr Sum.inr_injective.injOn)) f from rfl,
      Finsupp.comapDomain_sumElim_comapDomain]
  right_inv g := by
    ext a b
    rw [show coeff b (coeff a (sumToFun α β (sumInvFun α β g))) =
        coeff ((a.sumElim b).comapDomain Sum.inr Sum.inr_injective.injOn)
          (coeff ((a.sumElim b).comapDomain Sum.inl Sum.inl_injective.injOn) g) from rfl,
      Finsupp.comapDomain_inl_sumElim, Finsupp.comapDomain_inr_sumElim]
  map_add' f g := by
    ext a b
    simp only [map_add, coeff_sumToFun]
  map_mul' f g := by
    classical
    ext a b
    rw [coeff_sumToFun, coeff_mul_sumElim]
    rw [show coeff a (sumToFun α β f * sumToFun α β g) =
        ∑ q ∈ antidiagonal a, coeff q.1 (sumToFun α β f) * coeff q.2 (sumToFun α β g) from
      coeff_mul (φ := sumToFun α β f) (ψ := sumToFun α β g) (n := a), map_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [show coeff b (coeff q.1 (sumToFun α β f) * coeff q.2 (sumToFun α β g)) =
        ∑ r ∈ antidiagonal b, coeff r.1 (coeff q.1 (sumToFun α β f)) *
          coeff r.2 (coeff q.2 (sumToFun α β g)) from coeff_mul ..]
    exact Finset.sum_congr rfl fun r _ => by rw [coeff_sumToFun, coeff_sumToFun]

end SumRingEquiv

section FinSucc

variable {R : Type*} [CommSemiring R]

def finSuccSumEquiv (n : ℕ) : Fin (n + 1) ≃ Unit ⊕ Fin n where
  toFun := Fin.cases (Sum.inl ()) (fun i => Sum.inr i)
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv i := by
    induction i using Fin.cases <;> simp
  right_inv x := by
    rcases x with ⟨⟩ | i <;> simp

variable (R) in

def finSuccRingEquiv (n : ℕ) :
    MvPowerSeries (Fin (n + 1)) R ≃+* PowerSeries (MvPowerSeries (Fin n) R) :=
  ((renameEquiv R (finSuccSumEquiv n)).toRingEquiv).trans (sumRingEquiv Unit (Fin n) R)

end FinSucc

section IsEmpty

variable (σ : Type*) [IsEmpty σ] (R : Type*) [CommSemiring R]

def isEmptyRingEquiv : MvPowerSeries σ R ≃+* R :=
  RingEquiv.ofRingHom (constantCoeff (σ := σ) (R := R)) (C (σ := σ) (R := R))
    (by ext r; simp)
    (by classical
        ext f d
        obtain rfl : d = 0 := Subsingleton.eq_zero d
        simp [coeff_C, coeff_zero_eq_constantCoeff])

end IsEmpty

section Noetherian

theorem isNoetherianRing_fin (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) := by
  induction n with
  | zero =>
    exact isNoetherianRing_of_ringEquiv R (isEmptyRingEquiv (Fin 0) R).symm
  | succ n ih =>
    exact isNoetherianRing_of_ringEquiv _ (finSuccRingEquiv R n).symm

end Noetherian

end MvPowerSeries
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries

end
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries

end W2MV
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV

open IsLocalRing PowerSeries RingTheory
open scoped Pointwise

universe u

namespace W2PS
namespace PowerSeries

variable {R : Type u} [CommRing R]

lemma ker_constantCoeff : RingHom.ker (constantCoeff (R := R)) = Ideal.span {(X : R⟦X⟧)} := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, X_dvd_iff]

noncomputable def quotSpanXEquiv : (R⟦X⟧ ⧸ Ideal.span {(X : R⟦X⟧)}) ≃+* R :=
  (Ideal.quotEquivOfEq ker_constantCoeff.symm).trans
    (RingHom.quotientKerEquivOfSurjective constantCoeff_surj)

section IsLocalRing

variable [IsLocalRing R]

end IsLocalRing
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV

section KrullDim
variable (R) [IsNoetherianRing R] [IsLocalRing R]

end KrullDim
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV

section MaximalIdealSpan
variable [IsLocalRing R]

end MaximalIdealSpan
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV

end PowerSeries
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2PS.PowerSeries
end W2PS
open scoped _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV.MvPowerSeries _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2MV _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2PS.PowerSeries _root_.P2MW.S_MvPowerSeries_isNoetherianRing_fin.W2PS

open IsLocalRing

theorem solution (R : Type*) [CommRing R] [IsNoetherianRing R] (n : ℕ) :
    IsNoetherianRing (MvPowerSeries (Fin n) R) :=
  W2MV.MvPowerSeries.isNoetherianRing_fin R n
