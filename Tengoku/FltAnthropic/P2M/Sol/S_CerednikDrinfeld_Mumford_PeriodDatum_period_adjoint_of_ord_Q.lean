import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_CerednikDrinfeld_Mumford_PeriodDatum_period_adjoint_of_ord_Q.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_CerednikDrinfeld_Mumford_PeriodDatum_period_adjoint_of_ord_Q

set_option autoImplicit false

open ModularCurve CerednikDrinfeld CerednikDrinfeld.Mumford

theorem solution
    {E V : Type} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}
    {K L : Type} [Field K] [Field L] [Algebra K L] {ord : Additive Kˣ →+ ℤ}
    (P : PeriodDatum D K L ord) (H : HeckeData D)
    (ℓ : Nat.Primes) (x y y' : ↥(ribbonKernel D))
    (h : ∀ z : ↥(ribbonKernel D), P.QL y (heckeKernelMap H ℓ z) = P.QL y' z) :
    ribbonGram D (heckeKernelMap H ℓ x) y = ribbonGram D x y' := by
  have hinj : Function.Injective (unitsBaseChange K L) := by
    intro u v huv
    have huv' : Units.map (algebraMap K L).toMonoidHom (Additive.toMul u)
        = Units.map (algebraMap K L).toMonoidHom (Additive.toMul v) := huv
    have hval := congrArg (fun w : Lˣ => (w : L)) huv'
    simp only [Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe] at hval
    exact Additive.toMul.injective (Units.ext ((algebraMap K L).injective hval))
  have hQ : P.Q y (heckeKernelMap H ℓ x) = P.Q y' x := by
    have hx := h x
    simp only [PeriodDatum.QL_apply] at hx
    exact hinj hx
  rw [← P.ord_Q, ← P.ord_Q, P.Q_symm (heckeKernelMap H ℓ x) y, hQ, P.Q_symm y' x]
