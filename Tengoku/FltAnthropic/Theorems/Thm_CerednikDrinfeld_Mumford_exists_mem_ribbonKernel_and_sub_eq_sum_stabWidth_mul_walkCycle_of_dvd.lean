import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_SchottkyTreeAction
import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd
    {G : Type} [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (hfin : ∀ w : W, Finite (MulAction.stabilizer G w))
    (τ : W → ZMod 2) (hτ : ∀ (g : G) (w : W), τ (g • w) = τ w) (hadj : ∀ u v : W, 𝒯.Adj u v → τ u ≠ τ v)
    [DecidableEq (QuotEdge G 𝒯)]
    {E V : Type} [Fintype E] [DecidableEq V] (D : DegeneracyData E V)
    (eE : E ≃ {e : QuotEdge G 𝒯 // τ e.out.fst = 0})
    (eV : V ≃ QuotVert G W)
    (ha : ∀ e : E, eV (D.a e) = Quotient.mk (orbitRel G W) (eE e).1.out.fst)
    (hb : ∀ e : E, eV (D.b e) = Quotient.mk (orbitRel G W) (eE e).1.out.snd)
    (φ : W → ℤ) (hφ : ∀ g : G, ∃ n : ℤ, ∀ w : W, φ (g • w) = φ w + n)
    (hharm : ∀ (u : W) (S : Finset W), (∀ x, x ∈ S ↔ 𝒯.Adj u x) → ∑ x ∈ S, (φ x - φ u) = 0)
    (hdiv : ∀ d : 𝒯.Dart, ((Nat.card (MulAction.stabilizer G d) : ℕ) : ℤ) ∣ φ d.snd - φ d.fst) :
    ∃ c : E → ℤ,
      (∀ e : E, φ (eE e).1.out.snd - φ (eE e).1.out.fst = ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e) ∧
      c ∈ ribbonKernel D ∧
      ∀ (u u' : W) (p : 𝒯.Walk u u'),
        φ u' - φ u = ∑ e : E, ((stabWidth G 𝒯 (eE e).1 : ℕ) : ℤ) * c e * walkCycle 𝒯 (fun e => (eE e).1) p e := by exact @_root_.P2MW.S_CerednikDrinfeld_Mumford_exists_mem_ribbonKernel_and_sub_eq_sum_stabWidth_mul_walkCycle_of_dvd.solution G _ W _ 𝒯 _ hfin τ hτ hadj _ E V _ _ D eE eV ha hb φ hφ hharm hdiv
