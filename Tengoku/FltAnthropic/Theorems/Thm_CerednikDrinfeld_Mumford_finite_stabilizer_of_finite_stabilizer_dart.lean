import Tengoku.FltAnthropic.Definitions.Def_CerednikDrinfeld_MumfordPeriod
import Tengoku.FltAnthropic.P2M.Sol.S_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open CerednikDrinfeld CerednikDrinfeld.Mumford MulAction

theorem CerednikDrinfeld.Mumford.finite_stabilizer_of_finite_stabilizer_dart
    (G : Type) [Group G] {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) [GraphAction G 𝒯]
    (v : W) (hfin : (𝒯.neighborSet v).Finite) (hne : (𝒯.neighborSet v).Nonempty)
    (hD : ∀ d : 𝒯.Dart, d.fst = v → Finite (stabilizer G d)) :
    Finite (stabilizer G v) := by exact @_root_.P2MW.S_CerednikDrinfeld_Mumford_finite_stabilizer_of_finite_stabilizer_dart.solution G _ W _ 𝒯 _ v hfin hne hD
