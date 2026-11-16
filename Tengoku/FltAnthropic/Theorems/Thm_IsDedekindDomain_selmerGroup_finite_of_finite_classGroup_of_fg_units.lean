import Tengoku.Seed.RingTheory.DedekindDomain.SelmerGroup
import Tengoku.Seed.RingTheory.ClassGroup
import Tengoku.FltAnthropic.P2M.Sol.S_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

open IsDedekindDomain

universe u v
theorem IsDedekindDomain.selmerGroup.finite_of_finite_classGroup_of_fg_units
    {R : Type u} [CommRing R] [IsDedekindDomain R] {K : Type v} [Field K] [Algebra R K]
    [IsFractionRing R K] {S : Set (HeightOneSpectrum R)} {n : ℕ} [hn : Fact (0 < n)]
    [Finite (ClassGroup R)] [Monoid.FG Rˣ] [Finite S] :
    Finite (selmerGroup (R := R) (K := K) (S := S) (n := n)) := by exact @_root_.P2MW.S_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units.solution R _ _ K _ _ _ S n hn _ _ _
