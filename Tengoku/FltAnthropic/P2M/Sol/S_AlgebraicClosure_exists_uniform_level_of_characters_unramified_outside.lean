import Tengoku.FltAnthropic.Definitions.Def_FLTPrelim_Ramification
import Tengoku.Seed.FieldTheory.KummerExtension
import Tengoku.Seed.RingTheory.DedekindDomain.SelmerGroup
import Tengoku.Seed.RingTheory.DedekindDomain.Factorization
import Tengoku.Seed.RingTheory.DedekindDomain.Ideal.Lemmas
import Tengoku.Seed.FieldTheory.Galois.Basic
import Tengoku.Seed.FieldTheory.Normal.Closure
import Tengoku.Seed.FieldTheory.IsAlgClosed.AlgebraicClosure
import Tengoku.Seed.RingTheory.Polynomial.Cyclotomic.Roots
import Tengoku.Seed.NumberTheory.NumberField.Basic
import Tengoku.Seed.RingTheory.Ideal.NatInt
import Tengoku.Seed.RingTheory.Ideal.GoingUp
import Tengoku.Seed.GroupTheory.Index
import Tengoku.Seed.GroupTheory.QuotientGroup.Basic
import Tengoku.Seed.FieldTheory.IntermediateField.Adjoin.Algebra
import Tengoku.Seed.Algebra.Group.Subgroup.ZPowers.Basic
import Tengoku.Seed.LinearAlgebra.Dimension.Free
import Tengoku.Seed.Algebra.NoZeroSMulDivisors.Basic
import Tengoku.Seed.NumberTheory.NumberField.ClassNumber
import Tengoku.Seed.NumberTheory.NumberField.Units.DirichletTheorem
import Tengoku.FltAnthropic.Theorems.Thm_IsDedekindDomain_selmerGroup_finite_of_finite_classGroup_of_fg_units
import Tengoku.FltAnthropic.Theorems.Thm_ValuationSubring_exists_mem_inertiaSubgroupIn_fixing_ne_of_not_dvd_valuation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside.lean`: wrote out 2 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside

set_option autoImplicit false

open NumberField IsDedekindDomain

namespace WtTF

local notation "ℚ̄" => AlgebraicClosure ℚ

namespace Chi

scoped instance instIsAlgebraicRat : Algebra.IsAlgebraic ℚ ℚ̄ := AlgebraicClosure.isAlgebraic ℚ

scoped instance instIsAlgebraicOver (K : IntermediateField ℚ ℚ̄) : Algebra.IsAlgebraic K ℚ̄ :=
  Algebra.IsAlgebraic.tower_top (K := ℚ) (↥K)

scoped instance instIsAlgClosure (K : IntermediateField ℚ ℚ̄) : IsAlgClosure K ℚ̄ :=
  ⟨inferInstance, inferInstance⟩

theorem exists_primitiveRoot (p₀ : ℕ) (hp₀ : p₀.Prime) : ∃ ζ : ℚ̄, IsPrimitiveRoot ζ p₀ := by
  haveI : NeZero ((p₀ : ℕ) : ℚ̄) := ⟨Nat.cast_ne_zero.mpr hp₀.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := IsAlgClosed.exists_root (Polynomial.cyclotomic p₀ ℚ̄) (by
    rw [Polynomial.degree_eq_natDegree (Polynomial.cyclotomic_ne_zero p₀ ℚ̄),
      Polynomial.natDegree_cyclotomic, Nat.totient_prime hp₀]
    exact_mod_cast Nat.sub_ne_zero_of_lt hp₀.one_lt)
  exact ⟨ζ, Polynomial.isRoot_cyclotomic_iff.mp hζ⟩

end Chi
open scoped _root_.P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside.WtTF.Chi

end WtTF
open scoped _root_.P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside.WtTF.Chi _root_.P2MW.S_AlgebraicClosure_exists_uniform_level_of_characters_unramified_outside.WtTF
