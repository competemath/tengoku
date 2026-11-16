import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_RingTheory_AffineDilatation

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.lean`: wrote out 4 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 1 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow

set_option autoImplicit false

universe u

namespace AffineDilatation
export _root_.AffineDilatation (subalgebra gen_subset)
namespace PowDescription
open _root_.AffineDilatation

variable {A : Type u} [CommRing A]

def den (a : A) (n : ℕ) : Submonoid.powers a := ⟨a ^ n, n, rfl⟩

/--
@isnad1 id=eq.0h4v.s8.a6e0afe6fabd from=translated src=- shape=d80479ac vocab=913cce07
-/
theorem den_add (a : A) (m n : ℕ) : den a (m + n) = den a m * den a n :=
  Subtype.ext (pow_add a m n)

/--
@isnad1 id=eq.0h2v.s7.45f9b4b982e9 from=translated src=- shape=d1428eb3 vocab=8d2ac9f0
-/
theorem den_zero (a : A) : den a 0 = 1 := Subtype.ext (pow_zero a)

/--
@isnad1 id=eq.0h2v.s6.95494d0147db from=translated src=- shape=3b2d5994 vocab=fa4215c0
-/
theorem den_one (a : A) : den a 1 = ⟨a, Submonoid.mem_powers a⟩ := Subtype.ext (pow_one a)

noncomputable def frac (a : A) (n : ℕ) (g : A) : Localization.Away a :=
  IsLocalization.mk' (Localization.Away a) g (den a n)

/--
@isnad1 id=eq.0h3v.s7.fcb08c4319c1 from=translated src=- shape=d8ad7fe1 vocab=d56c4cb2
-/
theorem frac_zero_right (a : A) (g : A) : frac a 0 g = algebraMap A (Localization.Away a) g := by
  rw [frac, den_zero, IsLocalization.mk'_one]

/--
@isnad1 id=eq.0h4v.s8.8a68dfe1f58b from=translated src=- shape=6221bfaa vocab=0e20486d
-/
theorem frac_eq_mul (a : A) (n : ℕ) (g : A) :
    frac a n g = algebraMap A (Localization.Away a) g * frac a n 1 :=
  IsLocalization.mk'_eq_mul_mk'_one g (den a n)

/--
@isnad1 id=eq.0h5v.s7.4549971c8080 from=translated src=- shape=68d9eb8a vocab=48cd0ec2
-/
theorem frac_add_num (a : A) (n : ℕ) (g h : A) :
    frac a n (g + h) = frac a n g + frac a n h := by
  rw [frac_eq_mul, map_add, add_mul, ← frac_eq_mul, ← frac_eq_mul]

/--
@isnad1 id=eq.0h6v.s7.18d4b958f71b from=translated src=- shape=6e504401 vocab=6627d927
-/
theorem frac_add (a : A) (m n : ℕ) (g h : A) :
    frac a m g + frac a n h = frac a (m + n) (g * a ^ n + h * a ^ m) := by
  rw [frac, frac, frac, ← IsLocalization.mk'_add, den_add]
  rfl

/--
@isnad1 id=eq.0h6v.s6.8225305efc07 from=translated src=- shape=b765ce46 vocab=e3552619
-/
theorem frac_mul (a : A) (m n : ℕ) (g h : A) :
    frac a m g * frac a n h = frac a (m + n) (g * h) := by
  rw [frac, frac, frac, ← IsLocalization.mk'_mul, den_add]

/--
@isnad1 id=mem.1h5v.s8.6ea697c7ca0f from=translated src=- shape=4b344109 vocab=0968f3bc
-/
theorem frac_mem_of_mem_pow (I : Ideal A) (a : A) :
    ∀ (n : ℕ) (g : A), g ∈ I ^ n → frac a n g ∈ subalgebra I a := by
  intro n
  induction n with
  | zero =>
      intro g _
      rw [frac_zero_right]
      exact Subalgebra.algebraMap_mem _ g
  | succ n ih =>
      intro g hg
      rw [pow_succ] at hg
      refine Submodule.mul_induction_on hg ?_ ?_
      · intro x hx y hy
        rw [← frac_mul]
        refine Subalgebra.mul_mem _ (ih x hx) ?_
        rw [frac, den_one]
        exact gen_subset I a ⟨y, hy, rfl⟩
      · intro x y hx hy
        rw [frac_add_num]
        exact Subalgebra.add_mem _ hx hy

/--
@isnad1 id=ex.2h4v.s8.3c166e6d5735 from=translated src=- shape=78d4c4b1 vocab=0968f3bc
-/
theorem exists_pow_of_mem (I : Ideal A) (a : A) (ha : a ∈ I) (x : Localization.Away a)
    (hx : x ∈ subalgebra I a) : ∃ n : ℕ, ∃ g ∈ I ^ n, frac a n g = x := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
      obtain ⟨g, hg, rfl⟩ := hx
      refine ⟨1, g, by simpa using hg, ?_⟩
      rw [frac, den_one]
  | algebraMap r =>
      exact ⟨0, r, by simp, frac_zero_right a r⟩
  | add x y _ _ ihx ihy =>
      obtain ⟨m, g, hg, rfl⟩ := ihx
      obtain ⟨n, h, hh, rfl⟩ := ihy
      refine ⟨m + n, g * a ^ n + h * a ^ m, ?_, (frac_add a m n g h).symm⟩
      refine Ideal.add_mem _ ?_ ?_
      · rw [pow_add]; exact Ideal.mul_mem_mul hg (Ideal.pow_mem_pow ha n)
      · rw [add_comm, pow_add]; exact Ideal.mul_mem_mul hh (Ideal.pow_mem_pow ha m)
  | mul x y _ _ ihx ihy =>
      obtain ⟨m, g, hg, rfl⟩ := ihx
      obtain ⟨n, h, hh, rfl⟩ := ihy
      refine ⟨m + n, g * h, ?_, (frac_mul a m n g h).symm⟩
      rw [pow_add]; exact Ideal.mul_mem_mul hg hh

end AffineDilatation.PowDescription
open scoped _root_.P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.AffineDilatation _root_.P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.AffineDilatation.PowDescription
open scoped _root_.P2MW.S_AffineDilatation_mem_subalgebra_iff_exists_mem_pow.AffineDilatation

/--
@isnad1 id=iff.1h4v.s9.28a22e28e859 from=translated src=- shape=44ba15a0 vocab=d03a974b
-/
theorem solution
    {A : Type u} [CommRing A] (I : Ideal A) (a : A) (ha : a ∈ I) (x : Localization.Away a) :
    x ∈ AffineDilatation.subalgebra I a ↔
      ∃ (n : ℕ) (g : A), g ∈ I ^ n ∧
        IsLocalization.mk' (Localization.Away a) g (⟨a ^ n, n, rfl⟩ : Submonoid.powers a) = x :=
  ⟨fun hx => by
    obtain ⟨n, g, hg, hgx⟩ := AffineDilatation.PowDescription.exists_pow_of_mem I a ha x hx
    exact ⟨n, g, hg, hgx⟩,
   fun ⟨n, g, hg, hx⟩ => hx ▸ AffineDilatation.PowDescription.frac_mem_of_mem_pow I a n g hg⟩
