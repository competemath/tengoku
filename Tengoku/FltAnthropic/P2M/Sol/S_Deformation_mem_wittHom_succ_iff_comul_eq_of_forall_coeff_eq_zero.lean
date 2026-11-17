import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_DatumAndHonda
import Tengoku.FltAnthropic.Definitions.Def_Dieudonne_WittVectorHom

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero.lean`: wrote out 5 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_export`, 2 `p2m_open`, 2 `p2m_reactivate`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero

set_option autoImplicit false

open _root_.Function open _root_.Deformation open _root_.Deformation.TruncWitt
open scoped TensorProduct

universe u v

namespace Deformation
export _root_.Deformation (TruncWitt.shift wittHom mem_wittHom_iff)
namespace WittHomKerRestrict
open _root_.Deformation

variable {p : ℕ} [hp : Fact p.Prime]

section Iter

variable {S : Type v} [CommRing S] {S' : Type u} [CommRing S']

noncomputable def shiftIter : (m : ℕ) → (TruncatedWittVector p 1 S →+ TruncatedWittVector p (m + 1) S)
  | 0 => AddMonoidHom.id _
  | m + 1 => (TruncWitt.shift (p := p) (n := m + 1) (R := S)).comp (shiftIter m)

/--
@isnad1 id=eq.0h4v.s10.571396f877d0 from=translated src=- shape=63008d08 vocab=4248094c
-/
theorem shiftIter_succ (m : ℕ) (y : TruncatedWittVector p 1 S) :
    shiftIter (m + 1) y = TruncWitt.shift (shiftIter m y) := rfl

/--
@isnad1 id=injectiv.0h3v.s8.9c00a85193b3 from=translated src=- shape=1b08eb7b vocab=d1c1cf47
-/
theorem shiftIter_injective : ∀ m : ℕ, Injective (shiftIter (p := p) (S := S) m)
  | 0 => fun _ _ h => h
  | m + 1 => fun _ _ h => shiftIter_injective m (shift_injective h)

/--
@isnad1 id=eq.0h6v.s10.bff716bb1217 from=translated src=- shape=d019e0b0 vocab=45836c2d
-/
theorem map_shiftIter (f : S →+* S') : ∀ (m : ℕ) (y : TruncatedWittVector p 1 S),
    map f (shiftIter m y) = shiftIter m (map f y)
  | 0, _ => rfl
  | m + 1, y => by rw [shiftIter_succ, shiftIter_succ, map_shift, map_shiftIter f m y]

/--
@isnad1 id=eq.0h4v.s9.1a492f79481e from=translated src=- shape=1dad8522 vocab=3a2f2b7f
-/
theorem coeff_shiftIter_last : ∀ (m : ℕ) (y : TruncatedWittVector p 1 S),
    (shiftIter m y).coeff (Fin.last m) = y.coeff 0
  | 0, _ => rfl
  | m + 1, y => by
    rw [shiftIter_succ, ← Fin.succ_last, coeff_shift_succ, coeff_shiftIter_last m y]

/--
@isnad1 id=eq.1h5v.s9.9d7f031dc083 from=translated src=- shape=0ea9c9c1 vocab=3a2f2b7f
-/
theorem coeff_shiftIter_of_ne_last : ∀ (m : ℕ) (y : TruncatedWittVector p 1 S) (i : Fin (m + 1)),
    i ≠ Fin.last m → (shiftIter m y).coeff i = 0
  | 0, _, i, hi => absurd (Fin.eq_zero i) (by simpa using hi)
  | m + 1, y, i, hi => by
    rw [shiftIter_succ]
    refine Fin.cases ?_ (fun j hj => ?_) i hi
    · intro _; exact coeff_shift_zero _
    · rw [coeff_shift_succ]
      refine coeff_shiftIter_of_ne_last m y j fun h => hj ?_
      rw [h, Fin.succ_last]

theorem eq_shiftIter_of_forall_coeff_eq_zero (m : ℕ) (x : TruncatedWittVector p (m + 1) S)
    (hx : ∀ i : Fin (m + 1), i ≠ Fin.last m → x.coeff i = 0) :
    x = shiftIter m (TruncatedWittVector.mk p fun _ : Fin 1 => x.coeff (Fin.last m)) := by
  refine TruncatedWittVector.ext fun i => ?_
  by_cases hi : i = Fin.last m
  · subst hi
    rw [coeff_shiftIter_last, TruncatedWittVector.coeff_mk]
  · rw [hx i hi, coeff_shiftIter_of_ne_last m _ i hi]

/--
@isnad1 id=eq.0h4v.s7.31bac3c04915 from=translated src=- shape=c25f7f92 vocab=048cfc75
-/
theorem coeff_zero_add (a b : TruncatedWittVector p 1 S) :
    (a + b).coeff 0 = a.coeff 0 + b.coeff 0 := by
  obtain ⟨a, rfl⟩ := WittVector.truncate_surjective p 1 S a
  obtain ⟨b, rfl⟩ := WittVector.truncate_surjective p 1 S b
  rw [← map_add, WittVector.coeff_truncate, WittVector.coeff_truncate, WittVector.coeff_truncate]
  exact WittVector.add_coeff_zero a b

omit hp [CommRing S] in
theorem eq_iff_coeff_zero (a b : TruncatedWittVector p 1 S) :
    a = b ↔ a.coeff 0 = b.coeff 0 := by
  refine ⟨fun h => h ▸ rfl, fun h => TruncatedWittVector.ext fun i => ?_⟩
  have hi : i = 0 := Fin.eq_zero i
  subst hi
  exact h

end Iter

variable {R : Type u} [CommRing R] {n : ℕ} {A : Type v} [CommRing A] [Bialgebra R A]

/--
@isnad1 id=iff.0h4v.s10.a0edce91d44b from=translated src=- shape=94982a03 vocab=b2c370b3
-/
theorem mem_wittHom_one_iff (y : TruncatedWittVector p 1 A) :
    y ∈ wittHom R p 1 A ↔
      Coalgebra.comul (R := R) (y.coeff 0) = y.coeff 0 ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] y.coeff 0 := by
  rw [mem_wittHom_iff, eq_iff_coeff_zero, coeff_zero_add, coeff_map, coeff_map, coeff_map]
  exact Iff.rfl

/--
@isnad1 id=iff.1h5v.s10.7e78566df11f from=translated src=- shape=8b74e505 vocab=b4b62957
-/
theorem main (x : TruncatedWittVector p (n + 1) A)
    (hx : ∀ i : Fin (n + 1), i ≠ Fin.last n → x.coeff i = 0) :
    x ∈ wittHom R p (n + 1) A ↔
      Coalgebra.comul (R := R) (x.coeff (Fin.last n)) =
        x.coeff (Fin.last n) ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] x.coeff (Fin.last n) := by
  set y : TruncatedWittVector p 1 A := TruncatedWittVector.mk p fun _ : Fin 1 => x.coeff (Fin.last n)
    with hy
  have hxy : x = shiftIter n y := eq_shiftIter_of_forall_coeff_eq_zero n x hx
  have hy0 : y.coeff 0 = x.coeff (Fin.last n) := TruncatedWittVector.coeff_mk _ _
  rw [← hy0, ← mem_wittHom_one_iff (R := R), hxy, mem_wittHom_iff, mem_wittHom_iff,
    map_shiftIter, map_shiftIter, map_shiftIter, ← map_add]
  exact (shiftIter_injective n).eq_iff

end Deformation.WittHomKerRestrict
open scoped _root_.P2MW.S_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero.Deformation _root_.P2MW.S_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero.Deformation.WittHomKerRestrict
open scoped _root_.P2MW.S_Deformation_mem_wittHom_succ_iff_comul_eq_of_forall_coeff_eq_zero.Deformation

/--
@isnad1 id=iff.1h5v.s10.13dc308e471c from=translated src=- shape=3e10c826 vocab=b4b62957
-/
theorem solution
    {R : Type u} [CommRing R] {p : ℕ} [Fact p.Prime] {n : ℕ}
    {A : Type v} [CommRing A] [Bialgebra R A]
    (x : TruncatedWittVector p (n + 1) A)
    (hx : ∀ i : Fin (n + 1), i ≠ Fin.last n → x.coeff i = 0) :
    x ∈ Deformation.wittHom R p (n + 1) A ↔
      Coalgebra.comul (R := R) (x.coeff (Fin.last n)) =
        x.coeff (Fin.last n) ⊗ₜ[R] (1 : A) + (1 : A) ⊗ₜ[R] x.coeff (Fin.last n) :=
  Deformation.WittHomKerRestrict.main x hx
