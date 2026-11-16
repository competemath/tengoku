import Tengoku

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_AddCommGroup_natCard_torsionBy_prod_eq_mul.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_AddCommGroup_natCard_torsionBy_prod_eq_mul

set_option autoImplicit false

universe u v

/--
@isnad1 id=eq.0h3v.s8.e217218e5e73 from=translated src=- shape=f28c3c2b vocab=6d73fe48
-/
theorem solution
    (A : Type u) (B : Type v) [AddCommGroup A] [AddCommGroup B] (N : ℕ) :
    Nat.card (Submodule.torsionBy ℤ (A × B) (N : ℤ)) =
      Nat.card (Submodule.torsionBy ℤ A (N : ℤ)) * Nat.card (Submodule.torsionBy ℤ B (N : ℤ)) := by
  rw [← Nat.card_prod]
  refine Nat.card_congr ⟨fun x => (⟨x.1.1, ?_⟩, ⟨x.1.2, ?_⟩), fun y => ⟨(y.1.1, y.2.1), ?_⟩, fun x => rfl, fun y => rfl⟩
  · have := x.2; rw [Submodule.mem_torsionBy_iff] at this ⊢; exact (Prod.ext_iff.mp this).1
  · have := x.2; rw [Submodule.mem_torsionBy_iff] at this ⊢; exact (Prod.ext_iff.mp this).2
  · rw [Submodule.mem_torsionBy_iff, Prod.smul_mk, Prod.mk_eq_zero]
    exact ⟨(Submodule.mem_torsionBy_iff _ _).mp y.1.2, (Submodule.mem_torsionBy_iff _ _).mp y.2.2⟩
