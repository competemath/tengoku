import Tengoku
import Tengoku.FltAnthropic.Theorems.Thm_HopfAlgebra_nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_HopfAlgebra_nonempty_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_forall_isIdempotentElem

set_option autoImplicit false

universe u v

namespace S17N1conn

theorem main
    {R : Type u} [CommRing R] (h2 : Irreducible (2 : R))
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    (hrank : Module.finrank R H = 2) (hconn : ∀ e : H, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 2))) := by
  haveI : Nontrivial R := by
    by_contra hR
    rw [not_nontrivial_iff_subsingleton] at hR
    exact h2.not_isUnit (isUnit_of_subsingleton _)
  rcases HopfAlgebra.nonempty_algEquiv_pi_or_bialgEquiv_monoidAlgebra_of_finrank_eq_two_of_irreducible h2 H hrank with hφ | h
  · exfalso
    refine hφ.elim fun φ => ?_
    set f : Fin 2 → R := Pi.single 0 1 with hfdef
    have hf : IsIdempotentElem f := by
      change f * f = f
      rw [hfdef, ← Pi.single_mul, mul_one]
    have hf' : IsIdempotentElem (φ.symm f) := by
      change φ.symm f * φ.symm f = φ.symm f
      rw [← map_mul, hf.eq]
    rcases hconn _ hf' with h0 | h1
    · have h3 : f = 0 := φ.symm.injective (by rw [map_zero, h0])
      have := congr_fun h3 0
      simp [hfdef] at this
    · have h3 : f = 1 := φ.symm.injective (by rw [map_one, h1])
      have := congr_fun h3 1
      simp [hfdef] at this
  · exact h

end S17N1conn

theorem solution
    {R : Type u} [CommRing R] (h2 : Irreducible (2 : R))
    (H : Type v) [CommRing H] [HopfAlgebra R H] [Module.Finite R H] [Module.Free R H]
    (hrank : Module.finrank R H = 2) (hconn : ∀ e : H, IsIdempotentElem e → e = 0 ∨ e = 1) :
    Nonempty (H ≃ₐc[R] MonoidAlgebra R (Multiplicative (ZMod 2))) :=
  S17N1conn.main h2 H hrank hconn
