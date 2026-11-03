import Tengoku.Seed.RingTheory.Ideal.Operations
import Tengoku.Seed.RingTheory.Ideal.Quotient.Operations

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku repair: removed `#print axioms radical_eq_ker_of_prime_field_squares` (it only prints; the queue checks the axioms of every declaration). -/

/-!
An abstract prime-separation criterion for identifying a parametrization
kernel with the radical of its defining equations.  Applications may build
the commuting squares by localization and finite field extensions; none of
that construction is part of this lemma.
-/

namespace AlbertLean.Generic.PrimeKernelByFieldPoints

universe u v w

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [IsDomain S]

/-- If every prime over `J` admits a field-valued commuting square whose
quotient leg is injective, then the kernel of the domain-valued
parametrization is exactly `J.radical`.
@isnad1 id=eq.2h4v.s9.94e2ac8b0654 from=translated src=- shape=f847a5dc vocab=d37957d1
-/
theorem radical_eq_ker_of_prime_field_squares
    (J : Ideal R) (psi : R →+* S)
    (hJ : J ≤ RingHom.ker psi)
    (hsquare : ∀ (p : Ideal R) (hp : p.IsPrime), J ≤ p →
      ∃ (L : Type w) (_ : Field L) (j : R ⧸ p →+* L),
        Function.Injective j ∧
        ∃ e : S →+* L,
          e.comp psi = j.comp (Ideal.Quotient.mk p)) :
    J.radical = RingHom.ker psi := by
  apply le_antisymm
  · exact (RingHom.ker_isPrime psi).radical_le_iff.mpr hJ
  · rw [Ideal.radical_eq_sInf]
    refine le_sInf fun p hp => ?_
    obtain ⟨L, instL, j, hj, e, hcomm⟩ := hsquare p hp.2 hp.1
    intro x hx
    have hpoint := DFunLike.congr_fun hcomm x
    have hzero : j (Ideal.Quotient.mk p x) = j 0 := by
      calc
        j (Ideal.Quotient.mk p x) = e (psi x) := hpoint.symm
        _ = e 0 := by rw [RingHom.mem_ker.mp hx]
        _ = j 0 := by simp
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hj hzero)

end AlbertLean.Generic.PrimeKernelByFieldPoints
