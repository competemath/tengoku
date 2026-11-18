import Tengoku
import Tengoku.FltAnthropic.P2M.Sol.S_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `Theorems/Thm_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt.lean`: wrote out 1 shortcut(s) of the library's `P2M.Util` (it runs code when a module compiles) as plain Lean: 1 `p2m_exact_reverting`; removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/

set_option autoImplicit false

open Polynomial TensorProduct

universe u

theorem IsDedekindDomain.etale_quotient_map_span_of_forall_isUnramifiedAt
    {k : Type u} [Field k] (B : Type u) [CommRing B] [IsDedekindDomain B]
    [Algebra k[X] B] [Algebra k B] [IsScalarTower k k[X] B] [Module.Finite k[X] B] [NoZeroSMulDivisors k[X] B]
    (h : k[X]) (hirr : Irreducible h) (hsep : h.Separable)
    (hunr : ∀ (P : Ideal B) [P.IsPrime], P ≠ ⊥ → Ideal.span {h} ≤ P.comap (algebraMap k[X] B) →
      Algebra.IsUnramifiedAt k[X] P) :
    Algebra.Etale k (B ⧸ Ideal.map (algebraMap k[X] B) (Ideal.span {h})) := by exact @_root_.P2MW.S_IsDedekindDomain_etale_quotient_map_span_of_forall_isUnramifiedAt.solution k _ B _ _ _ _ _ _ _ h hirr hsep hunr
