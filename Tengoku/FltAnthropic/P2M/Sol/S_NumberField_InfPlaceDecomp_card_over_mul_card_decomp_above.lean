import Tengoku
import Tengoku.FltAnthropic.Definitions.Def_NumberField_ArchimedeanIdeleModule

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-! Tengoku change notice: this file was changed by the Tengoku factory from https://github.com/anthropics/fermats-last-theorem@aa2d8b34692b, `P2M/Sol/S_NumberField_InfPlaceDecomp_card_over_mul_card_decomp_above.lean`: removed the import of `P2M.Util`. What every declaration states is unchanged, and every proof is checked again by the kernel and by the tree's own build. -/
namespace P2MW.S_NumberField_InfPlaceDecomp_card_over_mul_card_decomp_above

set_option autoImplicit false
open IsDedekindDomain NumberField

/--
@isnad1 id=eq.0h3v.s8.db4cc61ca040 from=translated src=- shape=56c76b65 vocab=670fa684
-/
theorem solution (E K : Type) [Field E] [NumberField E] [Field K] [NumberField K]
    [Algebra E K] [IsGalois E K] (v : InfinitePlace E) :
    Nat.card {w : InfinitePlace K // w.comap (algebraMap E K) = v} *
      Nat.card (NumberField.InfPlaceDecomp.decomp E K (NumberField.ArchIdele.above E K v)) = Nat.card (K ≃ₐ[E] K) := by
  have h0 := NumberField.ArchIdele.comap_above E K v
  have e : {w : InfinitePlace K // w.comap (algebraMap E K) = v} ≃
      MulAction.orbit (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v) :=
    Equiv.subtypeEquivRight fun w => by
      rw [NumberField.InfinitePlace.mem_orbit_iff, h0, eq_comm]
  rw [Nat.card_congr e]
  change Nat.card (MulAction.orbit (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v)) *
      Nat.card (MulAction.stabilizer (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v)) = _
  rw [← Nat.card_prod]
  exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup (K ≃ₐ[E] K) (NumberField.ArchIdele.above E K v))
