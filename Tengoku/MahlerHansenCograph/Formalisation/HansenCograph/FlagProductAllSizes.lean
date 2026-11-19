/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy P Parker
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.FlagProductShuffle
import Tengoku.Seed.Data.Finite.Sigma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# All-size product shuffle codes

The fixed-size shuffle embedding is injective even after the two factor
cardinalities are allowed to vary.  The coordinate projection ranges recover
the two sizes, so a bounded finite sigma type packages all factor flags into
one clean lower bound for product flags.
-/

namespace HansenCograph

universe u v

variable {P : Type u} {Q : Type v}
variable [PartialOrder P] [BoundedOrder P] [Fintype P]
variable [PartialOrder Q] [BoundedOrder Q] [Fintype Q]

/--
@isnad1 id=finite.0h2v.s3.17ea78c7d6ed from=translated src=- shape=65786801 vocab=5c7efa11
-/
noncomputable instance instFiniteSizedFlag (R : Type*) [LE R] [Finite R]
    (n : ℕ) : Finite (SizedFlag R n) :=
  Finite.of_injective Subtype.val Subtype.val_injective

/--
@isnad1 id=finite.0h2v.s4.167e88751568 from=translated src=- shape=fd72fa61 vocab=7cc26951
-/
noncomputable instance instFiniteInterleaving (n m : ℕ) :
    Finite (Interleaving n m) :=
  Finite.of_injective (fun s : Interleaving n m => s.1) Subtype.val_injective

/-- All factor flags whose cardinality can occur in a finite carrier.-/
abbrev BoundedSizedProductCode :=
  Σ n : Fin (Fintype.card P), Σ m : Fin (Fintype.card Q),
    SizedFlag P n × SizedFlag Q m × Interleaving n m

/-- Product shuffle embedding for all possible factor flag sizes.-/
noncomputable def boundedSizedFlagProductEmbedding :
    BoundedSizedProductCode (P := P) (Q := Q) ↪ Flag (P × Q) where
  toFun x :=
    (sizedFlagProductEmbedding (P := P) (Q := Q) x.1 x.2.1
      (x.2.2.1, x.2.2.2.1, x.2.2.2.2))
  inj' := by
    rintro ⟨n, m, f, g, s⟩ ⟨n', m', f', g', s'⟩ h
    let rf := sizedFlagRankedEmbedding (P := P) n f
    let rg := sizedFlagRankedEmbedding (P := Q) m g
    let rf' := sizedFlagRankedEmbedding (P := P) n' f'
    let rg' := sizedFlagRankedEmbedding (P := Q) m' g'
    have hfst : Set.range rf = Set.range rf' := by
      rw [← RankedFlag.prodOfShuffle_fst_range rf rg
          (Interleaving.embedding n m s),
        ← RankedFlag.prodOfShuffle_fst_range rf' rg'
          (Interleaving.embedding n' m' s')]
      exact congrArg (fun z : Flag (P × Q) ↦ Prod.fst '' z.carrier) h
    have hsnd : Set.range rg = Set.range rg' := by
      rw [← RankedFlag.prodOfShuffle_snd_range rf rg
          (Interleaving.embedding n m s),
        ← RankedFlag.prodOfShuffle_snd_range rf' rg'
          (Interleaving.embedding n' m' s')]
      exact congrArg (fun z : Flag (P × Q) ↦ Prod.snd '' z.carrier) h
    have hcard_f := congrArg (fun S : Set P => Nat.card S) hfst
    have hcard_g := congrArg (fun S : Set Q => Nat.card S) hsnd
    have hcard_n : (n : ℕ) + 1 = (n' : ℕ) + 1 := by
      simpa only [Nat.card_range_of_injective rf.injective,
        Nat.card_range_of_injective rf'.injective, Nat.card_fin] using hcard_f
    have hcard_m : (m : ℕ) + 1 = (m' : ℕ) + 1 := by
      simpa only [Nat.card_range_of_injective rg.injective,
        Nat.card_range_of_injective rg'.injective, Nat.card_fin] using hcard_g
    have hn : n = n' := Fin.ext (by omega)
    have hm : m = m' := Fin.ext (by omega)
    subst n'
    subst m'
    have hcode := (sizedFlagProductEmbedding (P := P) (Q := Q) n m).injective h
    cases hcode
    rfl

/- All finite factor flag sizes and all interleavings inject into the product
flag set. -/
/--
@isnad1 id=le.0h2v.s5.406fa1459e67 from=translated src=- shape=356a122c vocab=45966562
-/
theorem boundedSizedFlagProduct_card_lower_bound :
    Nat.card (BoundedSizedProductCode (P := P) (Q := Q)) ≤
      Nat.card (Flag (P × Q)) := by
  exact Nat.card_le_card_of_injective
    (boundedSizedFlagProductEmbedding (P := P) (Q := Q))
    (boundedSizedFlagProductEmbedding (P := P) (Q := Q)).injective

/- Expanded form: sum over the two factor flag sizes, with the binomial
coefficient counting the interleaving choices. -/
/--
@isnad1 id=le.0h2v.s7.d9d45adb1f0c from=translated src=- shape=db480a39 vocab=e84acbb0
-/
theorem boundedSizedFlagProduct_card_lower_bound_sum :
    (∑ n : Fin (Fintype.card P), ∑ m : Fin (Fintype.card Q),
      Nat.card (SizedFlag P n) * Nat.card (SizedFlag Q m) *
        Nat.choose (n + m) n) ≤ Nat.card (Flag (P × Q)) := by
  have h := boundedSizedFlagProduct_card_lower_bound (P := P) (Q := Q)
  simp only [Nat.card_sigma, Nat.card_prod, Set.powersetCard.card,
    Nat.card_fin] at h
  simpa only [Nat.mul_assoc] using h

end HansenCograph
