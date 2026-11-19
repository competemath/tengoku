/-
Copyright (c) 2026 Jeremy Parker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tengoku.MahlerHansenCograph.Formalisation.HansenCograph.GeneralFlagProductShuffle
import Tengoku.Seed.Data.Finite.Sigma

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# All-size product shuffles without bounded ambient orders

Finite maximal chains in two arbitrary finite partial orders inject into
maximal chains in their product.  This is the code domain needed for rooted
upper intervals, whose induced orders have a bottom but no global top.
-/

namespace HansenCograph

universe u v

variable {P : Type u} {Q : Type v}
variable [PartialOrder P] [Finite P]
variable [PartialOrder Q] [Finite Q]

noncomputable instance instGeneralFintypeP : Fintype P := Fintype.ofFinite P
noncomputable instance instGeneralFintypeQ : Fintype Q := Fintype.ofFinite Q

noncomputable instance instFiniteGeneralSizedProductCode
    (R : Type*) [LE R] [Finite R] (n : ℕ) :
    Finite (SizedFlag R n) :=
  Finite.of_injective Subtype.val Subtype.val_injective

noncomputable instance instFiniteGeneralInterleaving (n m : ℕ) :
    Finite (Interleaving n m) :=
  Finite.of_injective (fun s : Interleaving n m => s.1) Subtype.val_injective

abbrev GeneralBoundedSizedProductCode :=
  Σ n : Fin (Fintype.card P), Σ m : Fin (Fintype.card Q),
    SizedFlag P n × SizedFlag Q m × Interleaving n m

noncomputable def generalBoundedSizedFlagProductEmbedding :
    GeneralBoundedSizedProductCode (P := P) (Q := Q) ↪ Flag (P × Q) where
  toFun x := Flag.productShuffle x.2.2.1.1 x.2.2.2.1.1
    x.2.2.1.2 x.2.2.2.1.2 (Interleaving.embedding x.1 x.2.1 x.2.2.2.2)
  inj' := by
    rintro ⟨n, m, f, g, s⟩ ⟨n', m', f', g', s'⟩ h
    have hfstSet : (f.1 : Set P) = (f'.1 : Set P) := by
      calc
        f.1 = Prod.fst ''
            (Flag.productShuffle f.1 g.1 f.2 g.2
              (Interleaving.embedding n m s)).carrier :=
          (Flag.productShuffle_fst_range f.1 g.1 f.2 g.2
            (Interleaving.embedding n m s)).symm
        _ = Prod.fst ''
            (Flag.productShuffle f'.1 g'.1 f'.2 g'.2
              (Interleaving.embedding n' m' s')).carrier :=
          congrArg (fun z : Flag (P × Q) ↦ Prod.fst '' z.carrier) h
        _ = f'.1 := Flag.productShuffle_fst_range f'.1 g'.1 f'.2 g'.2
          (Interleaving.embedding n' m' s')
    have hsndSet : (g.1 : Set Q) = (g'.1 : Set Q) := by
      calc
        g.1 = Prod.snd ''
            (Flag.productShuffle f.1 g.1 f.2 g.2
              (Interleaving.embedding n m s)).carrier :=
          (Flag.productShuffle_snd_range f.1 g.1 f.2 g.2
            (Interleaving.embedding n m s)).symm
        _ = Prod.snd ''
            (Flag.productShuffle f'.1 g'.1 f'.2 g'.2
              (Interleaving.embedding n' m' s')).carrier :=
          congrArg (fun z : Flag (P × Q) ↦ Prod.snd '' z.carrier) h
        _ = g'.1 := Flag.productShuffle_snd_range f'.1 g'.1 f'.2 g'.2
          (Interleaving.embedding n' m' s')
    have hfst : f.1 = f'.1 := by
      apply Flag.ext
      exact hfstSet
    have hsnd : g.1 = g'.1 := by
      apply Flag.ext
      exact hsndSet
    have hcard_f : Nat.card (f.1 : Set P) = Nat.card (f'.1 : Set P) := hfstSet ▸ rfl
    have hcard_g : Nat.card (g.1 : Set Q) = Nat.card (g'.1 : Set Q) := hsndSet ▸ rfl
    have hcard_n : (n : ℕ) + 1 = (n' : ℕ) + 1 := by
      exact f.2.symm.trans (hcard_f.trans f'.2)
    have hcard_m : (m : ℕ) + 1 = (m' : ℕ) + 1 := by
      exact g.2.symm.trans (hcard_g.trans g'.2)
    have hn : n = n' := Fin.ext (by omega)
    have hm : m = m' := Fin.ext (by omega)
    subst n'
    subst m'
    have hf : f = f' := by
      apply Subtype.ext
      exact hfst
    have hg : g = g' := by
      apply Subtype.ext
      exact hsnd
    subst f'
    subst g'
    have hpath : Interleaving.embedding n m s =
        Interleaving.embedding n m s' := by
      exact (Flag.productShuffle_injective_fixed f.1 g.1 f.2 g.2) h
    have hs : s = s' := (Interleaving.embedding n m).injective hpath
    subst s'
    rfl

theorem generalBoundedSizedFlagProduct_card_lower_bound :
    Nat.card (GeneralBoundedSizedProductCode (P := P) (Q := Q)) ≤
      Nat.card (Flag (P × Q)) := by
  exact Nat.card_le_card_of_injective
    (generalBoundedSizedFlagProductEmbedding (P := P) (Q := Q))
    (generalBoundedSizedFlagProductEmbedding (P := P) (Q := Q)).injective

theorem generalBoundedSizedFlagProduct_card_lower_bound_sum :
    (∑ n : Fin (Fintype.card P), ∑ m : Fin (Fintype.card Q),
      Nat.card (SizedFlag P n) * Nat.card (SizedFlag Q m) *
        Nat.choose (n + m) n) ≤ Nat.card (Flag (P × Q)) := by
  have h := generalBoundedSizedFlagProduct_card_lower_bound
    (P := P) (Q := Q)
  simp only [Nat.card_sigma, Nat.card_prod, Set.powersetCard.card,
    Nat.card_fin] at h
  simpa only [Nat.mul_assoc] using h

end HansenCograph
