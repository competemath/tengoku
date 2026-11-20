/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.Design.TriangularIso
import Tengoku.Srg266NonexistenceLean.SRG266.Design.Transport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped BigOperators

namespace SRG266.QuasiSymmetric

namespace Derived45

variable {P : Type*} [Fintype P] [DecidableEq P] (E : Derived45 P)

noncomputable def edgeEquiv : P ≃ Edge11 := E.exists_equiv_edge11.choose

/--
@isnad1 id=iff.0h4v.s6.737394be5e15 from=translated src=- shape=a9d35586 vocab=07406bc4
-/
theorem adj_iff_vmeet_edgeEquiv (p q : P) :
    E.blockGraph.Adj p q ↔ Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q) = 1 :=
  E.exists_equiv_edge11.choose_spec.1 p q

/--
@isnad1 id=eq.0h4v.s6.7419559e6a3d from=translated src=- shape=f21b0638 vocab=046d7b36
-/
theorem pairMult_add_vmeet_edgeEquiv (p q : P) :
    E.pairMult p q + Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q)
      = 2 + if p = q then 9 else 0 :=
  E.exists_equiv_edge11.choose_spec.2 p q

noncomputable def coverMember (i : Fin 45) : Finset Edge11 :=
  (E.block i).image E.edgeEquiv

/--
@isnad1 id=iff.0h4v.s6.2c5a31536e62 from=translated src=- shape=5dc6aada vocab=46690c6f
-/
theorem mem_coverMember {i : Fin 45} {e : Edge11} :
    e ∈ E.coverMember i ↔ E.edgeEquiv.symm e ∈ E.block i := by
  rw [coverMember]
  constructor
  · intro h
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    simpa using hp
  · intro h
    exact Finset.mem_image.mpr ⟨E.edgeEquiv.symm e, h, by simp⟩

/--
@isnad1 id=eq.0h3v.s5.787dbf2ea49a from=translated src=- shape=7193e965 vocab=1842097e
-/
theorem card_coverMember (i : Fin 45) : (E.coverMember i).card = 11 := by
  rw [coverMember, Finset.card_image_of_injective _ E.edgeEquiv.injective, E.block_card i]

/--
@isnad1 id=eq.0h4v.s7.96d568d72a66 from=translated src=- shape=d44830be vocab=3df4ae53
-/
theorem pairCount_coverMember (e f : Edge11) :
    pairCount E.coverMember e f = E.pairMult (E.edgeEquiv.symm e) (E.edgeEquiv.symm f) := by
  have hset : (Finset.univ.filter fun i => e ∈ E.coverMember i ∧ f ∈ E.coverMember i)
      = Finset.univ.filter fun i =>
          E.edgeEquiv.symm e ∈ E.block i ∧ E.edgeEquiv.symm f ∈ E.block i := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, E.mem_coverMember]
  exact congrArg Finset.card hset

/--
@isnad1 id=eq.0h5v.s6.b29b4046dc85 from=translated src=- shape=58057c5f vocab=a34e6fe8
-/
theorem sum_coverMember {M : Type*} [AddCommMonoid M] (i : Fin 45) (F : Edge11 → M) :
    (∑ e ∈ E.coverMember i, F e) = ∑ p ∈ E.block i, F (E.edgeEquiv p) := by
  rw [coverMember, Finset.sum_image]
  exact fun x _ y _ h => E.edgeEquiv.injective h

/--
@isnad1 id=eq.0h3v.s6.c2f51640722f from=translated src=- shape=bcdda211 vocab=74e92cb3
-/
theorem sum_inter_block_sq (i : Fin 45) :
    (∑ j, ((E.block i) ∩ (E.block j)).card ^ 2) = 297 := by
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  have hoff : ∀ j ∈ (Finset.univ : Finset (Fin 45)).erase i,
      ((E.block i) ∩ (E.block j)).card ^ 2 = 4 := by
    intro j hj
    rw [E.pair_meet i j (Ne.symm (Finset.mem_erase.mp hj).1)]
    norm_num
  rw [Finset.sum_congr rfl hoff, Finset.sum_const,
    Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin,
    Finset.inter_self, E.block_card i]
  norm_num [nsmul_eq_mul]

/--
@isnad1 id=eq.0h3v.s5.6db27da05a84 from=translated src=- shape=523b15cc vocab=6a523281
-/
theorem sum_pairMult_block (i : Fin 45) :
    (∑ p ∈ E.block i, ∑ q ∈ E.block i, E.pairMult p q) = 297 := by
  have h : (∑ p ∈ E.block i, ∑ q ∈ E.block i, E.pairMult p q)
      = ∑ j, ((E.block i) ∩ (E.block j)).card ^ 2 :=
    (sum_inter_card_sq E.block (E.block i)).symm
  rw [h, E.sum_inter_block_sq i]

/--
@isnad1 id=eq.0h3v.s5.202842dd028f from=translated src=- shape=00ad289f vocab=e713baac
-/
theorem sum_vmeet_coverMember (i : Fin 45) :
    (∑ e ∈ E.coverMember i, ∑ f ∈ E.coverMember i, Edge11.vmeet e f) = 44 := by
  have hdouble : (∑ e ∈ E.coverMember i, ∑ f ∈ E.coverMember i, Edge11.vmeet e f)
      = ∑ p ∈ E.block i, ∑ q ∈ E.block i,
          Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q) := by
    rw [E.sum_coverMember i fun e => ∑ f ∈ E.coverMember i, Edge11.vmeet e f]
    exact Finset.sum_congr rfl fun p _ => E.sum_coverMember i _
  have htot : (∑ p ∈ E.block i, ∑ q ∈ E.block i,
      (E.pairMult p q + Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q))) = 341 := by
    have hcell : ∀ p ∈ E.block i, (∑ q ∈ E.block i,
        (E.pairMult p q + Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q))) = 31 := by
      intro p hp
      rw [Finset.sum_congr rfl fun q _ => E.pairMult_add_vmeet_edgeEquiv p q,
        Finset.sum_add_distrib, Finset.sum_const, E.block_card i,
        Finset.sum_ite_eq (E.block i) p (fun _ => 9), ite_eq_left hp]
      norm_num [nsmul_eq_mul]
    rw [Finset.sum_congr rfl hcell, Finset.sum_const, E.block_card i]
    norm_num [nsmul_eq_mul]
  have hsplit : (∑ p ∈ E.block i, ∑ q ∈ E.block i,
      (E.pairMult p q + Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q)))
      = (∑ p ∈ E.block i, ∑ q ∈ E.block i, E.pairMult p q)
        + ∑ p ∈ E.block i, ∑ q ∈ E.block i,
            Edge11.vmeet (E.edgeEquiv p) (E.edgeEquiv q) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_add_distrib
  rw [hsplit, E.sum_pairMult_block i] at htot
  rw [hdouble]
  omega

/--
@isnad1 id=eq.0h4v.s6.0469dc7fb1ff from=translated src=- shape=8c3aff9c vocab=d8a49b62
-/
theorem two_regular_coverMember (i : Fin 45) (v : Fin 11) :
    ((E.coverMember i).filter fun e => v ∈ e.vertices).card = 2 := by
  have hsum : (∑ w : Fin 11,
      ((E.coverMember i).filter fun e => w ∈ e.vertices).card) = 22 := by
    have h := Edge11.sum_star_card (E.coverMember i)
    rw [Finset.sum_congr rfl fun e _ => Edge11.card_vertices e, Finset.sum_const,
      E.card_coverMember i] at h
    simpa using h
  have hsq : (∑ w : Fin 11,
      ((E.coverMember i).filter fun e => w ∈ e.vertices).card ^ 2) = 44 := by
    rw [← Edge11.sum_vmeet (E.coverMember i), E.sum_vmeet_coverMember i]
  have hle : ∀ w ∈ (Finset.univ : Finset (Fin 11)),
      4 * ((E.coverMember i).filter fun e => w ∈ e.vertices).card
        ≤ ((E.coverMember i).filter fun e => w ∈ e.vertices).card ^ 2 + 4 :=
    fun w _ => four_mul_le_sq_add_four _
  have heq : (∑ w : Fin 11,
      4 * ((E.coverMember i).filter fun e => w ∈ e.vertices).card)
      = ∑ w : Fin 11,
          (((E.coverMember i).filter fun e => w ∈ e.vertices).card ^ 2 + 4) := by
    rw [← Finset.mul_sum, hsum, Finset.sum_add_distrib, hsq, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin]
    norm_num [nsmul_eq_mul]
  have hpt := (Finset.sum_eq_sum_iff_of_le hle).mp heq v (Finset.mem_univ v)
  have hz : ((((E.coverMember i).filter fun e => v ∈ e.vertices).card : ℤ) - 2) ^ 2 = 0 := by
    have hcast : (4 : ℤ) *
        ((((E.coverMember i).filter fun e => v ∈ e.vertices).card : ℤ))
        = (((E.coverMember i).filter fun e => v ∈ e.vertices).card : ℤ) ^ 2 + 4 := by
      exact_mod_cast hpt
    linear_combination -hcast
  have htwo : ((((E.coverMember i).filter fun e => v ∈ e.vertices).card : ℤ)) = 2 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hz
    linarith
  exact_mod_cast htwo

/--
@isnad1 id=eq.2h4v.s6.4ed70ee65bda from=translated src=- shape=cf1e8b1e vocab=6661c939
-/
theorem cherry_exact_coverMember (e f : Edge11) (hef : e ≠ f)
    (hvm : Edge11.vmeet e f = 1) : pairCount E.coverMember e f = 1 := by
  have hne : E.edgeEquiv.symm e ≠ E.edgeEquiv.symm f := fun hcon =>
    hef (E.edgeEquiv.symm.injective hcon)
  have h := E.pairMult_add_vmeet_edgeEquiv (E.edgeEquiv.symm e) (E.edgeEquiv.symm f)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hvm, ite_eq_right hne] at h
  rw [E.pairCount_coverMember]
  omega

/--
@isnad1 id=eq.1h4v.s6.529434063191 from=translated src=- shape=076fda7d vocab=6661c939
-/
theorem disjoint_twice_coverMember (e f : Edge11) (hvm : Edge11.vmeet e f = 0) :
    pairCount E.coverMember e f = 2 := by
  have hef : e ≠ f := by
    rintro rfl
    rw [Edge11.vmeet_self] at hvm
    exact absurd hvm (by norm_num)
  have hne : E.edgeEquiv.symm e ≠ E.edgeEquiv.symm f := fun hcon =>
    hef (E.edgeEquiv.symm.injective hcon)
  have h := E.pairMult_add_vmeet_edgeEquiv (E.edgeEquiv.symm e) (E.edgeEquiv.symm f)
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply, hvm, ite_eq_right hne] at h
  rw [E.pairCount_coverMember]
  omega

noncomputable def toCherryCover : CherryCover where
  g := E.coverMember
  two_regular := E.two_regular_coverMember
  cherry_exact := E.cherry_exact_coverMember
  disjoint_twice := E.disjoint_twice_coverMember

/--
@isnad1 id=eq.0h3v.s6.6eaad05087a4 from=translated src=- shape=186a17a5 vocab=d81a924f
-/
@[simp] theorem toCherryCover_g (i : Fin 45) :
    E.toCherryCover.g i = (E.block i).image E.edgeEquiv := rfl

noncomputable def isoToCherryCover : Derived45Iso E E.toCherryCover.toDerived45 where
  point := E.edgeEquiv
  index := Equiv.refl (Fin 45)
  map_block _ := rfl

/--
@isnad1 id=isempty.1h2v.s7.bd7887896876 from=translated src=- shape=5e3aa921 vocab=cf25ad28
-/
theorem isEmpty_residual165_of_toCherryCover
    (h : IsEmpty (Residual165 E.toCherryCover.toDerived45)) : IsEmpty (Residual165 E) :=
  isEmpty_residual165_of_iso E.isoToCherryCover h

end Derived45

universe u

abbrev NoResidualCherryCover : Prop :=
  ∀ C : CherryCover, IsEmpty (Residual165 C.toDerived45)

end SRG266.QuasiSymmetric
