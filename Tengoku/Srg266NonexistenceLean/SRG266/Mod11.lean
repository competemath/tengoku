/-
Copyright (c) 2026 Kay Akiyama.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kay Akiyama
-/
import Tengoku.Srg266NonexistenceLean.SRG266.IntegralLattice
import Tengoku.Seed.Data.ZMod.Basic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

open scoped Matrix

namespace SRG266

variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

def localGramMatrixMod11 (x : V) :
    Matrix (SecondSubconstituent G x)
      (SecondSubconstituent G x) (ZMod 11) :=
  fun B C => localGramMatrix G x B C

def allOnesMatrixMod11 (x : V) :
    Matrix (SecondSubconstituent G x)
      (SecondSubconstituent G x) (ZMod 11) :=
  fun _ _ => 1

/--
@isnad1 id=eq.0h5v.s6.f89106df32d2 from=translated src=- shape=fb996be4 vocab=cb5b4efb
-/
@[simp]
theorem localGramMatrixMod11_apply
    (x : V) (B C : SecondSubconstituent G x) :
    localGramMatrixMod11 G x B C = localGramMatrix G x B C :=
  rfl

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/--
@isnad1 id=eq.0h5v.s6.88a7d745c593 from=translated src=- shape=07ae742a vocab=4e51232f
-/
@[simp] theorem allOnesMatrixMod11_apply
    (x : V) (B C : SecondSubconstituent G x) :
    allOnesMatrixMod11 G x B C = 1 :=
  rfl

/--
@isnad1 id=eq.1h5v.s8.655784132b7e from=translated src=- shape=e4ee4059 vocab=e404d8e4
-/
theorem localGramMatrixMod11_sq_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (localGramMatrixMod11 G x * localGramMatrixMod11 G x) B C =
      localGramMatrixMod11 G x B C + 2 := by
  rw [Matrix.mul_apply]
  have hcast :
      (∑ D,
          (localGramMatrix G x B D : ZMod 11) *
            (localGramMatrix G x D C : ZMod 11)) =
        ((localGramMatrix G x * localGramMatrix G x) B C : ℤ) := by
    rw [Matrix.mul_apply]
    norm_cast
  change
    (∑ D,
      (localGramMatrix G x B D : ZMod 11) *
        (localGramMatrix G x D C : ZMod 11)) =
      (localGramMatrix G x B C : ZMod 11) + 2
  rw [hcast, localGramMatrix_sq_apply G hG x B C]
  push_cast
  change
    (45 : ZMod 11) * (localGramMatrix G x B C : ZMod 11) + 90 =
      (localGramMatrix G x B C : ZMod 11) + 2
  have h45 : (45 : ZMod 11) = 1 := by decide
  have h90 : (90 : ZMod 11) = 2 := by decide
  rw [h45, h90]
  ring

/--
@isnad1 id=eq.1h3v.s9.139694a1d885 from=translated src=- shape=98e0594e vocab=869b6539
-/
theorem localGramMatrixMod11_sq
    (hG : IsHypothetical G) (x : V) :
    localGramMatrixMod11 G x * localGramMatrixMod11 G x =
      localGramMatrixMod11 G x +
        (2 : ZMod 11) • allOnesMatrixMod11 G x := by
  ext B C
  rw [localGramMatrixMod11_sq_apply G hG x B C]
  simp

/--
@isnad1 id=eq.1h5v.s8.68c6b141e946 from=translated src=- shape=a9e92809 vocab=eede3dd8
-/
theorem localGramMatrixMod11_mul_allOnes_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (localGramMatrixMod11 G x * allOnesMatrixMod11 G x) B C = 0 := by
  rw [Matrix.mul_apply]
  simp only [localGramMatrixMod11, allOnesMatrixMod11, mul_one]
  have hcast :
      (∑ D, (localGramMatrix G x B D : ZMod 11)) =
        ((∑ D, localGramMatrix G x B D : ℤ) : ZMod 11) := by
    norm_cast
  rw [hcast, localGramMatrix_row_sum G hG x B]
  exact (by decide : (165 : ZMod 11) = 0)

/--
@isnad1 id=eq.1h3v.s8.a03946337111 from=translated src=- shape=3b99b768 vocab=eede3dd8
-/
theorem localGramMatrixMod11_mul_allOnes
    (hG : IsHypothetical G) (x : V) :
    localGramMatrixMod11 G x * allOnesMatrixMod11 G x = 0 := by
  ext B C
  exact localGramMatrixMod11_mul_allOnes_apply G hG x B C

/--
@isnad1 id=eq.1h5v.s8.c63e2ed6dca8 from=translated src=- shape=a9e92809 vocab=eede3dd8
-/
theorem allOnesMatrixMod11_mul_localGram_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (allOnesMatrixMod11 G x * localGramMatrixMod11 G x) B C = 0 := by
  rw [Matrix.mul_apply]
  simp only [localGramMatrixMod11, allOnesMatrixMod11, one_mul]
  have hcast :
      (∑ D, (localGramMatrix G x D C : ZMod 11)) =
        ((∑ D, localGramMatrix G x D C : ℤ) : ZMod 11) := by
    norm_cast
  rw [hcast]
  have hcolumn :
      ∑ D, localGramMatrix G x D C = 165 := by
    rw [← localGramMatrix_row_sum G hG x C]
    apply Finset.sum_congr rfl
    intro D _
    exact localGramMatrix_comm G x D C
  rw [hcolumn]
  exact (by decide : (165 : ZMod 11) = 0)

/--
@isnad1 id=eq.1h3v.s8.c46f60eec390 from=translated src=- shape=3b99b768 vocab=eede3dd8
-/
theorem allOnesMatrixMod11_mul_localGram
    (hG : IsHypothetical G) (x : V) :
    allOnesMatrixMod11 G x * localGramMatrixMod11 G x = 0 := by
  ext B C
  exact allOnesMatrixMod11_mul_localGram_apply G hG x B C

/--
@isnad1 id=eq.1h5v.s8.d6f979d5997e from=translated src=- shape=a9e92809 vocab=c36065d2
-/
theorem allOnesMatrixMod11_sq_apply
    (hG : IsHypothetical G) (x : V)
    (B C : SecondSubconstituent G x) :
    (allOnesMatrixMod11 G x * allOnesMatrixMod11 G x) B C = 0 := by
  rw [Matrix.mul_apply]
  simp only [allOnesMatrixMod11, one_mul]
  calc
    (∑ _D : SecondSubconstituent G x, (1 : ZMod 11)) =
        (Fintype.card (SecondSubconstituent G x) : ZMod 11) := by
      simp
    _ = (220 : ZMod 11) := by
      exact congrArg (fun n : ℕ => (n : ZMod 11))
        (secondSubconstituent_card G hG x)
    _ = 0 := by decide

/--
@isnad1 id=eq.1h3v.s8.f51801c69e9b from=translated src=- shape=3b99b768 vocab=c36065d2
-/
theorem allOnesMatrixMod11_sq
    (hG : IsHypothetical G) (x : V) :
    allOnesMatrixMod11 G x * allOnesMatrixMod11 G x = 0 := by
  ext B C
  exact allOnesMatrixMod11_sq_apply G hG x B C

/--
@isnad1 id=eq.1h3v.s8.d7d5408617f5 from=translated src=- shape=ec56faba vocab=c4576718
-/
@[simp]
theorem localGramMatrixMod11_mulVec_one
    (hG : IsHypothetical G) (x : V) :
    localGramMatrixMod11 G x *ᵥ
        (1 : SecondSubconstituent G x → ZMod 11) = 0 := by
  funext B
  rw [Matrix.mulVec_apply_eq_sum]
  simp only [localGramMatrixMod11, Pi.one_apply, mul_one, Pi.zero_apply]
  have hcast :
      (∑ C, (localGramMatrix G x B C : ZMod 11)) =
        ((∑ C, localGramMatrix G x B C : ℤ) : ZMod 11) := by
    norm_cast
  rw [hcast, localGramMatrix_row_sum G hG x B]
  exact (by decide : (165 : ZMod 11) = 0)

/--
@isnad1 id=ne.1h3v.s7.615b0c4973dd from=translated src=- shape=3115cea9 vocab=a5066fbf
-/
theorem allOnesMatrixMod11_ne_zero
    (hG : IsHypothetical G) (x : V) :
    allOnesMatrixMod11 G x ≠ 0 := by
  have hcard :
      Fintype.card (SecondSubconstituent G x) = 220 :=
    secondSubconstituent_card G hG x
  have : Nonempty (SecondSubconstituent G x) :=
    Fintype.card_pos_iff.mp (by omega)
  let B : SecondSubconstituent G x := Classical.choice inferInstance
  intro hzero
  have hentry := congrFun (congrFun hzero B) B
  change (1 : ZMod 11) = 0 at hentry
  exact (by decide : (1 : ZMod 11) ≠ 0) hentry

/--
@isnad1 id=eq.1h3v.s9.0c4db435e646 from=translated src=- shape=5b6643dd vocab=33b5a166
-/
theorem localGramMatrixMod11_mul_sub_one
    (hG : IsHypothetical G) (x : V) :
    localGramMatrixMod11 G x *
        (localGramMatrixMod11 G x - 1) =
      (2 : ZMod 11) • allOnesMatrixMod11 G x := by
  have hsq := localGramMatrixMod11_sq G hG x
  noncomm_ring [hsq]

/--
@isnad1 id=ne.1h3v.s9.7b3ab7bbc8b0 from=translated src=- shape=a48ae584 vocab=23b25d17
-/
theorem localGramMatrixMod11_mul_sub_one_ne_zero
    (hG : IsHypothetical G) (x : V) :
    localGramMatrixMod11 G x *
        (localGramMatrixMod11 G x - 1) ≠ 0 := by
  rw [localGramMatrixMod11_mul_sub_one G hG x]
  intro hzero
  have hcard :
      Fintype.card (SecondSubconstituent G x) = 220 :=
    secondSubconstituent_card G hG x
  have : Nonempty (SecondSubconstituent G x) :=
    Fintype.card_pos_iff.mp (by omega)
  let B : SecondSubconstituent G x := Classical.choice inferInstance
  have hentry := congrFun (congrFun hzero B) B
  change (2 : ZMod 11) = 0 at hentry
  have htwo : (2 : ZMod 11) ≠ 0 := by decide
  exact htwo hentry

/--
@isnad1 id=eq.1h3v.s9.4fc78d0ee8ca from=translated src=- shape=a6196fa6 vocab=ca1428f2
-/
theorem localGramMatrixMod11_cube_eq_sq
    (hG : IsHypothetical G) (x : V) :
    localGramMatrixMod11 G x *
          localGramMatrixMod11 G x *
        localGramMatrixMod11 G x =
      localGramMatrixMod11 G x *
        localGramMatrixMod11 G x := by
  let L := localGramMatrixMod11 G x
  let J := allOnesMatrixMod11 G x
  have hsq : L * L = L + (2 : ZMod 11) • J := by
    simpa [L, J] using localGramMatrixMod11_sq G hG x
  have hJL : J * L = 0 := by
    simpa [L, J] using allOnesMatrixMod11_mul_localGram G hG x
  change L * L * L = L * L
  calc
    L * L * L = (L + (2 : ZMod 11) • J) * L := by
      rw [hsq]
    _ = L * L := by
      rw [add_mul, smul_mul_assoc, hJL]
      simp

/--
@isnad1 id=eq.1h3v.s9.5052818647ee from=translated src=- shape=237827a8 vocab=ca1428f2
-/
theorem localGramMatrixMod11_sq_idempotent
    (hG : IsHypothetical G) (x : V) :
    (localGramMatrixMod11 G x * localGramMatrixMod11 G x) *
        (localGramMatrixMod11 G x * localGramMatrixMod11 G x) =
      localGramMatrixMod11 G x * localGramMatrixMod11 G x := by
  let L := localGramMatrixMod11 G x
  have hcube : L * L * L = L * L := by
    simpa [L] using localGramMatrixMod11_cube_eq_sq G hG x
  change (L * L) * (L * L) = L * L
  calc
    (L * L) * (L * L) = (L * L * L) * L :=
      (Matrix.mul_assoc (L * L) L L).symm
    _ = (L * L) * L := congrArg (fun A => A * L) hcube
    _ = L * L := hcube

end SRG266
