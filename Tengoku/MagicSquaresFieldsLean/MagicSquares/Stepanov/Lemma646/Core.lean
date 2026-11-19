import Tengoku.MagicSquaresFieldsLean.MagicSquares.Stepanov.Core.Corollary650
import Tengoku.Seed.RingTheory.AdjoinRoot
import Tengoku.Seed.Algebra.Polynomial.Inductions
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

namespace MagicSquares
namespace LN97

open Polynomial

set_option maxHeartbeats 600000

variable {F : Type*} [Field F]

/-!
# LN97 Lemma 6.46: block elimination

This file formalizes the "base-q block" part of Lemma 6.46 on
pp. 301--303 of Lidl--Niederreiter.

The coefficients

    h_i(x) = e_{i,0}(x) + e_{i,1}(x) x^q + ... + e_{i,u}(x) x^{qu}

are represented by a polynomial `E i : F[x][z]`, and then `z` is
specialized to `x^q`.  Thus

    blockEval q (E i) = h_i.

The difficult algebraic input in the first block is isolated below as
`QuotientPowerIndependent`.  It says that modulo `x^q`, the powers
`1,g,...,g^(m-1)` are independent for coefficient polynomials in the
degree range appearing in LN97.  The remainder of Lemma 6.46 -- namely,
peeling the q-blocks one by one -- is proved here without any further
irreducibility assumptions.

`FirstBlockIndependence` derives `QuotientPowerIndependent` from
normalized Kummer irreducibility using the orbit-product argument.
`Complete` assembles this with absolute irreducibility and translation
to prove the full statement of LN97 6.46.
-/

/-- Evaluate a polynomial in the block variable `z` at `z = X^q`.-/
noncomputable def blockEval (q : ℕ) (E : Polynomial (Polynomial F)) :
    Polynomial F :=
  eval (X ^ q) E

/-- The relation occurring in LN97 6.46:
`Σ_i h_i g^i = 0`.-/
def BlockRelation {m : ℕ} (q : ℕ) (g : Polynomial F)
    (E : Fin m → Polynomial (Polynomial F)) : Prop :=
  ∑ i : Fin m, blockEval q (E i) * g ^ (i : ℕ) = 0

/-- Remove the first `r` base-`q` blocks of a block polynomial.-/
noncomputable def blockTail :
    ℕ → Polynomial (Polynomial F) → Polynomial (Polynomial F)
  | 0, E => E
  | r + 1, E => (blockTail r E).divX

/--
@isnad1 id=eq.0h2v.s5.486b1a86b94b from=translated src=- shape=91042db7 vocab=9e074255
-/
@[simp] theorem blockTail_zero (E : Polynomial (Polynomial F)) :
    blockTail 0 E = E := rfl

/--
@isnad1 id=eq.0h3v.s6.7055a8cea005 from=translated src=- shape=41611b18 vocab=a901e470
-/
@[simp] theorem blockTail_succ (r : ℕ) (E : Polynomial (Polynomial F)) :
    blockTail (r + 1) E = (blockTail r E).divX := rfl

/-- The coefficient in position `j` after removing `r` blocks is the
original coefficient in position `r+j`.
@isnad1 id=eq.0h4v.s6.9c679304a7b7 from=translated src=- shape=d38359ef vocab=3ab2a9b9
-/
theorem blockTail_coeff (r j : ℕ) (E : Polynomial (Polynomial F)) :
    (blockTail r E).coeff j = E.coeff (r + j) := by
  induction r generalizing j with
  | zero =>
      simp
  | succ r ih =>
      calc
        (blockTail (r + 1) E).coeff j =
            (blockTail r E).coeff (j + 1) := by
              rw [blockTail_succ, Polynomial.coeff_divX]
        _ = E.coeff (r + (j + 1)) := ih (j + 1)
        _ = E.coeff ((r + 1) + j) := by
              congr 1
              omega

/-- If the constant block vanishes, evaluating after removing that block
just factors one `X^q` from the result.
@isnad1 id=eq.1h3v.s8.4a9bb0237606 from=translated src=- shape=c3df7251 vocab=1774fad3
-/
theorem blockEval_eq_blockEval_divX_mul
    (q : ℕ) (E : Polynomial (Polynomial F))
    (h0 : E.coeff 0 = 0) :
    blockEval q E = blockEval q E.divX * X ^ q := by
  have hsplit := Polynomial.divX_mul_X_add E
  have hE : E = E.divX * X := by
    simpa [h0] using hsplit.symm
  calc
    blockEval q E =
        blockEval q (E.divX * X) := by
          exact congrArg (blockEval q) hE
    _ = blockEval q E.divX * X ^ q := by
      simp [blockEval, Polynomial.eval_mul]

/-- Once every constant block is zero, the relation can be divided by
the common factor `X^q`.
@isnad1 id=blockrel.2h5v.s7.43a2119de2b2 from=translated src=- shape=9986caad vocab=7527fc71
-/
theorem blockRelation_divX
    {m q : ℕ} (g : Polynomial F)
    (E : Fin m → Polynomial (Polynomial F))
    (h0 : ∀ i, (E i).coeff 0 = 0)
    (hrel : BlockRelation q g E) :
    BlockRelation q g (fun i => (E i).divX) := by
  unfold BlockRelation at hrel ⊢
  have hprod :
      (∑ i : Fin m, blockEval q ((E i).divX) * g ^ (i : ℕ)) * X ^ q = 0 := by
    calc
      (∑ i : Fin m, blockEval q ((E i).divX) * g ^ (i : ℕ)) * X ^ q
          =
        ∑ i : Fin m,
          (blockEval q ((E i).divX) * g ^ (i : ℕ)) * X ^ q := by
            rw [Finset.sum_mul]
      _ =
        ∑ i : Fin m, blockEval q (E i) * g ^ (i : ℕ) := by
          apply Finset.sum_congr rfl
          intro i hi
          rw [blockEval_eq_blockEval_divX_mul (F := F) q (E i) (h0 i)]
          ring
      _ = 0 := hrel
  have hX : (X ^ q : Polynomial F) ≠ 0 := pow_ne_zero _ Polynomial.X_ne_zero
  exact (mul_eq_zero.mp hprod).resolve_right hX

/-- Modulo `X^q`, evaluating a block polynomial at `X^q` retains only
its constant block.
@isnad1 id=eq.0h3v.s11.bf5b56461324 from=translated src=- shape=54656abf vocab=847a750e
-/
theorem adjoinRoot_mk_blockEval
    (q : ℕ) (E : Polynomial (Polynomial F)) :
    (AdjoinRoot.mk (X ^ q : Polynomial F)) (blockEval q E) =
      (AdjoinRoot.mk (X ^ q : Polynomial F)) (E.coeff 0) := by
  let φ : Polynomial F →+* AdjoinRoot (X ^ q : Polynomial F) :=
    AdjoinRoot.mk (X ^ q : Polynomial F)
  have hXq : φ (X ^ q : Polynomial F) = 0 := by
    exact AdjoinRoot.mk_self
  calc
    φ (blockEval q E)
        = eval (φ (X ^ q : Polynomial F)) (E.map φ) := by
            symm
            exact Polynomial.eval_map_apply φ (X ^ q : Polynomial F)
    _ = eval 0 (E.map φ) := by rw [hXq]
    _ = φ (eval 0 E) := by
      exact Polynomial.eval_zero_map φ E
    _ = φ (E.coeff 0) := by
      exact congrArg φ (Polynomial.coeff_zero_eq_eval_zero E).symm

/-- The exact first-block independence property needed by the recursive
part of LN97 6.46.

This is a quotient-ring formulation of the step proved in the book using
the product over the m-th roots of unity and absolute irreducibility.
Here `D` is the degree allowance `q / m - k`.-/
def QuotientPowerIndependent
    (m q D : ℕ) (g : Polynomial F) : Prop :=
  ∀ a : Fin m → Polynomial F,
    (∀ i, (a i).natDegree ≤ D) →
    (∑ i : Fin m,
      (AdjoinRoot.mk (X ^ q : Polynomial F)) (a i) *
        ((AdjoinRoot.mk (X ^ q : Polynomial F)) g) ^ (i : ℕ)) = 0 →
    ∀ i, a i = 0

/-- Quotient power-independence implies the first-block vanishing step
for an arbitrary family of block polynomials.
@isnad1 id=eq.3h7v.s7.42774eb7b348 from=translated src=- shape=d6f75d51 vocab=9ef005d2
-/
theorem firstBlock_vanishes_of_quotientPowerIndependent
    {m q D : ℕ} {g : Polynomial F}
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hrel : BlockRelation q g E) :
    ∀ i, (E i).coeff 0 = 0 := by
  apply hind (fun i => (E i).coeff 0)
  · intro i
    exact hdeg i 0
  · have hmap :
        (AdjoinRoot.mk (X ^ q : Polynomial F))
          (∑ i : Fin m, blockEval q (E i) * g ^ (i : ℕ)) = 0 := by
      rw [hrel]
      simp
    rw [map_sum] at hmap
    simpa [map_mul, map_pow, adjoinRoot_mk_blockEval (F := F)] using hmap

/-- The relation remains true after removing any prescribed number of
base-q blocks.
@isnad1 id=blockrel.3h7v.s6.289140281587 from=translated src=- shape=962760bd vocab=cc95768b
-/
theorem blockRelation_blockTail
    {m q D : ℕ} {g : Polynomial F}
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hrel : BlockRelation q g E) :
    ∀ r, BlockRelation q g (fun i => blockTail r (E i)) := by
  intro r
  induction r with
  | zero =>
      simpa using hrel
  | succ r ihr =>
      apply blockRelation_divX (F := F) g (fun i => blockTail r (E i))
      · intro i
        apply firstBlock_vanishes_of_quotientPowerIndependent
          (F := F) hind (fun i => blockTail r (E i))
        · intro i j
          rw [blockTail_coeff]
          exact hdeg i (r + j)
        · exact ihr
      · exact ihr

/-- **LN97 Lemma 6.46, block-elimination form.**

Assuming the first-block independence supplied by the
irreducibility/Kummer argument, every coefficient block is zero.
This is the recursive part of the lemma on pp. 302--303.
@isnad1 id=eq.3h7v.s7.6cb50c58fe7d from=translated src=- shape=c8d24d1b vocab=9ef005d2
-/
theorem ln97_6_46_of_quotientPowerIndependent
    {m q D : ℕ} {g : Polynomial F}
    (hind : QuotientPowerIndependent (F := F) m q D g)
    (E : Fin m → Polynomial (Polynomial F))
    (hdeg : ∀ i j, ((E i).coeff j).natDegree ≤ D)
    (hrel : BlockRelation q g E) :
    ∀ i, E i = 0 := by
  intro i
  apply Polynomial.ext
  intro j
  have hrelTail :=
    blockRelation_blockTail (F := F) hind E hdeg hrel j
  have hzero :
      (blockTail j (E i)).coeff 0 = 0 := by
    have hall :=
      firstBlock_vanishes_of_quotientPowerIndependent
        (F := F) hind (fun i => blockTail j (E i))
        (by
          intro i' t
          rw [blockTail_coeff]
          exact hdeg i' (j + t))
        hrelTail
    exact hall i
  rw [blockTail_coeff] at hzero
  simpa using hzero

end LN97
end MagicSquares
