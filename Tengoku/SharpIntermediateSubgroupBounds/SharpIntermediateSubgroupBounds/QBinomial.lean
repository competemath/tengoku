import Tengoku.SharpIntermediateSubgroupBounds.SharpIntermediateSubgroupBounds.Basic
import Tengoku.Seed.Algebra.BigOperators.Field
import Tengoku.Seed.Algebra.Field.ZMod
import Tengoku.Seed.Algebra.Module.ZMod
import Tengoku.Seed.FieldTheory.Finiteness
import Tengoku.Seed.LinearAlgebra.Matrix.GeneralLinearGroup.Card

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Gaussian binomial coefficients

This file supplies the Gaussian coefficients used in the sharp subgroup-interval
bound.  They are defined by the Gaussian Pascal recurrence; in particular, the
definition is integral and does not involve division.
-/

namespace SharpIntermediateSubgroupBounds

open scoped BigOperators

/-- The Gaussian binomial coefficient `n choose k` with parameter `q`.

The chosen recurrence is
`[n+1,k+1]_q = [n,k]_q + q^(k+1) [n,k+1]_q`, the form used by the
prime-power layer argument.-/
def qBinom (q : ℕ) : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)

/--
@isnad1 id=eq.0h1v.s4.e394c8e45497 from=translated src=- shape=5f667179 vocab=5428b1c1
-/
@[simp] theorem qBinom_zero_zero (q : ℕ) : qBinom q 0 0 = 1 := rfl

/--
@isnad1 id=eq.0h2v.s4.afa35db31283 from=translated src=- shape=92d1e92b vocab=7ab078f8
-/
@[simp] theorem qBinom_zero_succ (q k : ℕ) : qBinom q 0 (k + 1) = 0 := rfl

/--
@isnad1 id=eq.0h2v.s4.603d76a1b6d3 from=translated src=- shape=687adb21 vocab=7ab078f8
-/
@[simp] theorem qBinom_succ_zero (q n : ℕ) : qBinom q (n + 1) 0 = 1 := rfl

/--
@isnad1 id=eq.0h3v.s6.bdcd9420accd from=translated src=- shape=10050eda vocab=5f4abe42
-/
@[simp] theorem qBinom_succ_succ (q n k : ℕ) :
    qBinom q (n + 1) (k + 1) =
      qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1) := rfl

/--
@isnad1 id=eq.1h3v.s4.3a2c08966b78 from=translated src=- shape=5306ff9b vocab=3bf9c8b7
-/
theorem qBinom_eq_zero_of_lt (q : ℕ) : ∀ {n k : ℕ}, n < k → qBinom q n k = 0
  | 0, 0, h => by omega
  | 0, _ + 1, _ => by simp
  | _ + 1, 0, h => by omega
  | n + 1, k + 1, h => by
      rw [qBinom_succ_succ]
      have hnk : n < k := by omega
      have hnks : n < k + 1 := by omega
      simp [qBinom_eq_zero_of_lt q hnk, qBinom_eq_zero_of_lt q hnks]

/--
@isnad1 id=eq.0h2v.s3.4b91cc8b2db1 from=translated src=- shape=c2a510d9 vocab=5428b1c1
-/
@[simp] theorem qBinom_self (q : ℕ) : ∀ n : ℕ, qBinom q n n = 1
  | 0 => by simp
  | n + 1 => by
      rw [qBinom_succ_succ]
      simp [qBinom_self q n, qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]

/-- The Pascal recurrence in the indexing used in the manuscript.
@isnad1 id=eq.2h3v.s6.22e983a2fac4 from=translated src=- shape=154978c5 vocab=b2936f37
-/
theorem qBinom_pascal (q : ℕ) {n k : ℕ} (hn : 0 < n) (hk : 0 < k) :
    qBinom q n k = qBinom q (n - 1) (k - 1) + q ^ k * qBinom q (n - 1) k := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hk)
  simpa using qBinom_succ_succ q n k

/-- The product `(q-1)(q²-1)⋯(qⁿ-1)`.-/
def qFactorial (q n : ℕ) : ℕ :=
  ∏ i ∈ Finset.range n, (q ^ (i + 1) - 1)

/--
@isnad1 id=eq.0h1v.s4.fc6e728a2fe3 from=translated src=- shape=1d838610 vocab=ae89b785
-/
@[simp] theorem qFactorial_zero (q : ℕ) : qFactorial q 0 = 1 := by
  simp [qFactorial]

/--
@isnad1 id=eq.0h2v.s6.b8ed94d6c3fa from=translated src=- shape=97fb70f3 vocab=31895c7b
-/
theorem qFactorial_succ (q n : ℕ) :
    qFactorial q (n + 1) = qFactorial q n * (q ^ (n + 1) - 1) := by
  simp [qFactorial, Finset.prod_range_succ]

/--
@isnad1 id=lt.1h2v.s4.fab8d8ed1bd3 from=translated src=- shape=1852429d vocab=03046cf6
-/
theorem qFactorial_pos {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : 0 < qFactorial q n := by
  rw [qFactorial]
  exact Finset.prod_pos fun i hi ↦ by
    have hiq : 1 < q ^ (i + 1) := by
      exact one_lt_pow₀ (by omega) (by omega)
    omega

private theorem pow_sub_one_add_mul_pow_sub_one {q a b : ℕ} (hq : 1 ≤ q) :
    (q ^ a - 1) + q ^ a * (q ^ b - 1) = q ^ (a + b) - 1 := by
  have ha : 1 ≤ q ^ a := one_le_pow₀ hq
  have hb : 1 ≤ q ^ b := one_le_pow₀ hq
  have hab : q ^ a ≤ q ^ a * q ^ b := by
    simpa using Nat.mul_le_mul_left (q ^ a) hb
  rw [pow_add, Nat.mul_sub_left_distrib, mul_one, add_comm]
  exact tsub_add_tsub_cancel hab ha

/-- The division-free Gaussian factorial identity.
@isnad1 id=eq.2h3v.s5.cea3f41a2187 from=translated src=- shape=3738d603 vocab=4e8ce79f
-/
theorem qBinom_mul_qFactorials {q : ℕ} (hq : 2 ≤ q) :
    ∀ {n k : ℕ}, k ≤ n →
      qBinom q n k * qFactorial q k * qFactorial q (n - k) = qFactorial q n := by
  intro n
  induction n with
  | zero =>
      intro k hk
      have : k = 0 := by omega
      subst k
      simp
  | succ n ih =>
      intro k hk
      cases k with
      | zero => simp
      | succ k =>
          have hkn : k ≤ n := by omega
          by_cases htop : k = n
          · subst k
            rw [qBinom_succ_succ, qBinom_self,
              qBinom_eq_zero_of_lt q (Nat.lt_succ_self n)]
            simp [qFactorial_succ]
          · have hklt : k < n := lt_of_le_of_ne hkn htop
            have hk1 : k + 1 ≤ n := by omega
            have hsub : n - k = (n - (k + 1)) + 1 := by omega
            rw [qBinom_succ_succ, qFactorial_succ, Nat.succ_sub_succ_eq_sub, hsub,
              qFactorial_succ]
            calc
              (qBinom q n k + q ^ (k + 1) * qBinom q n (k + 1)) *
                    (qFactorial q k * (q ^ (k + 1) - 1)) *
                    (qFactorial q (n - (k + 1)) * (q ^ (n - (k + 1) + 1) - 1)) =
                  (qBinom q n k * qFactorial q k * qFactorial q (n - k)) *
                      (q ^ (k + 1) - 1) +
                    q ^ (k + 1) *
                      (qBinom q n (k + 1) * qFactorial q (k + 1) *
                        qFactorial q (n - (k + 1))) *
                      (q ^ (n - k) - 1) := by
                        rw [qFactorial_succ, hsub, qFactorial_succ]
                        ring
              _ = qFactorial q n * (q ^ (k + 1) - 1) +
                    q ^ (k + 1) * qFactorial q n * (q ^ (n - k) - 1) := by
                      rw [ih hkn, ih hk1]
              _ = qFactorial q n * (q ^ (n + 1) - 1) := by
                    have hexp : k + 1 + (n - k) = n + 1 := by omega
                    calc
                      qFactorial q n * (q ^ (k + 1) - 1) +
                          q ^ (k + 1) * qFactorial q n * (q ^ (n - k) - 1) =
                          qFactorial q n * ((q ^ (k + 1) - 1) +
                            q ^ (k + 1) * (q ^ (n - k) - 1)) := by ring
                      _ = qFactorial q n * (q ^ ((k + 1) + (n - k)) - 1) := by
                        rw [pow_sub_one_add_mul_pow_sub_one (by omega)]
                      _ = qFactorial q n * (q ^ (n + 1) - 1) := by rw [hexp]
              _ = qFactorial q (n + 1) := by rw [qFactorial_succ]

/-- Symmetry of Gaussian binomial coefficients.
@isnad1 id=eq.2h3v.s5.632f1c9c4535 from=translated src=- shape=96a99aa8 vocab=992de29f
-/
theorem qBinom_symm {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    qBinom q n k = qBinom q n (n - k) := by
  have hleft := qBinom_mul_qFactorials hq hk
  have hright := qBinom_mul_qFactorials hq (Nat.sub_le n k)
  rw [tsub_tsub_cancel_of_le hk] at hright
  have hden : 0 < qFactorial q k * qFactorial q (n - k) :=
    Nat.mul_pos (qFactorial_pos hq k) (qFactorial_pos hq (n - k))
  apply Nat.eq_of_mul_eq_mul_right hden
  calc
    qBinom q n k * (qFactorial q k * qFactorial q (n - k)) = qFactorial q n := by
      simpa [mul_assoc] using hleft
    _ = qBinom q n (n - k) * (qFactorial q k * qFactorial q (n - k)) := by
      simpa [mul_assoc, mul_left_comm, mul_comm] using hright.symm

/-- The usual product formula, stated in `ℚ` to make the division exact.
@isnad1 id=eq.2h3v.s6.be24ddca1dbb from=translated src=- shape=8113d022 vocab=657e2e07
-/
theorem qBinom_cast_eq_qFactorial_div {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    (qBinom q n k : ℚ) =
      qFactorial q n / (qFactorial q k * qFactorial q (n - k)) := by
  have hden : (qFactorial q k * qFactorial q (n - k) : ℚ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt
      (Nat.mul_pos (qFactorial_pos hq k) (qFactorial_pos hq (n - k))))
  apply (eq_div_iff hden).2
  simpa [mul_assoc] using (show
    (qBinom q n k : ℚ) * (qFactorial q k : ℚ) *
      (qFactorial q (n - k) : ℚ) = (qFactorial q n : ℚ) by
        exact_mod_cast qBinom_mul_qFactorials hq hk)

/-! ## Counting subspaces -/

/-- Ordered linearly independent `k`-frames in a module.-/
abbrev LinearIndependentFrames (K V : Type*) [Semiring K] [AddCommMonoid V] [Module K V]
    (k : ℕ) :=
  {s : Fin k → V // LinearIndependent K s}

/-- The type of `k`-dimensional subspaces.-/
abbrev FinrankSubspaces (K V : Type*) [Semiring K] [AddCommMonoid V] [Module K V]
    (k : ℕ) :=
  {W : Submodule K V // Module.finrank K W = k}

private theorem span_coe_frame_eq_submodule
    {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (k : ℕ) (W : Submodule K V) (s : Fin k → W)
    (hs : LinearIndependent K s) (hW : Module.finrank K W = k) :
    Submodule.span K (Set.range fun i ↦ (s i : V)) = W := by
  have htop : Submodule.span K (Set.range s) = ⊤ :=
    hs.span_eq_top_of_card_eq_finrank' (by simp [hW])
  change Submodule.span K (Set.range (W.subtype ∘ s)) = W
  rw [Set.range_comp, ← Submodule.map_span, htop, Submodule.map_top,
    Submodule.range_subtype]

/-- A linearly independent frame is equivalently a subspace together with a
linearly independent frame which spans that subspace.-/
noncomputable def linearIndependentFramesEquiv
    (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V]
    (k : ℕ) :
    LinearIndependentFrames K V k ≃
      Σ W : FinrankSubspaces K V k, LinearIndependentFrames K W.1 k := by
  let forward : LinearIndependentFrames K V k →
      Σ W : FinrankSubspaces K V k, LinearIndependentFrames K W.1 k := fun s ↦
    ⟨⟨Submodule.span K (Set.range s.1), by
        simpa using finrank_span_eq_card s.2⟩,
      ⟨fun i ↦ ⟨s.1 i, Submodule.subset_span (Set.mem_range_self i)⟩,
        linearIndependent_span s.2⟩⟩
  let backward : (Σ W : FinrankSubspaces K V k,
      LinearIndependentFrames K W.1 k) → LinearIndependentFrames K V k := fun x ↦
    ⟨fun i ↦ (x.2.1 i : V),
      x.2.2.map' x.1.1.subtype (Submodule.ker_subtype x.1.1)⟩
  refine Equiv.ofBijective forward ⟨?_, ?_⟩
  · intro s t hst
    have := congrArg backward hst
    exact Subtype.ext (congrArg Subtype.val this)
  · intro x
    refine ⟨backward x, ?_⟩
    rcases x with ⟨W, s⟩
    have hfirst : (forward (backward ⟨W, s⟩)).1 = W :=
      Subtype.ext (span_coe_frame_eq_submodule k W.1 s.1 s.2 W.2)
    have hsub :
        Submodule.span K (Set.range fun i ↦ ((s.1 i : W.1) : V)) = W.1 :=
      congrArg Subtype.val hfirst
    apply Sigma.ext hfirst
    simp only [forward, backward]
    apply (Subtype.heq_iff_coe_heq ?_ ?_).2
    · apply Function.hfunext rfl
      intro i j hij
      have hij' : i = j := eq_of_heq hij
      subst j
      apply (Subtype.heq_iff_coe_eq ?_).2
      · rfl
      · intro x
        change x ∈ Submodule.span K (Set.range fun i ↦ ((s.1 i : W.1) : V)) ↔ x ∈ W.1
        rw [hsub]
    · exact congrArg (fun U : Submodule K V ↦ Fin k → U) hsub
    · apply Function.hfunext
        (congrArg (fun U : Submodule K V ↦ Fin k → U) hsub)
      intro x y hxy
      congr! 2
      funext z
      rw [hsub]

/-- The number of ordered independent `k`-frames in an `n`-dimensional
vector space over a field of cardinality `q`.-/
def frameProd (q n k : ℕ) : ℕ :=
  ∏ i : Fin k, (q ^ n - q ^ i.val)

/--
@isnad1 id=eq.0h2v.s4.815cdfccb9af from=translated src=- shape=9bf57cd7 vocab=bbcbb6fc
-/
@[simp] theorem frameProd_zero (q n : ℕ) : frameProd q n 0 = 1 := by
  simp [frameProd]

/--
@isnad1 id=eq.0h3v.s6.c9ddb581d40c from=translated src=- shape=f057d4e8 vocab=4feb4db4
-/
theorem frameProd_succ (q n k : ℕ) :
    frameProd q n (k + 1) = frameProd q n k * (q ^ n - q ^ k) := by
  rw [frameProd, Fin.prod_univ_castSucc]
  simp [frameProd]

/-- The product of the powers of `q` which are factored out of an ordered
frame count.-/
def framePower (q k : ℕ) : ℕ := ∏ i : Fin k, q ^ i.val

/--
@isnad1 id=eq.0h1v.s4.f5fdf9f63795 from=translated src=- shape=1d838610 vocab=22c2e65a
-/
@[simp] theorem framePower_zero (q : ℕ) : framePower q 0 = 1 := by
  simp [framePower]

/--
@isnad1 id=eq.0h2v.s5.34d1277b4097 from=translated src=- shape=c832fd96 vocab=66482534
-/
theorem framePower_succ (q k : ℕ) :
    framePower q (k + 1) = framePower q k * q ^ k := by
  rw [framePower, Fin.prod_univ_castSucc]
  simp [framePower]

private theorem pow_sub_pow_eq_mul_sub {q n k : ℕ} (hk : k ≤ n) :
    q ^ n - q ^ k = q ^ k * (q ^ (n - k) - 1) := by
  nth_rewrite 1 [show n = k + (n - k) by omega]
  rw [pow_add, Nat.mul_sub_left_distrib]
  simp

/-- Clearing the denominator in the ordered-frame product formula.
@isnad1 id=eq.1h3v.s5.3787ddd62f57 from=translated src=- shape=ff2d1b20 vocab=e560aacf
-/
theorem frameProd_mul_qFactorial {q n k : ℕ} (hk : k ≤ n) :
    frameProd q n k * qFactorial q (n - k) =
      framePower q k * qFactorial q n := by
  induction k with
  | zero => simp
  | succ k ih =>
      have hkn : k ≤ n := by omega
      have hsub : n - k = (n - (k + 1)) + 1 := by omega
      rw [frameProd_succ, pow_sub_pow_eq_mul_sub hkn, framePower_succ]
      calc
        frameProd q n k * (q ^ k * (q ^ (n - k) - 1)) *
              qFactorial q (n - (k + 1)) =
            q ^ k * (frameProd q n k *
              (qFactorial q (n - (k + 1)) * (q ^ (n - k) - 1))) := by ring
        _ = q ^ k * (frameProd q n k * qFactorial q (n - k)) := by
          rw [hsub, qFactorial_succ]
        _ = q ^ k * (framePower q k * qFactorial q n) := by rw [ih hkn]
        _ = framePower q k * q ^ k * qFactorial q n := by ring

/-- The ordered-frame form of the Gaussian product identity.
@isnad1 id=eq.2h3v.s5.571f61804b4c from=translated src=- shape=2065b08a vocab=feaa7492
-/
theorem qBinom_mul_frameProd {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    qBinom q n k * frameProd q k k = frameProd q n k := by
  have hmain := frameProd_mul_qFactorial (q := q) (n := n) hk
  have hdiag := frameProd_mul_qFactorial (q := q) (n := k) (le_refl k)
  have hqbin := qBinom_mul_qFactorials hq hk
  simp only [Nat.sub_self, qFactorial_zero, mul_one] at hdiag
  have hcancel : 0 < qFactorial q (n - k) := qFactorial_pos hq _
  apply Nat.eq_of_mul_eq_mul_right hcancel
  calc
    qBinom q n k * frameProd q k k * qFactorial q (n - k) =
        framePower q k *
          (qBinom q n k * qFactorial q k * qFactorial q (n - k)) := by
            rw [hdiag]
            ring
    _ = framePower q k * qFactorial q n := by rw [hqbin]
    _ = frameProd q n k * qFactorial q (n - k) := hmain.symm

/--
@isnad1 id=lt.2h3v.s5.07a0304634a3 from=translated src=- shape=2ab25192 vocab=adcafea6
-/
theorem frameProd_pos {q n k : ℕ} (hq : 2 ≤ q) (hk : k ≤ n) :
    0 < frameProd q n k := by
  rw [frameProd]
  apply Finset.prod_pos
  intro i hi
  have hik : i.val < k := i.isLt
  have hin : i.val < n := lt_of_lt_of_le hik hk
  exact Nat.sub_pos_of_lt (Nat.pow_lt_pow_right (by omega) hin)

/--
@isnad1 id=eq.1h3v.s6.de1e1ad8ced9 from=translated src=- shape=795b7c8e vocab=cc6683b4
-/
theorem card_linearIndependentFrames
    {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V]
    [Finite V] {k : ℕ} (hk : k ≤ Module.finrank K V) :
    Nat.card (LinearIndependentFrames K V k) =
      frameProd (Fintype.card K) (Module.finrank K V) k := by
  simpa [frameProd] using card_linearIndependent (K := K) (V := V) hk

/-- The exact number of ordered bases of the standard `r`-space over
`ZMod p`, expressed as the ordered-frame product.
@isnad1 id=eq.0h2v.s6.0e83ee07dfdc from=translated src=- shape=2c732c5b vocab=8096ac6c
-/
theorem card_orderedBases_fin_zmod (p r : ℕ) [Fact p.Prime] :
    Nat.card (LinearIndependentFrames (ZMod p) (Fin r → ZMod p) r) =
      frameProd p r r := by
  simpa using
    (card_linearIndependentFrames
      (K := ZMod p) (V := Fin r → ZMod p) (k := r) (by simp))

/-- Counting independent frames by their span.
@isnad1 id=eq.1h3v.s6.cef4985dcd2f from=translated src=- shape=4835e7f1 vocab=b2013690
-/
theorem card_finrankSubspaces_mul_frameProd
    {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V]
    [Finite V] {k : ℕ} (hk : k ≤ Module.finrank K V) :
    Nat.card (FinrankSubspaces K V k) * frameProd (Fintype.card K) k k =
      frameProd (Fintype.card K) (Module.finrank K V) k := by
  letI : Fintype (FinrankSubspaces K V k) := Fintype.ofFinite _
  calc
    Nat.card (FinrankSubspaces K V k) * frameProd (Fintype.card K) k k =
        ∑ W : FinrankSubspaces K V k, frameProd (Fintype.card K) k k := by
          rw [Finset.sum_const, nsmul_eq_mul]
          simp [Nat.card_eq_fintype_card]
    _ = ∑ W : FinrankSubspaces K V k,
          Nat.card (LinearIndependentFrames K W.1 k) := by
        apply Finset.sum_congr rfl
        intro W hW
        symm
        simpa [W.2] using
          (card_linearIndependentFrames (K := K) (V := W.1) (k := k)
            (by simp [W.2]))
    _ = Nat.card (Σ W : FinrankSubspaces K V k,
          LinearIndependentFrames K W.1 k) := Nat.card_sigma.symm
    _ = Nat.card (LinearIndependentFrames K V k) :=
      Nat.card_congr (linearIndependentFramesEquiv K V k).symm
    _ = frameProd (Fintype.card K) (Module.finrank K V) k :=
      card_linearIndependentFrames hk

/-- The Gaussian coefficient counts subspaces of a fixed dimension over any
finite division ring.
@isnad1 id=eq.1h3v.s6.0c8354870a2b from=translated src=- shape=795b7c8e vocab=665c4553
-/
theorem card_finrankSubspaces_eq_qBinom
    {K V : Type*} [DivisionRing K] [Fintype K] [AddCommGroup V] [Module K V]
    [Finite V] {k : ℕ} (hk : k ≤ Module.finrank K V) :
    Nat.card (FinrankSubspaces K V k) =
      qBinom (Fintype.card K) (Module.finrank K V) k := by
  have hq : 2 ≤ Fintype.card K := Fintype.one_lt_card
  have hpos : 0 < frameProd (Fintype.card K) k k := frameProd_pos hq le_rfl
  apply Nat.eq_of_mul_eq_mul_right hpos
  calc
    Nat.card (FinrankSubspaces K V k) * frameProd (Fintype.card K) k k =
        frameProd (Fintype.card K) (Module.finrank K V) k :=
      card_finrankSubspaces_mul_frameProd hk
    _ = qBinom (Fintype.card K) (Module.finrank K V) k *
        frameProd (Fintype.card K) k k := (qBinom_mul_frameProd hq hk).symm

/-- Exact Gaussian count for subspaces of the standard `n`-space over
`ZMod p`.
@isnad1 id=eq.1h3v.s9.b498fde13a57 from=translated src=- shape=ce776650 vocab=3446ba7d
-/
theorem card_subspaces_fin_zmod (p n k : ℕ) [Fact p.Prime] (hk : k ≤ n) :
    Nat.card {W : Submodule (ZMod p) (Fin n → ZMod p) //
      Module.finrank (ZMod p) W = k} = qBinom p n k := by
  simpa using
    (card_finrankSubspaces_eq_qBinom
      (K := ZMod p) (V := Fin n → ZMod p) (k := k) (by simpa using hk))

/-- A subspace together with its dimension, bounded by the ambient
dimension.-/
noncomputable def submoduleEquivSigmaFinrank
    (K V : Type*) [DivisionRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] :
    Submodule K V ≃
      Σ k : Fin (Module.finrank K V + 1), FinrankSubspaces K V k.val where
  toFun W := ⟨⟨Module.finrank K W, Nat.lt_succ_of_le W.finrank_le⟩, ⟨W, rfl⟩⟩
  invFun x := x.2.1
  left_inv _ := rfl
  right_inv x := by
    rcases x with ⟨k, W⟩
    rcases W with ⟨W, hW⟩
    have hk : (⟨Module.finrank K W, Nat.lt_succ_of_le W.finrank_le⟩ :
        Fin (Module.finrank K V + 1)) = k := Fin.ext hW
    cases hk
    rfl

/-- The total Gaussian sum.-/
def totalQBinom (q n : ℕ) : ℕ :=
  ∑ k : Fin (n + 1), qBinom q n k.val

/-- Pairing dimensions equidistant from the middle in even rank.
@isnad1 id=eq.1h2v.s6.6e36cbbc6c59 from=translated src=- shape=50c24373 vocab=dfc8fd8b
-/
theorem totalQBinom_even_split {q : ℕ} (hq : 2 ≤ q) (a : ℕ) :
    totalQBinom q (2 * a) = qBinom q (2 * a) a +
      2 * ∑ j ∈ Finset.range a, qBinom q (2 * a) (a + (j + 1)) := by
  let f : ℕ → ℕ := fun k ↦ qBinom q (2 * a) k
  have hlow : (∑ j ∈ Finset.range a, f j) =
      ∑ j ∈ Finset.range a, f (a + (j + 1)) := by
    calc
      (∑ j ∈ Finset.range a, f j) =
          ∑ j ∈ Finset.range a, f (a - 1 - j) :=
        (Finset.sum_range_reflect f a).symm
      _ = ∑ j ∈ Finset.range a, f (a + (j + 1)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hja : j < a := Finset.mem_range.mp hj
        dsimp [f]
        rw [qBinom_symm hq (by omega : a - 1 - j ≤ 2 * a)]
        congr 1
        omega
  rw [totalQBinom, Fin.sum_univ_eq_sum_range]
  have hsize : 2 * a + 1 = (a + 1) + a := by omega
  rw [hsize, Finset.sum_range_add, Finset.sum_range_succ, hlow]
  dsimp [f]
  simp only [Nat.add_assoc]
  ring

/-- Exact count of all subspaces of the standard space over `ZMod p`.
@isnad1 id=eq.0h2v.s6.c443fecb4d00 from=translated src=- shape=09ebe6bc vocab=540dedfa
-/
theorem card_all_subspaces_fin_zmod (p n : ℕ) [Fact p.Prime] :
    Nat.card (Submodule (ZMod p) (Fin n → ZMod p)) = totalQBinom p n := by
  rw [Nat.card_congr (submoduleEquivSigmaFinrank (ZMod p) (Fin n → ZMod p)),
    Nat.card_sigma]
  have hfin : Module.finrank (ZMod p) (Fin n → ZMod p) = n := by simp
  rw [hfin]
  have hsum :
      (∑ k : Fin (n + 1), Nat.card (FinrankSubspaces (ZMod p) (Fin n → ZMod p) k.val)) =
        ∑ k : Fin (n + 1), qBinom p n k.val := by
    apply Fintype.sum_congr
    intro k
    exact card_subspaces_fin_zmod p n k.val (by omega)
  simpa only [totalQBinom] using hsum

end SharpIntermediateSubgroupBounds
