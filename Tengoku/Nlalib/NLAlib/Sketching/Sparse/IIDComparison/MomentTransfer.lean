/- Copyright (c) 2026 Diar Heidary.
Ported to NLAlib from commit b9da2b5d96e5fd70252e9c6551aefc92643e7d0b.
Released under the MIT license; see docs/ports/sparse-fock-MIT.txt. -/
import Tengoku.Nlalib.NLAlib.Sketching.Sparse.IIDComparison.DistributionBridges
import Tengoku.Nlalib.NLAlib.Matrix.Functions.TracePowerConvexity
import Tengoku.Seed.Tactic

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Exact trace-moment transfer identities

This file contains the algebraic and distributional equalities needed to pass
from the finite sparse-selector model to the iid product-Fock model.  It does
not assume the analytic moment estimate.
-/

namespace NLAlib.SparseSketch

open SparseStackSelectors

open scoped InnerProductSpace Matrix

noncomputable section

variable {s b n d : ℕ}

/-- Scaling both iid vectors by `c_b` scales the `2q`-trace moment by
`c_b^(4q)`.

Source: ported from `SparseFockFormal.MomentTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.0h7v.s7.729965169a83 from=translated src=- shape=1caad8d7 vocab=1125447f
-/
theorem scaledIIDVectorError_trace_even (F : Frame n d)
    (y : YArray b s n) (q : ℕ) :
    ((scaledIIDVectorError F y) ^ (2 * q)).trace =
      cB b ^ (4 * q) * ((iidVectorError F y) ^ (2 * q)).trace := by
  rw [scaledIIDVectorError_eq_smul, smul_pow, Matrix.trace_smul, smul_eq_mul]
  congr 1
  rw [← pow_mul]
  congr 1
  omega

/-- The sparse-selector trace moment is literally the raw SparseStack trace
moment under the identical finite law.

Source: ported from `SparseFockFormal.MomentTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.2h6v.s8.ef7248696de5 from=translated src=- shape=b6e1134c vocab=1b510f90
-/
theorem selector_trace_moment_eq_raw (hs : 0 < s) (hb : 0 < b)
    (F : Frame n d) (q : ℕ) :
    (selectorArrayLaw hb s n).expect
        (fun x ↦ ((sparseVectorError F x) ^ (2 * q)).trace) =
      (sparseStackSelectorLaw s b n hb).expect
        (fun ω ↦ ((gramError F (sparseStackMatrix (toSample ω))) ^ (2 * q)).trace) := by
  rw [selectorArrayLaw_eq_rawSampleLaw]
  apply (sparseStackSelectorLaw s b n hb).expect_congr
  intro x
  rw [sparseVectorError_eq_gramError hs]

/-- The unscaled iid-vector trace moment is exactly the product-Fock trace
moment after the proved finite-coordinate flattening.

Source: ported from `SparseFockFormal.MomentTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.2h6v.s8.63448368c8bc from=translated src=- shape=474889a7 vocab=08dca12d
-/
theorem iid_trace_moment_eq_product (hs : 0 < s) (hb : 1 < b)
    (F : Frame n d) (q : ℕ) :
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun y ↦ ((iidVectorError F y) ^ (2 * q)).trace) =
      (iidLaw b hb (s * b) n).expect
        (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace) := by
  calc
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun y ↦ ((iidVectorError F y) ^ (2 * q)).trace) =
        (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun y ↦ ((iidGramError b F (flattenY y)) ^ (2 * q)).trace) := by
      apply (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect_congr
      intro y
      rw [iidVectorError_eq_flattened_iidGramError hs hb]
    _ = (iidLaw b hb (s * b) n).expect
        (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace) :=
      iidArrayLaw_expect_flatten_eq_iidLaw_expect
        (s := s) (n := n) hb
        (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace)

/-- Full algebraic factor in the iid side of the convex-order transfer.

Source: ported from `SparseFockFormal.MomentTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=eq.2h6v.s8.a9647ef13ed3 from=translated src=- shape=f3eafca2 vocab=b4af4cbc
-/
theorem scaled_iid_trace_moment_eq_product (hs : 0 < s) (hb : 1 < b)
    (F : Frame n d) (q : ℕ) :
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun y ↦ ((scaledIIDVectorError F y) ^ (2 * q)).trace) =
      cB b ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace) := by
  calc
    (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
        (fun y ↦ ((scaledIIDVectorError F y) ^ (2 * q)).trace) =
        (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun y ↦ cB b ^ (4 * q) *
            ((iidVectorError F y) ^ (2 * q)).trace) := by
      apply (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect_congr
      intro y
      exact scaledIIDVectorError_trace_even F y q
    _ = cB b ^ (4 * q) *
        (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun y ↦ ((iidVectorError F y) ^ (2 * q)).trace) := by
      exact FiniteLaw.expect_smul _ _ _
    _ = cB b ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun ω ↦ ((iidGramError b F ω) ^ (2 * q)).trace) := by
      rw [iid_trace_moment_eq_product hs hb F q]

/-- The proved convexity of the even trace power instantiates the full
unconditional sparse--iid convex order.

Source: ported from `SparseFockFormal.MomentTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h6v.s8.8683c173aa74 from=translated src=- shape=5afb38d7 vocab=03ecc2e0
-/
theorem unconditional_trace_moment_order (hb : 0 < b)
    (F : Frame n d) (q : ℕ) :
    (selectorArrayLaw hb s n).expect
        (fun x ↦ ((sparseVectorError F x) ^ (2 * q)).trace) ≤
      (iidArrayLaw hb s n).expect
        (fun y ↦ ((scaledIIDVectorError F y) ^ (2 * q)).trace) := by
  simpa [traceEvenPower, sparseSymmetricError,
    scaledIIDSymmetricError] using
      (unconditional_convex_order hb F
        (traceEvenPower (d := d) q)
        (convexOn_traceEvenPower d q))

/-- Exact distribution-level convex-moment bridge from the literal raw
SparseStack law to the product-Fock iid law.

Source: ported from `SparseFockFormal.MomentTransfer`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.2h6v.s8.d6af837253cb from=translated src=- shape=b869ddf0 vocab=65df5f81
-/
theorem raw_trace_moment_le_scaled_product (hs : 0 < s) (hb : 1 < b)
    (F : Frame n d) (q : ℕ) :
    (sparseStackSelectorLaw s b n (lt_trans Nat.zero_lt_one hb)).expect
        (fun z ↦ ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) ≤
      cB b ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun omega ↦ ((iidGramError b F omega) ^ (2 * q)).trace) := by
  calc
    (sparseStackSelectorLaw s b n (lt_trans Nat.zero_lt_one hb)).expect
        (fun z ↦ ((gramError F (sparseStackMatrix (toSample z))) ^ (2 * q)).trace) =
        (selectorArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun x ↦ ((sparseVectorError F x) ^ (2 * q)).trace) :=
      (selector_trace_moment_eq_raw hs (lt_trans Nat.zero_lt_one hb) F q).symm
    _ ≤ (iidArrayLaw (lt_trans Nat.zero_lt_one hb) s n).expect
          (fun y ↦ ((scaledIIDVectorError F y) ^ (2 * q)).trace) :=
      unconditional_trace_moment_order (lt_trans Nat.zero_lt_one hb) F q
    _ = cB b ^ (4 * q) *
        (iidLaw b hb (s * b) n).expect
          (fun omega ↦ ((iidGramError b F omega) ^ (2 * q)).trace) :=
      scaled_iid_trace_moment_eq_product hs hb F q

/-- The exact trace-moment comparison needed after the sparse--iid
conditional barycenter identity.

Source: ported from `SparseFockFormal.TracePowerConvexity.conditional_traceEvenPower_order`,
b9da2b5d96e5fd70252e9c6551aefc92643e7d0b; supports `sparse-ose`.
@isnad1 id=le.1h7v.s6.6b37de2ccc8b from=translated src=- shape=5004e75f vocab=59ed3c10
-/
theorem conditional_traceEvenPower_order {b s n d : ℕ} (hb : 0 < b)
    (F : Frame n d) (x : XArray b s n) (q : ℕ) :
    traceEvenPower q (sparseSymmetricError F x) ≤
      (conditionalArrayLaw hb x).expect
        (fun y ↦ traceEvenPower q (scaledIIDSymmetricError F y)) := by
  exact conditional_convex_order hb F x
    (traceEvenPower q) (convexOn_traceEvenPower d q)

end

end NLAlib.SparseSketch
