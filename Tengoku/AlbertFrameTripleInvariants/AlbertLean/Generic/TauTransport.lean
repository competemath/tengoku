import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.SecondStatement
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Compact.Solution
import Tengoku.AlbertFrameTripleInvariants.AlbertLean.Generic.FrameTransport

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# Transport from public coordinates to the Tau Ceti statement surface

The completed compact identification is repackaged as one linear equivalence.
All public objects are then transported structurally: products, projectors,
frames, ledgers, detectors, and the full automorphism relation.  Only the
three-entry diagonal trace is read explicitly; no matrix-family coordinate
calculation occurs here.
-/

noncomputable section

namespace AlbertLean.Generic.TauTransport

local instance : Invertible (2 : ℚ) := invertibleOfNonzero (by decide)

/-- Copy the four public ledger tables without changing their index order.-/
def ledgerCopy (L : AlbertLean.Ledger) : SecondStatement.Ledger :=
  ⟨L.P, L.Q, L.R, L.C0⟩

/-- Copying the public tables to the statement ledger loses no information.
@isnad1 id=injectiv.0h0v.s2.8d6e8f0bd09b from=translated src=- shape=54c8eceb vocab=cf8178b2
-/
theorem ledgerCopy_injective : Function.Injective ledgerCopy := by
  rintro ⟨P, Q, R, C0⟩ ⟨P', Q', R', C0'⟩ h
  simp only [ledgerCopy, SecondStatement.Ledger.mk.injEq] at h
  rw [AlbertLean.Ledger.mk.injEq]
  exact h

end AlbertLean.Generic.TauTransport
