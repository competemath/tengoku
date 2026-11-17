import Tengoku.TunnellTwoToOneMap.TunnellMap.AffineLattice

/-! Tengoku: the imports are the original's, in the tree's names (the umbrella `Tengoku` made names ambiguous). -/

/-!
# The index-two lattice of the `tau` embedding

This file proves equation (5.1): the image of `tau` consists exactly of
triples whose first and third coordinates have the same parity, with the
displayed division-by-two inverse.
-/

namespace TunnellMap

def InTauLattice (r : Triple) : Prop := (2 : ℤ) ∣ r.x - r.z

instance inTauLatticeDecidable (r : Triple) : Decidable (InTauLattice r) := by
  unfold InTauLattice
  infer_instance

def tauInv (r : Triple) : Triple :=
  ⟨(r.x + r.z) / 2, r.y, (r.x - r.z) / 2⟩

/--
@isnad1 id=intaulat.0h1v.s2.56b67da88601 from=translated src=- shape=76a08d12 vocab=4165529e
-/
theorem tau_mem (d : Triple) : InTauLattice (tau d) := by
  refine ⟨d.z, ?_⟩
  simp [InTauLattice, tau]
  ring

/--
@isnad1 id=eq.0h1v.s3.a44fad54f97a from=translated src=- shape=47dcad53 vocab=464bc62e
-/
@[simp] theorem tauInv_tau (d : Triple) : tauInv (tau d) = d := by
  apply Triple.ext
  · simp only [tauInv, tau]
    rw [show (d.x + d.z + (d.x - d.z)) = 2 * d.x by ring]
    exact Int.mul_ediv_cancel_left d.x (by norm_num)
  · rfl
  · simp only [tauInv, tau]
    rw [show (d.x + d.z - (d.x - d.z)) = 2 * d.z by ring]
    exact Int.mul_ediv_cancel_left d.z (by norm_num)

/--
@isnad1 id=eq.1h1v.s3.5c36f00f8323 from=translated src=- shape=f9d42bb4 vocab=21a09c93
-/
theorem tau_tauInv {r : Triple} (hr : InTauLattice r) : tau (tauInv r) = r := by
  have hdiff : (2 : ℤ) ∣ r.x - r.z := hr
  have hsum : (2 : ℤ) ∣ r.x + r.z := by
    obtain ⟨k, hk⟩ := hdiff
    refine ⟨k + r.z, ?_⟩
    linarith
  have hdiffDiv : 2 * ((r.x - r.z) / 2) = r.x - r.z := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hdiff
  have hsumDiv : 2 * ((r.x + r.z) / 2) = r.x + r.z := by
    rw [mul_comm]
    exact Int.ediv_mul_cancel hsum
  apply Triple.ext
  · simp only [tau, tauInv]
    omega
  · rfl
  · simp only [tau, tauInv]
    omega

def tauEquiv : Triple ≃ {r : Triple // InTauLattice r} where
  toFun d := ⟨tau d, tau_mem d⟩
  invFun r := tauInv r.1
  left_inv := tauInv_tau
  right_inv := by
    intro r
    apply Subtype.ext
    exact tau_tauInv r.2

/--
@isnad1 id=injectiv.0h0v.s2.217b67d19d4a from=translated src=- shape=e3d48bcb vocab=48342373
-/
theorem tau_injective : Function.Injective tau := by
  intro d e h
  simpa using congrArg tauInv h

end TunnellMap
