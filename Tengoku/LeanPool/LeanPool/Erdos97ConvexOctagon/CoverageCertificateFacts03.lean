/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData00
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 3).
@isnad1 id=eq.0h0v.s5.22e7d882d2c9 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_03 :
    branchClaimRootValidB 0 3 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 21).
@isnad1 id=eq.0h0v.s5.facd9332dcf5 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_21 :
    branchClaimRootValidB 4 21 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 16).
@isnad1 id=eq.0h0v.s5.bd02d18b0d7c from=translated src=- shape=e9e0773c vocab=4b57976f
-/
theorem coverageBranchRoot_1_16 :
    branchClaimRootValidB 1 16 (.search branchClaims1Row16) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 9), starting at 64.
@isnad1 id=eq.0h0v.s3.c092d41d18b6 from=translated src=- shape=6f582f20 vocab=01544a0d
-/
theorem coverageBranchNodes_1_09_00064 :
    nodeClaimChunkValidB branchClaims1Row9 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 9), starting at 128.
@isnad1 id=eq.0h0v.s3.5af7e3ca61d6 from=translated src=- shape=6f582f20 vocab=01544a0d
-/
theorem coverageBranchNodes_1_09_00128 :
    nodeClaimChunkValidB branchClaims1Row9 128 16 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 16), starting at 0.
@isnad1 id=eq.0h0v.s3.74c1c7ee3bcd from=translated src=- shape=6f582f20 vocab=0329daff
-/
theorem coverageBranchNodes_1_16_00000 :
    nodeClaimChunkValidB branchClaims1Row16 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 16), starting at 64.
@isnad1 id=eq.0h0v.s3.9c4ec7f03fb2 from=translated src=- shape=6f582f20 vocab=0329daff
-/
theorem coverageBranchNodes_1_16_00064 :
    nodeClaimChunkValidB branchClaims1Row16 64 28 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
