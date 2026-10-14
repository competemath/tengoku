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

/-- Root audit for fixed branch (0, 2).
@isnad1 id=eq.0h0v.s5.283f0c2a79ca from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_02 :
    branchClaimRootValidB 0 2 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 20).
@isnad1 id=eq.0h0v.s5.2b995bde3812 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_20 :
    branchClaimRootValidB 4 20 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 8).
@isnad1 id=eq.0h0v.s5.48333341c913 from=translated src=- shape=e9e0773c vocab=4c88d311
-/
theorem coverageBranchRoot_1_08 :
    branchClaimRootValidB 1 8 (.search branchClaims1Row8) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 9).
@isnad1 id=eq.0h0v.s5.e28c361a1194 from=translated src=- shape=e9e0773c vocab=eb900cdb
-/
theorem coverageBranchRoot_1_09 :
    branchClaimRootValidB 1 9 (.search branchClaims1Row9) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 8), starting at 0.
@isnad1 id=eq.0h0v.s3.5b5843c37ba9 from=translated src=- shape=6f582f20 vocab=b891e789
-/
theorem coverageBranchNodes_1_08_00000 :
    nodeClaimChunkValidB branchClaims1Row8 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 8), starting at 64.
@isnad1 id=eq.0h0v.s3.3502b7e34def from=translated src=- shape=6f582f20 vocab=b891e789
-/
theorem coverageBranchNodes_1_08_00064 :
    nodeClaimChunkValidB branchClaims1Row8 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 8), starting at 128.
@isnad1 id=eq.0h0v.s3.13406f43ca3e from=translated src=- shape=6f582f20 vocab=b891e789
-/
theorem coverageBranchNodes_1_08_00128 :
    nodeClaimChunkValidB branchClaims1Row8 128 18 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 9), starting at 0.
@isnad1 id=eq.0h0v.s3.6e0d12f87286 from=translated src=- shape=6f582f20 vocab=01544a0d
-/
theorem coverageBranchNodes_1_09_00000 :
    nodeClaimChunkValidB branchClaims1Row9 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
