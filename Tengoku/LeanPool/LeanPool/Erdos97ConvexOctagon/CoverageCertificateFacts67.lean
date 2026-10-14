/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 17).
@isnad1 id=eq.0h0v.s5.14996dd1f591 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_17 :
    branchClaimRootValidB 3 17 (.patternThree 4) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 31).
@isnad1 id=eq.0h0v.s5.d62b55fb01c5 from=translated src=- shape=e9e0773c vocab=7b81936a
-/
theorem coverageBranchRoot_5_31 :
    branchClaimRootValidB 5 31 (.search branchClaims5Row31) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 29), starting at 192.
@isnad1 id=eq.0h0v.s3.c3a780ddd7f6 from=translated src=- shape=6f582f20 vocab=a1dc1839
-/
theorem coverageBranchNodes_5_29_00192 :
    nodeClaimChunkValidB branchClaims5Row29 192 57 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 31), starting at 0.
@isnad1 id=eq.0h0v.s3.da9e6b966ba7 from=translated src=- shape=6f582f20 vocab=677a6d2a
-/
theorem coverageBranchNodes_5_31_00000 :
    nodeClaimChunkValidB branchClaims5Row31 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 31), starting at 64.
@isnad1 id=eq.0h0v.s3.8202b5c10758 from=translated src=- shape=6f582f20 vocab=677a6d2a
-/
theorem coverageBranchNodes_5_31_00064 :
    nodeClaimChunkValidB branchClaims5Row31 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 31), starting at 128.
@isnad1 id=eq.0h0v.s3.1c08bf74aa49 from=translated src=- shape=6f582f20 vocab=677a6d2a
-/
theorem coverageBranchNodes_5_31_00128 :
    nodeClaimChunkValidB branchClaims5Row31 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
