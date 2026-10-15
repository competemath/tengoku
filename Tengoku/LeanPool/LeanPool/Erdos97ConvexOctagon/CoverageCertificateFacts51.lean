/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData08
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (2, 0).
@isnad1 id=eq.0h0v.s5.bb7e7225df1f from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_2_00 :
    branchClaimRootValidB 2 0 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 14).
@isnad1 id=eq.0h0v.s5.a06e3440c487 from=translated src=- shape=e9e0773c vocab=7b70b77c
-/
theorem coverageBranchRoot_5_14 :
    branchClaimRootValidB 5 14 (.search branchClaims5Row14) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 12), starting at 64.
@isnad1 id=eq.0h0v.s3.fa8ae59888c8 from=translated src=- shape=6f582f20 vocab=8ccb4304
-/
theorem coverageBranchNodes_5_12_00064 :
    nodeClaimChunkValidB branchClaims5Row12 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 12), starting at 128.
@isnad1 id=eq.0h0v.s3.70bd3b9f8c68 from=translated src=- shape=6f582f20 vocab=8ccb4304
-/
theorem coverageBranchNodes_5_12_00128 :
    nodeClaimChunkValidB branchClaims5Row12 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 12), starting at 192.
@isnad1 id=eq.0h0v.s3.ed0b1e78c66f from=translated src=- shape=6f582f20 vocab=8ccb4304
-/
theorem coverageBranchNodes_5_12_00192 :
    nodeClaimChunkValidB branchClaims5Row12 192 10 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 14), starting at 0.
@isnad1 id=eq.0h0v.s3.2307dc038bd1 from=translated src=- shape=6f582f20 vocab=89a7448e
-/
theorem coverageBranchNodes_5_14_00000 :
    nodeClaimChunkValidB branchClaims5Row14 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
