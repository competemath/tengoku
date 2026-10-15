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

/-- Root audit for fixed branch (3, 19).
@isnad1 id=eq.0h0v.s5.51d831c0139e from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_19 :
    branchClaimRootValidB 3 19 (.patternThree 2) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 32).
@isnad1 id=eq.0h0v.s5.37d414170ec5 from=translated src=- shape=e9e0773c vocab=c620ff69
-/
theorem coverageBranchRoot_5_32 :
    branchClaimRootValidB 5 32 (.search branchClaims5Row32) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 31), starting at 384.
@isnad1 id=eq.0h0v.s3.397c05f15bcb from=translated src=- shape=6f582f20 vocab=677a6d2a
-/
theorem coverageBranchNodes_5_31_00384 :
    nodeClaimChunkValidB branchClaims5Row31 384 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 31), starting at 448.
@isnad1 id=eq.0h0v.s3.848f4a88c507 from=translated src=- shape=6f582f20 vocab=677a6d2a
-/
theorem coverageBranchNodes_5_31_00448 :
    nodeClaimChunkValidB branchClaims5Row31 448 38 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 0.
@isnad1 id=eq.0h0v.s3.6586f421314f from=translated src=- shape=6f582f20 vocab=e3f0be63
-/
theorem coverageBranchNodes_5_32_00000 :
    nodeClaimChunkValidB branchClaims5Row32 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 64.
@isnad1 id=eq.0h0v.s3.50b3b1f1fd9d from=translated src=- shape=6f582f20 vocab=e3f0be63
-/
theorem coverageBranchNodes_5_32_00064 :
    nodeClaimChunkValidB branchClaims5Row32 64 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
