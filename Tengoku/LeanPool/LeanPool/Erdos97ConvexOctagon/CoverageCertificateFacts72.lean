/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 22).
@isnad1 id=eq.0h0v.s5.be5b1c664523 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_22 :
    branchClaimRootValidB 3 22 (.patternThree 1) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 34), starting at 64.
@isnad1 id=eq.0h0v.s3.a0b513556187 from=translated src=- shape=6f582f20 vocab=fbc3c659
-/
theorem coverageBranchNodes_5_34_00064 :
    nodeClaimChunkValidB branchClaims5Row34 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 34), starting at 128.
@isnad1 id=eq.0h0v.s3.e83d7ec0b8ec from=translated src=- shape=6f582f20 vocab=fbc3c659
-/
theorem coverageBranchNodes_5_34_00128 :
    nodeClaimChunkValidB branchClaims5Row34 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 34), starting at 192.
@isnad1 id=eq.0h0v.s3.235f5b9a06da from=translated src=- shape=6f582f20 vocab=fbc3c659
-/
theorem coverageBranchNodes_5_34_00192 :
    nodeClaimChunkValidB branchClaims5Row34 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 34), starting at 256.
@isnad1 id=eq.0h0v.s3.2cfc515673b9 from=translated src=- shape=6f582f20 vocab=fbc3c659
-/
theorem coverageBranchNodes_5_34_00256 :
    nodeClaimChunkValidB branchClaims5Row34 256 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
