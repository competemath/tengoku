/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData05
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 34).
@isnad1 id=eq.0h0v.s5.6183f14b047c from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_34 :
    branchClaimRootValidB 0 34 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 33).
@isnad1 id=eq.0h0v.s5.088a807b1ad5 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_6_33 :
    branchClaimRootValidB 6 33 (.patternThree 6) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 23).
@isnad1 id=eq.0h0v.s5.5a7ae2ceb5cc from=translated src=- shape=e9e0773c vocab=38b78fd0
-/
theorem coverageBranchRoot_3_23 :
    branchClaimRootValidB 3 23 (.search branchClaims3Row23) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 23), starting at 0.
@isnad1 id=eq.0h0v.s3.662bf5825d9f from=translated src=- shape=6f582f20 vocab=8d09d39a
-/
theorem coverageBranchNodes_3_23_00000 :
    nodeClaimChunkValidB branchClaims3Row23 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 23), starting at 64.
@isnad1 id=eq.0h0v.s3.a95d6054f003 from=translated src=- shape=6f582f20 vocab=8d09d39a
-/
theorem coverageBranchNodes_3_23_00064 :
    nodeClaimChunkValidB branchClaims3Row23 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 23), starting at 128.
@isnad1 id=eq.0h0v.s3.d5282ade1a11 from=translated src=- shape=6f582f20 vocab=8d09d39a
-/
theorem coverageBranchNodes_3_23_00128 :
    nodeClaimChunkValidB branchClaims3Row23 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 23), starting at 192.
@isnad1 id=eq.0h0v.s3.496ab2d61722 from=translated src=- shape=6f582f20 vocab=8d09d39a
-/
theorem coverageBranchNodes_3_23_00192 :
    nodeClaimChunkValidB branchClaims3Row23 192 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
