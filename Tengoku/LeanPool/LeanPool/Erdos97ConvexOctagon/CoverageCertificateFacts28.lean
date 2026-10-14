/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 28).
@isnad1 id=eq.0h0v.s5.d1140cab1ddb from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_28 :
    branchClaimRootValidB 0 28 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 0).
@isnad1 id=eq.0h0v.s5.6ed43c2fcf36 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_6_00 :
    branchClaimRootValidB 6 0 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 34).
@isnad1 id=eq.0h0v.s5.33dce7e9c350 from=translated src=- shape=e9e0773c vocab=59e1b509
-/
theorem coverageBranchRoot_2_34 :
    branchClaimRootValidB 2 34 (.search branchClaims2Row34) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 33), starting at 64.
@isnad1 id=eq.0h0v.s3.abdf9e87525c from=translated src=- shape=6f582f20 vocab=f45cb2fb
-/
theorem coverageBranchNodes_2_33_00064 :
    nodeClaimChunkValidB branchClaims2Row33 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 33), starting at 128.
@isnad1 id=eq.0h0v.s3.70b466fe09eb from=translated src=- shape=6f582f20 vocab=f45cb2fb
-/
theorem coverageBranchNodes_2_33_00128 :
    nodeClaimChunkValidB branchClaims2Row33 128 38 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 34), starting at 0.
@isnad1 id=eq.0h0v.s3.8dfb19587d5d from=translated src=- shape=6f582f20 vocab=f7cc570d
-/
theorem coverageBranchNodes_2_34_00000 :
    nodeClaimChunkValidB branchClaims2Row34 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 34), starting at 64.
@isnad1 id=eq.0h0v.s3.4b67d3cd673e from=translated src=- shape=6f582f20 vocab=f7cc570d
-/
theorem coverageBranchNodes_2_34_00064 :
    nodeClaimChunkValidB branchClaims2Row34 64 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
