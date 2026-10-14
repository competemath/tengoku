/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 12).
@isnad1 id=eq.0h0v.s5.3bc9c82122f5 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_12 :
    branchClaimRootValidB 1 12 (.patternThree 178) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 28).
@isnad1 id=eq.0h0v.s5.e2b0bf007d97 from=translated src=- shape=e9e0773c vocab=8a8e1a2a
-/
theorem coverageBranchRoot_3_28 :
    branchClaimRootValidB 3 28 (.search branchClaims3Row28) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 27), starting at 320.
@isnad1 id=eq.0h0v.s3.bcbf5900d81e from=translated src=- shape=6f582f20 vocab=3299c20b
-/
theorem coverageBranchNodes_3_27_00320 :
    nodeClaimChunkValidB branchClaims3Row27 320 25 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 28), starting at 0.
@isnad1 id=eq.0h0v.s3.d35b47921da1 from=translated src=- shape=6f582f20 vocab=6a248f59
-/
theorem coverageBranchNodes_3_28_00000 :
    nodeClaimChunkValidB branchClaims3Row28 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 28), starting at 64.
@isnad1 id=eq.0h0v.s3.c9b3e4ff526d from=translated src=- shape=6f582f20 vocab=6a248f59
-/
theorem coverageBranchNodes_3_28_00064 :
    nodeClaimChunkValidB branchClaims3Row28 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 28), starting at 128.
@isnad1 id=eq.0h0v.s3.990ab09502da from=translated src=- shape=6f582f20 vocab=6a248f59
-/
theorem coverageBranchNodes_3_28_00128 :
    nodeClaimChunkValidB branchClaims3Row28 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
