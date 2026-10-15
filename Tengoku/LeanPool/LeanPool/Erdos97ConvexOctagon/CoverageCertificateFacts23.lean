/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 23).
@isnad1 id=eq.0h0v.s5.07ea992b0cc8 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_23 :
    branchClaimRootValidB 0 23 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 21).
@isnad1 id=eq.0h0v.s5.548eb25397ef from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_21 :
    branchClaimRootValidB 5 21 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 27).
@isnad1 id=eq.0h0v.s5.701374f515c0 from=translated src=- shape=e9e0773c vocab=a48c8b5f
-/
theorem coverageBranchRoot_2_27 :
    branchClaimRootValidB 2 27 (.search branchClaims2Row27) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 28).
@isnad1 id=eq.0h0v.s5.dced7e97f69a from=translated src=- shape=e9e0773c vocab=fc405ffb
-/
theorem coverageBranchRoot_2_28 :
    branchClaimRootValidB 2 28 (.search branchClaims2Row28) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 26), starting at 64.
@isnad1 id=eq.0h0v.s3.0650af85aedc from=translated src=- shape=6f582f20 vocab=4af5a85f
-/
theorem coverageBranchNodes_2_26_00064 :
    nodeClaimChunkValidB branchClaims2Row26 64 34 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 27), starting at 0.
@isnad1 id=eq.0h0v.s3.9c267057b9d0 from=translated src=- shape=6f582f20 vocab=04c4bccb
-/
theorem coverageBranchNodes_2_27_00000 :
    nodeClaimChunkValidB branchClaims2Row27 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 27), starting at 64.
@isnad1 id=eq.0h0v.s3.27ff73f2acda from=translated src=- shape=6f582f20 vocab=04c4bccb
-/
theorem coverageBranchNodes_2_27_00064 :
    nodeClaimChunkValidB branchClaims2Row27 64 26 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 28), starting at 0.
@isnad1 id=eq.0h0v.s3.8d83c8991a6f from=translated src=- shape=6f582f20 vocab=7368fc0c
-/
theorem coverageBranchNodes_2_28_00000 :
    nodeClaimChunkValidB branchClaims2Row28 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
