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

/-- Root audit for fixed branch (1, 25).
@isnad1 id=eq.0h0v.s5.8da547db966d from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_25 :
    branchClaimRootValidB 1 25 (.patternThree 179) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 11).
@isnad1 id=eq.0h0v.s5.232f085da552 from=translated src=- shape=e9e0773c vocab=8a790cc9
-/
theorem coverageBranchRoot_5_11 :
    branchClaimRootValidB 5 11 (.search branchClaims5Row11) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 12).
@isnad1 id=eq.0h0v.s5.ccb20fcc8db3 from=translated src=- shape=e9e0773c vocab=9758f90b
-/
theorem coverageBranchRoot_5_12 :
    branchClaimRootValidB 5 12 (.search branchClaims5Row12) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 11), starting at 0.
@isnad1 id=eq.0h0v.s3.ef066939b6cf from=translated src=- shape=6f582f20 vocab=8704c06c
-/
theorem coverageBranchNodes_5_11_00000 :
    nodeClaimChunkValidB branchClaims5Row11 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 11), starting at 64.
@isnad1 id=eq.0h0v.s3.fba95b1b6c20 from=translated src=- shape=6f582f20 vocab=8704c06c
-/
theorem coverageBranchNodes_5_11_00064 :
    nodeClaimChunkValidB branchClaims5Row11 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 11), starting at 128.
@isnad1 id=eq.0h0v.s3.402480514530 from=translated src=- shape=6f582f20 vocab=8704c06c
-/
theorem coverageBranchNodes_5_11_00128 :
    nodeClaimChunkValidB branchClaims5Row11 128 25 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 12), starting at 0.
@isnad1 id=eq.0h0v.s3.cbc2b46eb51c from=translated src=- shape=6f582f20 vocab=8ccb4304
-/
theorem coverageBranchNodes_5_12_00000 :
    nodeClaimChunkValidB branchClaims5Row12 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
