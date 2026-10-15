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

/-- Root audit for fixed branch (2, 13).
@isnad1 id=eq.0h0v.s5.ddec1aaee680 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_2_13 :
    branchClaimRootValidB 2 13 (.patternThree 2) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 15).
@isnad1 id=eq.0h0v.s5.f52a37329205 from=translated src=- shape=e9e0773c vocab=b56892fd
-/
theorem coverageBranchRoot_5_15 :
    branchClaimRootValidB 5 15 (.search branchClaims5Row15) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 14), starting at 320.
@isnad1 id=eq.0h0v.s3.029067b9cac9 from=translated src=- shape=6f582f20 vocab=89a7448e
-/
theorem coverageBranchNodes_5_14_00320 :
    nodeClaimChunkValidB branchClaims5Row14 320 44 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 15), starting at 0.
@isnad1 id=eq.0h0v.s3.4cf915e9819f from=translated src=- shape=6f582f20 vocab=15da5cca
-/
theorem coverageBranchNodes_5_15_00000 :
    nodeClaimChunkValidB branchClaims5Row15 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 15), starting at 64.
@isnad1 id=eq.0h0v.s3.bc1244ec2ab5 from=translated src=- shape=6f582f20 vocab=15da5cca
-/
theorem coverageBranchNodes_5_15_00064 :
    nodeClaimChunkValidB branchClaims5Row15 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 15), starting at 128.
@isnad1 id=eq.0h0v.s3.adb68d851f80 from=translated src=- shape=6f582f20 vocab=15da5cca
-/
theorem coverageBranchNodes_5_15_00128 :
    nodeClaimChunkValidB branchClaims5Row15 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
