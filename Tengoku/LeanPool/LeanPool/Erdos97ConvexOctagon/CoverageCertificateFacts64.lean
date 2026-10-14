/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 14).
@isnad1 id=eq.0h0v.s5.9e71b92a5fd5 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_14 :
    branchClaimRootValidB 3 14 (.patternThree 4) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 28).
@isnad1 id=eq.0h0v.s5.15a6782c0ea2 from=translated src=- shape=e9e0773c vocab=18a28568
-/
theorem coverageBranchRoot_5_28 :
    branchClaimRootValidB 5 28 (.search branchClaims5Row28) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 384.
@isnad1 id=eq.0h0v.s3.eec8ef21e042 from=translated src=- shape=6f582f20 vocab=6bef2226
-/
theorem coverageBranchNodes_5_27_00384 :
    nodeClaimChunkValidB branchClaims5Row27 384 8 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 0.
@isnad1 id=eq.0h0v.s3.751001834783 from=translated src=- shape=6f582f20 vocab=962ae527
-/
theorem coverageBranchNodes_5_28_00000 :
    nodeClaimChunkValidB branchClaims5Row28 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 64.
@isnad1 id=eq.0h0v.s3.17f3c1dc59ed from=translated src=- shape=6f582f20 vocab=962ae527
-/
theorem coverageBranchNodes_5_28_00064 :
    nodeClaimChunkValidB branchClaims5Row28 64 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 96.
@isnad1 id=eq.0h0v.s3.e3b58d531bac from=translated src=- shape=6f582f20 vocab=962ae527
-/
theorem coverageBranchNodes_5_28_00096 :
    nodeClaimChunkValidB branchClaims5Row28 96 32 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
