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

/-- Root audit for fixed branch (3, 18).
@isnad1 id=eq.0h0v.s5.3a9a0f7ffe1a from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_18 :
    branchClaimRootValidB 3 18 (.patternThree 5) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 31), starting at 192.
@isnad1 id=eq.0h0v.s3.b6bf93bfddda from=translated src=- shape=6f582f20 vocab=677a6d2a
-/
theorem coverageBranchNodes_5_31_00192 :
    nodeClaimChunkValidB branchClaims5Row31 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 31), starting at 256.
@isnad1 id=eq.0h0v.s3.fd968ae65051 from=translated src=- shape=6f582f20 vocab=677a6d2a
-/
theorem coverageBranchNodes_5_31_00256 :
    nodeClaimChunkValidB branchClaims5Row31 256 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 31), starting at 320.
@isnad1 id=eq.0h0v.s3.24e25028ce09 from=translated src=- shape=6f582f20 vocab=677a6d2a
-/
theorem coverageBranchNodes_5_31_00320 :
    nodeClaimChunkValidB branchClaims5Row31 320 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 31), starting at 352.
@isnad1 id=eq.0h0v.s3.c8f4019e8625 from=translated src=- shape=6f582f20 vocab=677a6d2a
-/
theorem coverageBranchNodes_5_31_00352 :
    nodeClaimChunkValidB branchClaims5Row31 352 32 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
