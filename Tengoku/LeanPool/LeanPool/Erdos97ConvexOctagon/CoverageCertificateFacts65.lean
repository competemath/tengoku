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

/-- Root audit for fixed branch (3, 15).
@isnad1 id=eq.0h0v.s5.9d9fd551f9df from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_15 :
    branchClaimRootValidB 3 15 (.patternThree 5) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 128.
@isnad1 id=eq.0h0v.s3.8c629f03b35e from=translated src=- shape=6f582f20 vocab=962ae527
-/
theorem coverageBranchNodes_5_28_00128 :
    nodeClaimChunkValidB branchClaims5Row28 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 192.
@isnad1 id=eq.0h0v.s3.8d0aa5949603 from=translated src=- shape=6f582f20 vocab=962ae527
-/
theorem coverageBranchNodes_5_28_00192 :
    nodeClaimChunkValidB branchClaims5Row28 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 256.
@isnad1 id=eq.0h0v.s3.3ee9999089d4 from=translated src=- shape=6f582f20 vocab=962ae527
-/
theorem coverageBranchNodes_5_28_00256 :
    nodeClaimChunkValidB branchClaims5Row28 256 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 28), starting at 288.
@isnad1 id=eq.0h0v.s3.f5ffef3aa7c1 from=translated src=- shape=6f582f20 vocab=962ae527
-/
theorem coverageBranchNodes_5_28_00288 :
    nodeClaimChunkValidB branchClaims5Row28 288 32 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
