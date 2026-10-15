/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData11
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 21).
@isnad1 id=eq.0h0v.s5.2a23c972af8e from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_21 :
    branchClaimRootValidB 3 21 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 34).
@isnad1 id=eq.0h0v.s5.2e8a2354aac8 from=translated src=- shape=e9e0773c vocab=73c4dfd3
-/
theorem coverageBranchRoot_5_34 :
    branchClaimRootValidB 5 34 (.search branchClaims5Row34) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 352.
@isnad1 id=eq.0h0v.s3.1cc498249b32 from=translated src=- shape=6f582f20 vocab=e3f0be63
-/
theorem coverageBranchNodes_5_32_00352 :
    nodeClaimChunkValidB branchClaims5Row32 352 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 384.
@isnad1 id=eq.0h0v.s3.2a81810cb891 from=translated src=- shape=6f582f20 vocab=e3f0be63
-/
theorem coverageBranchNodes_5_32_00384 :
    nodeClaimChunkValidB branchClaims5Row32 384 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 32), starting at 413.
@isnad1 id=eq.0h0v.s3.e1e54dc25832 from=translated src=- shape=6f582f20 vocab=e3f0be63
-/
theorem coverageBranchNodes_5_32_00413 :
    nodeClaimChunkValidB branchClaims5Row32 413 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 34), starting at 0.
@isnad1 id=eq.0h0v.s3.7bfa3da31584 from=translated src=- shape=6f582f20 vocab=fbc3c659
-/
theorem coverageBranchNodes_5_34_00000 :
    nodeClaimChunkValidB branchClaims5Row34 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
