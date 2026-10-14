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

/-- Root audit for fixed branch (3, 13).
@isnad1 id=eq.0h0v.s5.9d2400a38742 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_13 :
    branchClaimRootValidB 3 13 (.patternThree 2) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 128.
@isnad1 id=eq.0h0v.s3.8e7d48b46fd1 from=translated src=- shape=6f582f20 vocab=6bef2226
-/
theorem coverageBranchNodes_5_27_00128 :
    nodeClaimChunkValidB branchClaims5Row27 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 192.
@isnad1 id=eq.0h0v.s3.5e96d249c2c9 from=translated src=- shape=6f582f20 vocab=6bef2226
-/
theorem coverageBranchNodes_5_27_00192 :
    nodeClaimChunkValidB branchClaims5Row27 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 256.
@isnad1 id=eq.0h0v.s3.dc578944250a from=translated src=- shape=6f582f20 vocab=6bef2226
-/
theorem coverageBranchNodes_5_27_00256 :
    nodeClaimChunkValidB branchClaims5Row27 256 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 27), starting at 320.
@isnad1 id=eq.0h0v.s3.792d67954cdd from=translated src=- shape=6f582f20 vocab=6bef2226
-/
theorem coverageBranchNodes_5_27_00320 :
    nodeClaimChunkValidB branchClaims5Row27 320 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
