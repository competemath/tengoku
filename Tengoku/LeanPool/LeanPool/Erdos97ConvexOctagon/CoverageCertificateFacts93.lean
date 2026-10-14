/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData15
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 17).
@isnad1 id=eq.0h0v.s5.f7e85c35f269 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_17 :
    branchClaimRootValidB 4 17 (.patternTwo 0) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 32), starting at 128.
@isnad1 id=eq.0h0v.s3.580ca78858c7 from=translated src=- shape=6f582f20 vocab=257efa1c
-/
theorem coverageBranchNodes_6_32_00128 :
    nodeClaimChunkValidB branchClaims6Row32 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 32), starting at 192.
@isnad1 id=eq.0h0v.s3.cb6948ed22d9 from=translated src=- shape=6f582f20 vocab=257efa1c
-/
theorem coverageBranchNodes_6_32_00192 :
    nodeClaimChunkValidB branchClaims6Row32 192 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 32), starting at 256.
@isnad1 id=eq.0h0v.s3.186a6ddde18f from=translated src=- shape=6f582f20 vocab=257efa1c
-/
theorem coverageBranchNodes_6_32_00256 :
    nodeClaimChunkValidB branchClaims6Row32 256 1 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
