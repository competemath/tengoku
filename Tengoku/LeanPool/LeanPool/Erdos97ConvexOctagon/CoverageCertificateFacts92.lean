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

/-- Root audit for fixed branch (4, 16).
@isnad1 id=eq.0h0v.s5.c0cc91ffa72a from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_16 :
    branchClaimRootValidB 4 16 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 32).
@isnad1 id=eq.0h0v.s5.e37e4d8211e2 from=translated src=- shape=e9e0773c vocab=fbf6dad6
-/
theorem coverageBranchRoot_6_32 :
    branchClaimRootValidB 6 32 (.search branchClaims6Row32) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 31), starting at 192.
@isnad1 id=eq.0h0v.s3.8c29f9a15ecb from=translated src=- shape=6f582f20 vocab=dbf421f1
-/
theorem coverageBranchNodes_6_31_00192 :
    nodeClaimChunkValidB branchClaims6Row31 192 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 31), starting at 221.
@isnad1 id=eq.0h0v.s3.98c67f9ff05c from=translated src=- shape=6f582f20 vocab=dbf421f1
-/
theorem coverageBranchNodes_6_31_00221 :
    nodeClaimChunkValidB branchClaims6Row31 221 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 32), starting at 0.
@isnad1 id=eq.0h0v.s3.498a388be321 from=translated src=- shape=6f582f20 vocab=257efa1c
-/
theorem coverageBranchNodes_6_32_00000 :
    nodeClaimChunkValidB branchClaims6Row32 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 32), starting at 64.
@isnad1 id=eq.0h0v.s3.4617845a98c6 from=translated src=- shape=6f582f20 vocab=257efa1c
-/
theorem coverageBranchNodes_6_32_00064 :
    nodeClaimChunkValidB branchClaims6Row32 64 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
