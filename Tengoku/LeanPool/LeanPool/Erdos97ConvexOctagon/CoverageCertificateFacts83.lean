/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 7).
@isnad1 id=eq.0h0v.s5.d1a299f34e61 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_07 :
    branchClaimRootValidB 4 7 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 18).
@isnad1 id=eq.0h0v.s5.5c0fe1825662 from=translated src=- shape=e9e0773c vocab=a2f63dcb
-/
theorem coverageBranchRoot_6_18 :
    branchClaimRootValidB 6 18 (.search branchClaims6Row18) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 18), starting at 0.
@isnad1 id=eq.0h0v.s3.444996f48f4b from=translated src=- shape=6f582f20 vocab=3a371963
-/
theorem coverageBranchNodes_6_18_00000 :
    nodeClaimChunkValidB branchClaims6Row18 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 18), starting at 64.
@isnad1 id=eq.0h0v.s3.71579104be91 from=translated src=- shape=6f582f20 vocab=3a371963
-/
theorem coverageBranchNodes_6_18_00064 :
    nodeClaimChunkValidB branchClaims6Row18 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 18), starting at 128.
@isnad1 id=eq.0h0v.s3.02efe76637b1 from=translated src=- shape=6f582f20 vocab=3a371963
-/
theorem coverageBranchNodes_6_18_00128 :
    nodeClaimChunkValidB branchClaims6Row18 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 18), starting at 192.
@isnad1 id=eq.0h0v.s3.93ad8626fba7 from=translated src=- shape=6f582f20 vocab=3a371963
-/
theorem coverageBranchNodes_6_18_00192 :
    nodeClaimChunkValidB branchClaims6Row18 192 3 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
