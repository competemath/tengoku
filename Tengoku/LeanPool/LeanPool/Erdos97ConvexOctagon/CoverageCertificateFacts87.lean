/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 11).
@isnad1 id=eq.0h0v.s5.345c7f99fa09 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_11 :
    branchClaimRootValidB 4 11 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 26).
@isnad1 id=eq.0h0v.s5.7e8b8f8fbc9f from=translated src=- shape=e9e0773c vocab=684f73b0
-/
theorem coverageBranchRoot_6_26 :
    branchClaimRootValidB 6 26 (.search branchClaims6Row26) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 26), starting at 0.
@isnad1 id=eq.0h0v.s3.ac186fc645dc from=translated src=- shape=6f582f20 vocab=0de1f7e3
-/
theorem coverageBranchNodes_6_26_00000 :
    nodeClaimChunkValidB branchClaims6Row26 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 26), starting at 64.
@isnad1 id=eq.0h0v.s3.305644220f65 from=translated src=- shape=6f582f20 vocab=0de1f7e3
-/
theorem coverageBranchNodes_6_26_00064 :
    nodeClaimChunkValidB branchClaims6Row26 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 26), starting at 128.
@isnad1 id=eq.0h0v.s3.dab29ad02fee from=translated src=- shape=6f582f20 vocab=0de1f7e3
-/
theorem coverageBranchNodes_6_26_00128 :
    nodeClaimChunkValidB branchClaims6Row26 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 26), starting at 192.
@isnad1 id=eq.0h0v.s3.8b56baf79fde from=translated src=- shape=6f582f20 vocab=0de1f7e3
-/
theorem coverageBranchNodes_6_26_00192 :
    nodeClaimChunkValidB branchClaims6Row26 192 40 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
