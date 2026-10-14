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

/-- Root audit for fixed branch (4, 14).
@isnad1 id=eq.0h0v.s5.0a745572c014 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_14 :
    branchClaimRootValidB 4 14 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 30).
@isnad1 id=eq.0h0v.s5.0d2bbc3db512 from=translated src=- shape=e9e0773c vocab=e55e68a9
-/
theorem coverageBranchRoot_6_30 :
    branchClaimRootValidB 6 30 (.search branchClaims6Row30) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 30), starting at 0.
@isnad1 id=eq.0h0v.s3.0132e0c52155 from=translated src=- shape=6f582f20 vocab=f9f6cde3
-/
theorem coverageBranchNodes_6_30_00000 :
    nodeClaimChunkValidB branchClaims6Row30 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 30), starting at 64.
@isnad1 id=eq.0h0v.s3.903130086279 from=translated src=- shape=6f582f20 vocab=f9f6cde3
-/
theorem coverageBranchNodes_6_30_00064 :
    nodeClaimChunkValidB branchClaims6Row30 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 30), starting at 128.
@isnad1 id=eq.0h0v.s3.a9019cbe4d61 from=translated src=- shape=6f582f20 vocab=f9f6cde3
-/
theorem coverageBranchNodes_6_30_00128 :
    nodeClaimChunkValidB branchClaims6Row30 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 30), starting at 192.
@isnad1 id=eq.0h0v.s3.955932f1e590 from=translated src=- shape=6f582f20 vocab=f9f6cde3
-/
theorem coverageBranchNodes_6_30_00192 :
    nodeClaimChunkValidB branchClaims6Row30 192 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
