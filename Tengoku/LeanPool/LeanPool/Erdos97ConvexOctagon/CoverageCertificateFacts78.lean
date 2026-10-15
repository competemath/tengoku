/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData13
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 2).
@isnad1 id=eq.0h0v.s5.fc8c794e3bc2 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_02 :
    branchClaimRootValidB 4 2 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 11).
@isnad1 id=eq.0h0v.s5.9ea88bbdf40d from=translated src=- shape=e9e0773c vocab=0776b384
-/
theorem coverageBranchRoot_6_11 :
    branchClaimRootValidB 6 11 (.search branchClaims6Row11) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 12).
@isnad1 id=eq.0h0v.s5.a90fc2d39513 from=translated src=- shape=e9e0773c vocab=9f3f8e8d
-/
theorem coverageBranchRoot_6_12 :
    branchClaimRootValidB 6 12 (.search branchClaims6Row12) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 11), starting at 0.
@isnad1 id=eq.0h0v.s3.b4cc25d19b42 from=translated src=- shape=6f582f20 vocab=115a6524
-/
theorem coverageBranchNodes_6_11_00000 :
    nodeClaimChunkValidB branchClaims6Row11 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 11), starting at 64.
@isnad1 id=eq.0h0v.s3.7d7fafeeca78 from=translated src=- shape=6f582f20 vocab=115a6524
-/
theorem coverageBranchNodes_6_11_00064 :
    nodeClaimChunkValidB branchClaims6Row11 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 11), starting at 128.
@isnad1 id=eq.0h0v.s3.b537a8f696e6 from=translated src=- shape=6f582f20 vocab=115a6524
-/
theorem coverageBranchNodes_6_11_00128 :
    nodeClaimChunkValidB branchClaims6Row11 128 14 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 12), starting at 0.
@isnad1 id=eq.0h0v.s3.1d2fe7dda327 from=translated src=- shape=6f582f20 vocab=738fd675
-/
theorem coverageBranchNodes_6_12_00000 :
    nodeClaimChunkValidB branchClaims6Row12 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
