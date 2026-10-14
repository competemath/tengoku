/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData14
public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData15
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 15).
@isnad1 id=eq.0h0v.s5.04a10398266a from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_15 :
    branchClaimRootValidB 4 15 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 31).
@isnad1 id=eq.0h0v.s5.0a343d3d01b9 from=translated src=- shape=e9e0773c vocab=3cd29a37
-/
theorem coverageBranchRoot_6_31 :
    branchClaimRootValidB 6 31 (.search branchClaims6Row31) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 30), starting at 256.
@isnad1 id=eq.0h0v.s3.5bc7de49bdb8 from=translated src=- shape=6f582f20 vocab=f9f6cde3
-/
theorem coverageBranchNodes_6_30_00256 :
    nodeClaimChunkValidB branchClaims6Row30 256 9 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 31), starting at 0.
@isnad1 id=eq.0h0v.s3.025243e109b1 from=translated src=- shape=6f582f20 vocab=dbf421f1
-/
theorem coverageBranchNodes_6_31_00000 :
    nodeClaimChunkValidB branchClaims6Row31 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 31), starting at 64.
@isnad1 id=eq.0h0v.s3.650874a3a0d8 from=translated src=- shape=6f582f20 vocab=dbf421f1
-/
theorem coverageBranchNodes_6_31_00064 :
    nodeClaimChunkValidB branchClaims6Row31 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 31), starting at 128.
@isnad1 id=eq.0h0v.s3.863706db607b from=translated src=- shape=6f582f20 vocab=dbf421f1
-/
theorem coverageBranchNodes_6_31_00128 :
    nodeClaimChunkValidB branchClaims6Row31 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
