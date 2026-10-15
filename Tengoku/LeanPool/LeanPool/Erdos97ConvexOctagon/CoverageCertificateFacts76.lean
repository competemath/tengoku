/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData12
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (4, 0).
@isnad1 id=eq.0h0v.s5.65266cf460ba from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_00 :
    branchClaimRootValidB 4 0 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 8).
@isnad1 id=eq.0h0v.s5.3b1e0aca0c58 from=translated src=- shape=e9e0773c vocab=6febaeea
-/
theorem coverageBranchRoot_6_08 :
    branchClaimRootValidB 6 8 (.search branchClaims6Row8) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 9).
@isnad1 id=eq.0h0v.s5.256842e16257 from=translated src=- shape=e9e0773c vocab=4d30bdc1
-/
theorem coverageBranchRoot_6_09 :
    branchClaimRootValidB 6 9 (.search branchClaims6Row9) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 8), starting at 0.
@isnad1 id=eq.0h0v.s3.e43a8a14c919 from=translated src=- shape=6f582f20 vocab=93874451
-/
theorem coverageBranchNodes_6_08_00000 :
    nodeClaimChunkValidB branchClaims6Row8 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 8), starting at 64.
@isnad1 id=eq.0h0v.s3.1bf5227a443b from=translated src=- shape=6f582f20 vocab=93874451
-/
theorem coverageBranchNodes_6_08_00064 :
    nodeClaimChunkValidB branchClaims6Row8 64 28 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 8), starting at 92.
@isnad1 id=eq.0h0v.s3.480e12a0d734 from=translated src=- shape=6f582f20 vocab=93874451
-/
theorem coverageBranchNodes_6_08_00092 :
    nodeClaimChunkValidB branchClaims6Row8 92 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 9), starting at 0.
@isnad1 id=eq.0h0v.s3.db1e628e5f15 from=translated src=- shape=6f582f20 vocab=ee60d6c2
-/
theorem coverageBranchNodes_6_09_00000 :
    nodeClaimChunkValidB branchClaims6Row9 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
