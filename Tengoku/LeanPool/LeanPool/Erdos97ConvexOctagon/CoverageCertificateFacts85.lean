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

/-- Root audit for fixed branch (4, 9).
@isnad1 id=eq.0h0v.s5.cf77c84cd60d from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_09 :
    branchClaimRootValidB 4 9 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 24).
@isnad1 id=eq.0h0v.s5.eadcba2e2f61 from=translated src=- shape=e9e0773c vocab=81c564c7
-/
theorem coverageBranchRoot_6_24 :
    branchClaimRootValidB 6 24 (.search branchClaims6Row24) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 24), starting at 0.
@isnad1 id=eq.0h0v.s3.50bf9b61e749 from=translated src=- shape=6f582f20 vocab=a31b6116
-/
theorem coverageBranchNodes_6_24_00000 :
    nodeClaimChunkValidB branchClaims6Row24 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 24), starting at 64.
@isnad1 id=eq.0h0v.s3.48767adf9baf from=translated src=- shape=6f582f20 vocab=a31b6116
-/
theorem coverageBranchNodes_6_24_00064 :
    nodeClaimChunkValidB branchClaims6Row24 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 24), starting at 128.
@isnad1 id=eq.0h0v.s3.d48e8bcd7fce from=translated src=- shape=6f582f20 vocab=a31b6116
-/
theorem coverageBranchNodes_6_24_00128 :
    nodeClaimChunkValidB branchClaims6Row24 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 24), starting at 192.
@isnad1 id=eq.0h0v.s3.12553d05edab from=translated src=- shape=6f582f20 vocab=a31b6116
-/
theorem coverageBranchNodes_6_24_00192 :
    nodeClaimChunkValidB branchClaims6Row24 192 43 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
