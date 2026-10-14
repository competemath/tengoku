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

/-- Root audit for fixed branch (4, 6).
@isnad1 id=eq.0h0v.s5.cba90f385aa1 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_06 :
    branchClaimRootValidB 4 6 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 17).
@isnad1 id=eq.0h0v.s5.33cfed6dcc24 from=translated src=- shape=e9e0773c vocab=9b9a85b9
-/
theorem coverageBranchRoot_6_17 :
    branchClaimRootValidB 6 17 (.search branchClaims6Row17) = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 16), starting at 64.
@isnad1 id=eq.0h0v.s3.289343001c7c from=translated src=- shape=6f582f20 vocab=2feb8b88
-/
theorem coverageBranchNodes_6_16_00064 :
    nodeClaimChunkValidB branchClaims6Row16 64 54 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 17), starting at 0.
@isnad1 id=eq.0h0v.s3.fb1b876d06d6 from=translated src=- shape=6f582f20 vocab=d145ddd5
-/
theorem coverageBranchNodes_6_17_00000 :
    nodeClaimChunkValidB branchClaims6Row17 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 17), starting at 64.
@isnad1 id=eq.0h0v.s3.e12aa1ac3ff4 from=translated src=- shape=6f582f20 vocab=d145ddd5
-/
theorem coverageBranchNodes_6_17_00064 :
    nodeClaimChunkValidB branchClaims6Row17 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (6, 17), starting at 128.
@isnad1 id=eq.0h0v.s3.7c653a4ab4e0 from=translated src=- shape=6f582f20 vocab=d145ddd5
-/
theorem coverageBranchNodes_6_17_00128 :
    nodeClaimChunkValidB branchClaims6Row17 128 43 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
