/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData01
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 10).
@isnad1 id=eq.0h0v.s5.2d5fb253e265 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_10 :
    branchClaimRootValidB 0 10 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (4, 28).
@isnad1 id=eq.0h0v.s5.d2cce5cc2bf3 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_4_28 :
    branchClaimRootValidB 4 28 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (1, 32).
@isnad1 id=eq.0h0v.s5.a05ac02f8402 from=translated src=- shape=e9e0773c vocab=8e145b83
-/
theorem coverageBranchRoot_1_32 :
    branchClaimRootValidB 1 32 (.search branchClaims1Row32) = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 31), starting at 128.
@isnad1 id=eq.0h0v.s3.fac5a8da9eff from=translated src=- shape=6f582f20 vocab=83b05302
-/
theorem coverageBranchNodes_1_31_00128 :
    nodeClaimChunkValidB branchClaims1Row31 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 31), starting at 192.
@isnad1 id=eq.0h0v.s3.a07b904c26a3 from=translated src=- shape=6f582f20 vocab=83b05302
-/
theorem coverageBranchNodes_1_31_00192 :
    nodeClaimChunkValidB branchClaims1Row31 192 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 31), starting at 221.
@isnad1 id=eq.0h0v.s3.0ee18698164b from=translated src=- shape=6f582f20 vocab=83b05302
-/
theorem coverageBranchNodes_1_31_00221 :
    nodeClaimChunkValidB branchClaims1Row31 221 29 = true := by
  decide +kernel

/-- Node audit for fixed branch (1, 32), starting at 0.
@isnad1 id=eq.0h0v.s3.80e1b88db801 from=translated src=- shape=6f582f20 vocab=60ebc641
-/
theorem coverageBranchNodes_1_32_00000 :
    nodeClaimChunkValidB branchClaims1Row32 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
