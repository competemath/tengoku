/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData07
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 20).
@isnad1 id=eq.0h0v.s5.9e1e75149337 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_20 :
    branchClaimRootValidB 1 20 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 32).
@isnad1 id=eq.0h0v.s5.f244466ed68a from=translated src=- shape=e9e0773c vocab=2cb30090
-/
theorem coverageBranchRoot_3_32 :
    branchClaimRootValidB 3 32 (.search branchClaims3Row32) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 32), starting at 0.
@isnad1 id=eq.0h0v.s3.dc6037f70b0b from=translated src=- shape=6f582f20 vocab=366eccd2
-/
theorem coverageBranchNodes_3_32_00000 :
    nodeClaimChunkValidB branchClaims3Row32 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 32), starting at 64.
@isnad1 id=eq.0h0v.s3.41aab7eff4d6 from=translated src=- shape=6f582f20 vocab=366eccd2
-/
theorem coverageBranchNodes_3_32_00064 :
    nodeClaimChunkValidB branchClaims3Row32 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 32), starting at 128.
@isnad1 id=eq.0h0v.s3.9ad9e49a104b from=translated src=- shape=6f582f20 vocab=366eccd2
-/
theorem coverageBranchNodes_3_32_00128 :
    nodeClaimChunkValidB branchClaims3Row32 128 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 32), starting at 192.
@isnad1 id=eq.0h0v.s3.7530acc0e768 from=translated src=- shape=6f582f20 vocab=366eccd2
-/
theorem coverageBranchNodes_3_32_00192 :
    nodeClaimChunkValidB branchClaims3Row32 192 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
