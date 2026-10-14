/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData04
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 30).
@isnad1 id=eq.0h0v.s5.d833f7d9ce73 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_30 :
    branchClaimRootValidB 0 30 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (6, 20).
@isnad1 id=eq.0h0v.s5.78a3f200cb5e from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_6_20 :
    branchClaimRootValidB 6 20 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 3).
@isnad1 id=eq.0h0v.s5.fbb0a7f5e7cd from=translated src=- shape=e9e0773c vocab=68c89b6a
-/
theorem coverageBranchRoot_3_03 :
    branchClaimRootValidB 3 3 (.search branchClaims3Row3) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 4).
@isnad1 id=eq.0h0v.s5.b1e8ec239d0b from=translated src=- shape=e9e0773c vocab=cac83cf4
-/
theorem coverageBranchRoot_3_04 :
    branchClaimRootValidB 3 4 (.search branchClaims3Row4) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 2), starting at 64.
@isnad1 id=eq.0h0v.s3.d28b1672c958 from=translated src=- shape=6f582f20 vocab=dd379bbc
-/
theorem coverageBranchNodes_3_02_00064 :
    nodeClaimChunkValidB branchClaims3Row2 64 52 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 3), starting at 0.
@isnad1 id=eq.0h0v.s3.caba43110fdc from=translated src=- shape=6f582f20 vocab=3e0cf0b4
-/
theorem coverageBranchNodes_3_03_00000 :
    nodeClaimChunkValidB branchClaims3Row3 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 3), starting at 64.
@isnad1 id=eq.0h0v.s3.18e65224d7c4 from=translated src=- shape=6f582f20 vocab=3e0cf0b4
-/
theorem coverageBranchNodes_3_03_00064 :
    nodeClaimChunkValidB branchClaims3Row3 64 31 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 4), starting at 0.
@isnad1 id=eq.0h0v.s3.cf0a78ac1762 from=translated src=- shape=6f582f20 vocab=4d741516
-/
theorem coverageBranchNodes_3_04_00000 :
    nodeClaimChunkValidB branchClaims3Row4 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
