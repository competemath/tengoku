/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData06
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (1, 3).
@isnad1 id=eq.0h0v.s5.9a2733741236 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_03 :
    branchClaimRootValidB 1 3 (.patternThree 178) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 26).
@isnad1 id=eq.0h0v.s5.ebe4555713f9 from=translated src=- shape=e9e0773c vocab=d3b43ce4
-/
theorem coverageBranchRoot_3_26 :
    branchClaimRootValidB 3 26 (.search branchClaims3Row26) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 25), starting at 320.
@isnad1 id=eq.0h0v.s3.90dd24921309 from=translated src=- shape=6f582f20 vocab=8f57ad29
-/
theorem coverageBranchNodes_3_25_00320 :
    nodeClaimChunkValidB branchClaims3Row25 320 21 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 26), starting at 0.
@isnad1 id=eq.0h0v.s3.325c8920efe2 from=translated src=- shape=6f582f20 vocab=bcc82e23
-/
theorem coverageBranchNodes_3_26_00000 :
    nodeClaimChunkValidB branchClaims3Row26 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 26), starting at 64.
@isnad1 id=eq.0h0v.s3.6d521caaad2c from=translated src=- shape=6f582f20 vocab=bcc82e23
-/
theorem coverageBranchNodes_3_26_00064 :
    nodeClaimChunkValidB branchClaims3Row26 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 26), starting at 128.
@isnad1 id=eq.0h0v.s3.c38b8aae22ef from=translated src=- shape=6f582f20 vocab=bcc82e23
-/
theorem coverageBranchNodes_3_26_00128 :
    nodeClaimChunkValidB branchClaims3Row26 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
