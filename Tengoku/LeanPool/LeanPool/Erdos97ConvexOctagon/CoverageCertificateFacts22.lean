/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData03
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (0, 22).
@isnad1 id=eq.0h0v.s5.b43dd007d906 from=translated src=- shape=2fed53d3 vocab=765e34ad
-/
theorem coverageBranchRoot_0_22 :
    branchClaimRootValidB 0 22 (.patternTwo 0) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 20).
@isnad1 id=eq.0h0v.s5.fcf914be9cac from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_5_20 :
    branchClaimRootValidB 5 20 (.patternThree 1) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 25).
@isnad1 id=eq.0h0v.s5.e02a2cfd195b from=translated src=- shape=e9e0773c vocab=8261d0d6
-/
theorem coverageBranchRoot_2_25 :
    branchClaimRootValidB 2 25 (.search branchClaims2Row25) = true := by
  decide +kernel

/-- Root audit for fixed branch (2, 26).
@isnad1 id=eq.0h0v.s5.b0483411a29c from=translated src=- shape=e9e0773c vocab=9e023b0e
-/
theorem coverageBranchRoot_2_26 :
    branchClaimRootValidB 2 26 (.search branchClaims2Row26) = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 24), starting at 64.
@isnad1 id=eq.0h0v.s3.11f206f8d450 from=translated src=- shape=6f582f20 vocab=302567cb
-/
theorem coverageBranchNodes_2_24_00064 :
    nodeClaimChunkValidB branchClaims2Row24 64 46 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 25), starting at 0.
@isnad1 id=eq.0h0v.s3.44d2220c62d5 from=translated src=- shape=6f582f20 vocab=80cd3124
-/
theorem coverageBranchNodes_2_25_00000 :
    nodeClaimChunkValidB branchClaims2Row25 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 25), starting at 64.
@isnad1 id=eq.0h0v.s3.016c90840c24 from=translated src=- shape=6f582f20 vocab=80cd3124
-/
theorem coverageBranchNodes_2_25_00064 :
    nodeClaimChunkValidB branchClaims2Row25 64 41 = true := by
  decide +kernel

/-- Node audit for fixed branch (2, 26), starting at 0.
@isnad1 id=eq.0h0v.s3.024e4837be34 from=translated src=- shape=6f582f20 vocab=4af5a85f
-/
theorem coverageBranchNodes_2_26_00000 :
    nodeClaimChunkValidB branchClaims2Row26 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
