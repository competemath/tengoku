/-
Copyright (c) 2026 Egor Lyfar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egor Lyfar
-/
module

public import Tengoku.LeanPool.LeanPool.Erdos97ConvexOctagon.CoverageCertificateData10
public import Tengoku

/-! # Bounded coverage-certificate computation facts -/

@[expose] public section

namespace Erdos97Octagon.RawIncidence.StaticDirectCoverage

/-- Root audit for fixed branch (3, 8).
@isnad1 id=eq.0h0v.s5.27be909577c8 from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_3_08 :
    branchClaimRootValidB 3 8 (.patternThree 4) = true := by
  decide +kernel

/-- Root audit for fixed branch (5, 26).
@isnad1 id=eq.0h0v.s5.87a1cd8a1586 from=translated src=- shape=e9e0773c vocab=7f975de6
-/
theorem coverageBranchRoot_5_26 :
    branchClaimRootValidB 5 26 (.search branchClaims5Row26) = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 25), starting at 223.
@isnad1 id=eq.0h0v.s3.a084ec999ce9 from=translated src=- shape=6f582f20 vocab=0ab4b116
-/
theorem coverageBranchNodes_5_25_00223 :
    nodeClaimChunkValidB branchClaims5Row25 223 31 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 26), starting at 0.
@isnad1 id=eq.0h0v.s3.cb21d2c84b94 from=translated src=- shape=6f582f20 vocab=bb88c2f5
-/
theorem coverageBranchNodes_5_26_00000 :
    nodeClaimChunkValidB branchClaims5Row26 0 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 26), starting at 64.
@isnad1 id=eq.0h0v.s3.252c72f1f53e from=translated src=- shape=6f582f20 vocab=bb88c2f5
-/
theorem coverageBranchNodes_5_26_00064 :
    nodeClaimChunkValidB branchClaims5Row26 64 64 = true := by
  decide +kernel

/-- Node audit for fixed branch (5, 26), starting at 128.
@isnad1 id=eq.0h0v.s3.73e0dde7300f from=translated src=- shape=6f582f20 vocab=bb88c2f5
-/
theorem coverageBranchNodes_5_26_00128 :
    nodeClaimChunkValidB branchClaims5Row26 128 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
