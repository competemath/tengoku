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

/-- Root audit for fixed branch (1, 10).
@isnad1 id=eq.0h0v.s5.0d5c0db7347e from=translated src=- shape=2fed53d3 vocab=0443f047
-/
theorem coverageBranchRoot_1_10 :
    branchClaimRootValidB 1 10 (.patternThree 178) = true := by
  decide +kernel

/-- Root audit for fixed branch (3, 27).
@isnad1 id=eq.0h0v.s5.1919fa92b523 from=translated src=- shape=e9e0773c vocab=005d1a90
-/
theorem coverageBranchRoot_3_27 :
    branchClaimRootValidB 3 27 (.search branchClaims3Row27) = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 26), starting at 192.
@isnad1 id=eq.0h0v.s3.4f70297ed462 from=translated src=- shape=6f582f20 vocab=bcc82e23
-/
theorem coverageBranchNodes_3_26_00192 :
    nodeClaimChunkValidB branchClaims3Row26 192 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 26), starting at 224.
@isnad1 id=eq.0h0v.s3.6230d8a10cd4 from=translated src=- shape=6f582f20 vocab=bcc82e23
-/
theorem coverageBranchNodes_3_26_00224 :
    nodeClaimChunkValidB branchClaims3Row26 224 32 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 26), starting at 256.
@isnad1 id=eq.0h0v.s3.e8762fecd75e from=translated src=- shape=6f582f20 vocab=bcc82e23
-/
theorem coverageBranchNodes_3_26_00256 :
    nodeClaimChunkValidB branchClaims3Row26 256 42 = true := by
  decide +kernel

/-- Node audit for fixed branch (3, 27), starting at 0.
@isnad1 id=eq.0h0v.s3.41b8c4444241 from=translated src=- shape=6f582f20 vocab=3299c20b
-/
theorem coverageBranchNodes_3_27_00000 :
    nodeClaimChunkValidB branchClaims3Row27 0 64 = true := by
  decide +kernel

end Erdos97Octagon.RawIncidence.StaticDirectCoverage
