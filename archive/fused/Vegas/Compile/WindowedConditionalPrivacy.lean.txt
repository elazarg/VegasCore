/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedPolicyPrivacy

/-! # Paired inclusion of certified conditional publications -/

noncomputable section

namespace Vegas.WindowedApplication.PolicyAgreement

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}
variable {runtime : WindowedApplication P L} {focal : P}
variable {left right : runtime.application.PolicyExecution}

/-- Including the same certified conditional packet preserves focal policy
agreement when both handlers publish the same result. The two handler
equalities are local acceptance obligations for a compiler theorem; they do
not assume global equality of private verifier state or that the author is the
focal player. -/
theorem environmentPolicyStep_include_conditional
    (agreement : PolicyAgreement runtime focal left right)
    (code : ConditionalCode P L) (result : Option (L.Val code.secretTy))
    (id : MessageId P)
    (message : Message P (ApplicationImage.Payload P L))
    (hlookup : left.native.pool.lookup id = some message)
    (hleftHandle : runtime.handle left.native.application message = some
      (runtime.advanceTo left.native.application
        (left.native.application.base.publishConditional code result)))
    (hrightHandle : runtime.handle right.native.application message = some
      (runtime.advanceTo right.native.application
        (right.native.application.base.publishConditional code result)))
    (nextLeft nextRight : runtime.application.PolicyExecution)
    (hleft : nextLeft ∈
      (runtime.application.environmentPolicyStep left (.include id)).support)
    (hright : nextRight ∈
      (runtime.application.environmentPolicyStep right (.include id)).support) :
    PolicyAgreement runtime focal nextLeft nextRight := by
  have hrightLookup : right.native.pool.lookup id = some message := by
    rw [← agreement.pool]
    exact hlookup
  have hbase :
      (left.native.application.base.publishConditional code result).AgreesFor focal
        (right.native.application.base.publishConditional code result) :=
    agreement.state.base.publishConditional code result
  have happlication :
      (runtime.advanceTo left.native.application
          (left.native.application.base.publishConditional code result)).AgreesFor focal
        (runtime.advanceTo right.native.application
          (right.native.application.base.publishConditional code result)) :=
    agreement.state.advanceTo runtime hbase
  simp only [MessageApplication.environmentPolicyStep, MessageApplication.advance,
    EnvironmentPolicyCommand.toAction, MessageApplication.step, FinDist.pure_bind,
    FinDist.mem_support_pure] at hleft hright
  subst nextLeft
  subst nextRight
  rw [runtime.application.includePending_accept left.native id message _ hlookup hleftHandle,
    runtime.application.includePending_accept right.native id message _
      hrightLookup hrightHandle]
  exact ⟨happlication, by rw [agreement.pool], by rw [agreement.receipts], agreement.history⟩

end Vegas.WindowedApplication.PolicyAgreement

/-- info:
'Vegas.WindowedApplication.PolicyAgreement.environmentPolicyStep_include_conditional'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms
  Vegas.WindowedApplication.PolicyAgreement.environmentPolicyStep_include_conditional
