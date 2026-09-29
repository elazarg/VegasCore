/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceDisclosure
import GameTheoryExtensions.Math.Probability.ConditionalNoise

/-! # Private intentions behind a failed native disclosure

At an actual compiled guarded resolve, an ineffective source disclosure and
withholding produce the same native silence. Conditioning on that physical
response preserves the complete source intention distribution. Restoring the
private intention reconstructs the original source successor, including the
history used by later source policies. This is a local operational posterior
identity, not a claim about arbitrary native information-site beliefs.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  {Γ : SourceCtx Player L} {name : VarId} {owner : Player} {payload : L.Ty}
  (published : VarId) (binding : HasVar Γ name (.commitment owner payload))
  (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
  (execution : (application setup leaks).Execution)
  (agree : refs.Agrees source.state execution.application.config.store)
  (event : (graph setup).EventId)
  (outputEq : (graph setup).outputLayout event = .publication payload)
  (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
    ((graph setup).nodes event) = .resolve owner payload (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding))
  (node : nodeView (graph setup) event = .resolve owner payload (refs.get binding)
    (compileChecks (published := published) refs source.registry source.revelations binding)
    outputEq codeEq)

include agree node

/-- A guarded source failure is actual silence under the retained compiler,
whether the original private intention was withholding or disclosure. -/
theorem failed_disclosure_response
    (failure : disclosureResult published binding source true = .failure)
    (intention : Bool) :
    (runtime setup).serviceDecision leaks owner (execution.recall owner)
      (execution.observe (application setup leaks) owner) event
      (cast (congrArg EventGraph.EventField.Action outputEq.symm) intention) = ⟨none⟩ := by
  have resolved := compiled_disclosure_result published binding source refs
    execution.application.config.store agree true
  rw [failure] at resolved
  have localResult : EventGraph.EventCode.resolveOutput? (refs.get binding)
      (compileChecks (published := published) refs source.registry source.revelations binding)
      true (execution.observe (application setup leaks) owner).application.observation.store =
        some .failure := resolved
  cases intention <;>
    simp only [serviceDecision, reactiveDecision, node, reactiveResolutionPacket,
      cast_cast, cast_eq, localResult, Bool.false_eq_true, ↓reduceIte] <;>
    rw [disclosureSubmission_normalize_withhold] <;> rfl

/-- The posterior over original intentions after the physical silent response
is the original law. In particular, no artificial resampling or erasure of the
owner's private failed intention is justified by this response. -/
theorem failed_disclosure_response_posterior
    (failure : disclosureResult published binding source true = .failure)
    (intentions : PMF Bool) :
    fiberConditional intentions (fun intention =>
      (runtime setup).serviceDecision leaks owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) intention)) ⟨none⟩ =
      intentions := by
  classical
  have constant := failed_disclosure_response setup leaks published binding source refs
    execution agree event outputEq codeEq node failure
  have functionEq : (fun intention =>
      (runtime setup).serviceDecision leaks owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) intention)) =
      fun _ : Bool => (⟨none⟩ : (application setup leaks).Action) := funext constant
  rw [functionEq]
  have fiber : (fun _ : Bool => (⟨none⟩ : (application setup leaks).Action)) ⁻¹'
      {⟨none⟩} = Set.univ := by ext intention; simp only [Set.mem_preimage,
        Set.mem_singleton_iff, Set.mem_univ]
  obtain ⟨intention, supported⟩ := intentions.support_nonempty
  have present : ∃ intention ∈ (Set.univ : Set Bool), intention ∈ intentions.support :=
    ⟨intention, Set.mem_univ _, supported⟩
  simp only [fiberConditional, fiber, dite_eq_left present, FinDist.condOn_univ]

/-- Conditioning the original successor on the actual failed native response
retains both intended actions. The normalized source successor is withholding;
its private-history posterior restores the original successor exactly. -/
theorem failed_disclosure_successor_posterior
    (failure : disclosureResult published binding source true = .failure)
    (intentions : PMF Bool) :
    ((fiberConditional intentions (fun intention =>
      (runtime setup).serviceDecision leaks owner (execution.recall owner)
        (execution.observe (application setup leaks) owner) event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) intention)) ⟨none⟩).map
      (revealSuccessor published binding source)) =
      intentions.map (fun intention =>
        (revealSuccessor published binding source false).restoreDisclosure
          owner name intention) := by
  rw [failed_disclosure_response_posterior setup leaks published binding source refs
    execution agree event outputEq codeEq node failure intentions]
  apply map_congr_on_support _
  intro intention _supported
  have effective : effectiveDisclosure published binding source intention = false := by
    cases intention <;> simp only [effectiveDisclosure, disclosureResult_false, failure]
  rw [← effective, revealSuccessor_restore_effective]

end Vegas
