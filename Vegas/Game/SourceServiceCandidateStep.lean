/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCheckpoint
import Vegas.Pending.ReactiveBindingTranscript

/-! # Mixed source bindings preserve dynamic catalogue reconstruction

This instantiates the native allocation facts at the actual compiled source
commitment kernel. The public allocator is derived from its prepared-prefix
invariant. Both usable and unusable source bindings remain in the law.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

theorem sourceServicePolicy_commit_catalog_checkpoint
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    {name : VarId} {owner : Player} {payload : L.Ty}
    (fresh : name ∉ Γ.map Prod.fst) (guard : SourceGuard L Γ owner name payload)
    (next : SourceProgram Player L ((name, .commitment owner payload) :: Γ)
      (insert name openNames))
    (wholeProfile : BehavioralProfile setup.program)
    (profile : BehavioralProfile (.commit name owner fresh guard next))
    (refs : ContextRefs (graphLayout setup.program) Γ) (source : Config Player L Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      (.commit name owner fresh guard next))
    (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile
      (.commit name owner fresh guard next) profile
      refs source.revelations source.registry embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (checkpoint : SourceCheckpoint setup source refs offset execution.application.config)
    (represented : execution.application.CandidatesRepresented)
    (recorded : execution.application.AcceptedRecorded)
    (prepared : execution.application.PreparedPrefix owner)
    (unused : execution.application.HandleUnused
      (owner, .prepared (execution.application.publicView.bindingCount owner)))
    (serials : execution.network.SerialsBeforeNext)
    (players : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (granted : execution.application.serviceGrant = some event)
      (ready : execution.application.config.cut.Ready event)
      (timely : execution.application.WithinDeadline (runtime setup) event)
      (vacant : execution.application.accepted (.inr event) = none)
      (after : (application setup leaks).Execution),
      after ∈ ((sourceServicePolicy setup leaks wholeProfile owner (execution.recall owner)
        (execution.observe (application setup leaks) owner)).bind fun response =>
          (runtime setup).interactionStep leaks players network (.includeLatest event owner)
            (execution.respond (application setup leaks) owner response)).support →
      after.application.CandidatesRepresented ∧ after.application.AcceptedRecorded ∧
      ∃ choice ∈ (commitKernel profile (source.view owner)).support,
        SourceCheckpoint setup (commitSuccessor name guard source choice)
          (refs.cons (name := name) ⟨.inr event, outputEq⟩) (offset + 1)
          after.application.config ∧
        after.receipts = execution.receipts ++
          [((owner, execution.network.nextSerial owner), true)] := by
  intro index event outputEq granted ready timely vacant after supported
  let serial := execution.application.publicView.bindingCount owner
  have selected : reactiveFreshSlot (execution.observe
      (application setup leaks) owner).application = some serial :=
    prepared.freshSlot (runtime setup) leaks
  have candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh :=
    (prepared serial).mpr (Nat.le_refl _)
  have semantic := sourceServicePolicy_commit_checkpoint setup leaks fresh guard next wholeProfile
    profile refs source embedding refsBefore offset aligned execution checkpoint serial selected
      candidate unused serials players network granted ready timely vacant after supported
  have codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload := by
    change cast (congrArg (EventGraph.EventCode (graphLayout setup.program)) outputEq)
      ((toEventGraph setup.program).nodes event) = _
    simpa [event, index, compileRankedNodes] using aligned.graphSuffix.nodeEq index
  have node : nodeView (graph setup) event = .bind owner payload outputEq codeEq := by
    cases viewed : nodeView (graph setup) event with
    | sample otherPayload law kind code => cases kind.symm.trans outputEq
    | resolve other otherPayload binding checks kind code => cases kind.symm.trans outputEq
    | bind other otherPayload kind code =>
        obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj (kind.symm.trans outputEq)
        rfl
  have policy := sourceServicePolicy_commit setup leaks fresh guard next wholeProfile profile refs
    source embedding refsBefore offset aligned execution checkpoint.agrees checkpoint.history
      granted
  dsimp only at policy
  rw [policy, FinDist.bind_map] at supported
  obtain ⟨choice, _chosen, response⟩ :=
    Set.mem_iUnion₂.mp (FinDist.support_bind .. ▸ supported)
  have choiceEq := serviceDecision_binding_fresh (runtime setup) leaks execution owner event payload
    outputEq codeEq node serial selected candidate choice
  rw [choiceEq] at response
  exact ⟨(runtime setup).reactiveBinding_reserved_represented leaks execution owner event payload
      outputEq codeEq node choice serial represented ready timely candidate vacant unused serials
        players network after response,
    (runtime setup).reactiveBinding_reserved_recorded leaks execution owner event payload
      outputEq codeEq node choice recorded ready timely candidate vacant unused serials
        players network after response, semantic⟩

end Vegas.SourceProgram.RevealService
