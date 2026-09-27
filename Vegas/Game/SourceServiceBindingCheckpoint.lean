/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingPhase
import Vegas.Game.SourceServiceCandidateStep

/-! # Dynamic source checkpoints after an entire binding roster

The source commitment kernel is executed after its earlier replay visits and
settled after all remaining foreign visits. Its actual supported endpoints
retain the source configuration relation and the dynamic candidate and accepted
handle invariants. The proof uses full application provenance, rather than
freezing either catalogue at initialization.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Finite Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Every actual endpoint has a supported original source successor and the
catalogue reconstruction properties required at subsequent source events. -/
theorem sourceServiceLastPolicy_commit_catalog_checkpoint
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup))
    (rosters : (graph setup).EventId → List Player)
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
    (prepared : ∀ who, execution.application.PreparedPrefix who)
    (unused : execution.application.HandleUnused
      (owner, .prepared (execution.application.publicView.bindingCount owner)))
    (serials : execution.network.SerialsBeforeNext)
    (accounted : ∀ who, execution.network.nextSerial who =
      execution.network.ledger.countP (fun message => message.sender = who))
    (published : execution.network.Satisfies fun message =>
      message.id ∈ execution.network.ledger.map Message.id)
    (network : (runtime setup).NetworkPolicy leaks)
    (visited remaining : List Player) (absent : owner ∉ remaining) :
    let index : Fin (eventCount (.commit name owner fresh guard next)) :=
      ⟨0, by simp [eventCount]⟩
    let event := embedding.event index
    let outputEq : (graph setup).outputLayout event = .binding owner payload := by
      change outputLayout setup.program (embedding.event index) = _
      simpa [index, outputLayout, eventCount] using embedding.layout_eq index
    ∀ (_position : rosters event = visited ++ owner :: remaining)
      (_granted : execution.application.serviceGrant = some event)
      (_ready : execution.application.config.cut.Ready event)
      (_timely : execution.application.WithinDeadline (runtime setup) event)
      (_vacant : execution.application.accepted (.inr event) = none)
      (_unsent : (runtime setup).eventRecorded leaks (execution.recall owner) event = false)
      (_counted : (execution.recall owner).length = rosterOffset setup rosters owner event)
      (final : (application setup leaks).Execution),
      final ∈ ((runtime setup).runInteractionPlan leaks
        (sourceServiceLastPolicy setup leaks rosters wholeProfile) network
        ((rosters event).map ServiceInstruction.player ++
          [.includeLatest event owner]) execution).support →
      final.application.CandidatesRepresented ∧ final.application.AcceptedRecorded ∧
      (∀ who, final.application.PreparedPrefix who) ∧
      (∀ who, final.network.nextSerial who =
        final.network.ledger.countP (fun message => message.sender = who)) ∧
      final.network.Satisfies (fun message => message.id ∈ final.network.ledger.map Message.id) ∧
      ∃ choice ∈ (commitKernel profile (source.view owner)).support,
        SourceCheckpoint setup (commitSuccessor name guard source choice)
          (refs.cons (name := name) ⟨.inr event, outputEq⟩) (offset + 1)
          final.application.config ∧
        final.receipts = execution.receipts ++
          [((owner, execution.network.nextSerial owner), true)] := by
  intro index event outputEq position granted ready timely vacant unsent counted final reached
  let app := application setup leaks
  let serial := execution.application.publicView.bindingCount owner
  have selected : reactiveFreshSlot (execution.observe app owner).application = some serial :=
    (prepared owner).freshSlot (runtime setup) leaks
  have candidate : execution.application.candidates.lookup (owner, .prepared serial) = .fresh :=
    (prepared owner serial).mpr (Nat.le_refl _)
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
  have owned : (graph setup).actor? event = some owner := by
    change (toEventGraph setup.program).actor? event = some owner
    simpa [event, index, eventOwner?, eventCount] using aligned.actorEq index
  obtain ⟨before, immediate, applicationEq, ledgerEq, receiptsEq, countersEq, beforeSerials,
    included, finalApplication, finalLedger, finalReceipts, finalCounters, finalPublished⟩ :=
      sourceServiceLastPolicy_binding_provenance setup leaks bounds rosters wholeProfile network
        execution event owner payload outputEq codeEq node granted owned ready serial selected
          candidate serials published visited remaining absent position counted unsent final reached
  have beforeCheckpoint : SourceCheckpoint setup source refs offset before.application.config := by
    rw [applicationEq]
    exact checkpoint
  have beforeRepresented : before.application.CandidatesRepresented := by
    rw [applicationEq]
    exact represented
  have beforeRecorded : before.application.AcceptedRecorded := by
    rw [applicationEq]
    exact recorded
  have beforePrepared : ∀ who, before.application.PreparedPrefix who := by
    rw [applicationEq]
    exact prepared
  have beforeAccounted : ∀ who, before.network.nextSerial who =
      before.network.ledger.countP (fun message => message.sender = who) := by
    rw [countersEq, ledgerEq]
    exact accounted
  have beforeUnused : before.application.HandleUnused
      (owner, .prepared (before.application.publicView.bindingCount owner)) := by
    rw [applicationEq]
    exact unused
  have beforeGrant : before.application.serviceGrant = some event := by
    rw [applicationEq]
    exact granted
  have beforeReady : before.application.config.cut.Ready event := by
    rw [applicationEq]
    exact ready
  have beforeTimely : before.application.WithinDeadline (runtime setup) event := by
    rw [applicationEq]
    exact timely
  have beforeVacant : before.application.accepted (.inr event) = none := by
    rw [applicationEq]
    exact vacant
  have completed := sourceServicePolicy_commit_catalog_checkpoint setup leaks fresh guard next
    wholeProfile profile refs source embedding refsBefore offset aligned before beforeCheckpoint
      beforeRepresented beforeRecorded beforePrepared beforeUnused beforeSerials beforeAccounted
      (fun _ => app.replayPolicy) network beforeGrant beforeReady beforeTimely beforeVacant
        immediate included
  refine ⟨?_, ?_, ?_, ?_, finalPublished, ?_⟩
  · rw [finalApplication]
    exact completed.1
  · rw [finalApplication]
    exact completed.2.1
  · rw [finalApplication]
    exact completed.2.2.1
  · rw [finalCounters, finalLedger]
    exact completed.2.2.2.1
  · simpa only [finalApplication, finalReceipts, receiptsEq, countersEq]
      using completed.2.2.2.2

end Vegas.SourceProgram.RevealService
