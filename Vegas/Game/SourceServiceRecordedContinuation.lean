/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceContinuationBridge
import Vegas.Game.SourceServiceRecordedPlan
import Vegas.Game.SourceServiceSubmittedBinding

/-! # Owner visits after an already submitted binding

The authentic pending binding remains selected through every replay choice.
Once the binding has been recorded, the timed compiler uses replay-only laws
at all remaining visits. The application law at the next event boundary is
therefore independent of the owner's current legal response, and the generic
local comparison gives zero gain at every such owner site.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A binding output has the binding node code. -/
theorem binding_nodeView (setup : Setup (Player := Player) (L := L))
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload) :
    ∃ codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
        ((graph setup).nodes event) = .bind owner payload,
      nodeView (graph setup) event = .bind owner payload outputEq codeEq := by
  cases viewed : nodeView (graph setup) event with
  | sample other law kind code => cases kind.symm.trans outputEq
  | resolve other otherPayload binding checks kind code => cases kind.symm.trans outputEq
  | bind other otherPayload kind code =>
      obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj (kind.symm.trans outputEq)
      exact ⟨code, rfl⟩

variable [Fintype Player]

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

include approx in
/-- At an actual decision after the event's binding is recorded, every legal
current response of any player leaves the same configuration law at the next
event boundary. -/
theorem recorded_phase_invariant {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (owner : Player) (payload : L.Ty)
    (outputEq : (graph service.setup).outputLayout phase.event = .binding owner payload)
    (recorded : (runtime service.setup).eventRecorded service.leaks (execution.recall owner)
      phase.event = true)
    (first second : (application service.setup service.leaks).Action)
    (firstAllowed : first ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (secondAllowed : second ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second := by
  have owned := binding_actor service.setup phase.event owner payload outputEq
  obtain ⟨codeEq, node⟩ := binding_nodeView service.setup phase.event owner payload outputEq
  let id : MessageId Player :=
    (owner, Message.distinctAuthoredCount execution.network.ledger owner)
  let message : Message Player (WitnessedPacket (graph service.setup)) :=
    ⟨id, ⟨.commitment phase.event (owner, .prepared
      (execution.application.publicView.bindingCount owner)), none, some ⟨phase.event⟩⟩⟩
  obtain ⟨value, _, _, _, _, _, pending, packets, _, selected⟩ :=
    sourceService_recorded_binding_resources service.setup service.leaks service.bounds
      service.values service.capacity service.rosters service.opportunities.binding
      service.network who ⟨remaining, some who, execution⟩ trace rfl phase.event phase.ready
      owner payload outputEq codeEq node owned recorded
  have unpublished : message.id ∉ execution.network.ledger.map Message.id := by
    unfold reactiveLatest at selected
    split at selected
    · cases selected
    · rename_i packet found
      have good : packet.sender = owner ∧
          packet.payload.call.event? (graph service.setup) = some phase.event ∧
          (execution.observeEnvironment (application service.setup service.leaks)).Unpublished
            (application service.setup service.leaks) packet.id := by
        simpa only [decide_eq_true_eq] using List.find?_some found
      have same : packet.id = message.id := ReactiveApplication.Command.include.inj selected
      exact same ▸ good.2.2
  have transport (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)) :
      response = ⟨none⟩ := by
    have supported := service.menu.fullyMixed_response_support (initialLaw service.setup)
      service.planLength service.scheduler approx.players approx.covered approx.assessment
      approx.strategy approx.mixed who remaining execution trace response allowed
    exact sourceServiceTimedPolicy_recorded_transport service.setup service.leaks service.rosters
      approx.timing approx.profile phase.event owner owned execution phase.sole recorded
      execution rfl (List.Subset.refl _) who response supported
  have ending : rosterPhaseEnding service.setup phase.event =
      [.includeLatest phase.event owner] ++
        (List.replicate (phase.event.val + 1) .tick ++ [.expire phase.event]) := by
    simp only [rosterPhaseEnding, owned, List.append_assoc]
  have law (response : (application service.setup service.leaks).Action)
      (allowed : response ∈ service.menu.actions who (execution.recall who)
        (execution.observe (application service.setup service.leaks) who)) :=
    sourceService_recorded_response_application_law service.setup service.leaks service.rosters
      approx.timing approx.profile service.network phase.event owner owned execution phase.sole
      recorded message rfl rfl packets pending unpublished who response (transport response allowed)
      phase.visits (phase.event.val + 1)
  have applications := (law first firstAllowed).trans (law second secondAllowed).symm
  simp only [phaseConfigLaw, phaseLaw, DecisionPhase.tail, ending]
  simpa only [List.append_assoc, PMF.map_comp, Function.comp_def] using
    congrArg (PMF.map EventGraphRuntime.State.config) applications

open Classical in
/-- At an owner's information site after its binding is recorded, every local
lottery has the prescribed continuation law, for every belief over the site. -/
theorem recorded_comparison_eq (who : Player) (site : service.model.InformationSite who)
    (past : List (application service.setup service.leaks).PlayerEntry)
    (view : (application service.setup service.leaks).PlayerView)
    (observed : site.1 = some (past, view))
    {event : (graph service.setup).EventId} {payload : L.Ty}
    (outputEq : (graph service.setup).outputLayout event = .binding who payload)
    (readyView : view.application.publicView.EventReady event)
    (recorded : (runtime service.setup).eventRecorded service.leaks past event = true)
    (law : PMF (service.model.Choice who site.1)) :
    let comparison := service.model.assessmentComparisonWith (service.model.truncatedRunner
        service.fuel) service.readout
      approx.assessment who (site, (approx.assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  apply approx.comparison_eq_of_phase_invariant who site
  intro history remaining execution current info phase first second firstAllowed secondAllowed
  have input := Option.some.inj
    ((service.infoOf_decision history current).symm.trans (info.trans observed))
  have readyNow :=
    (congrArg (fun pair : List (application service.setup service.leaks).PlayerEntry ×
      (application service.setup service.leaks).PlayerView =>
        pair.2.application.publicView.EventReady event) input).mpr readyView
  have same : phase.event = event := (phase.sole.2 event readyNow).symm
  subst same
  have ownRecall : execution.recall who = past := congrArg Prod.fst input
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  exact approx.recorded_phase_invariant trace phase who payload outputEq
    (ownRecall ▸ recorded) first second firstAllowed secondAllowed

end TimedApproximant

end Vegas
