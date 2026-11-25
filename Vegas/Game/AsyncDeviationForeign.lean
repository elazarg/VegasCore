module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.SourceServiceFirstTurnCompletion
public import Vegas.Game.SourceServiceDeviationChoice
public import Vegas.Game.SourceServiceCanonicalSlots
public import Interaction.ReactiveRoundCongruence
public import Vegas.Pending.EventActivationOrigin
public import Vegas.Pending.ForeignPublicationTraffic
public import Vegas.Pending.EventBindingInvariant
public import Vegas.Pending.ReactiveGuardedResponse

@[expose] public section

/-! # Foreign source choices and native traffic

An honest foreign owner decides once at its first ready callback. The focal
player's traffic is compared through actual native rounds and automatic completion;
public omission stays distinct from an accepted opaque binding. The comparison
uses actual recall, initialized binding provenance and the sole native executor.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory.Math.Probability Interaction EventGraphRuntime EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies} {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Away from an unrecorded first turn that still fits the deadline, the
decided policy is silent. -/
theorem decidedTurnPolicy_closed {bound : (serviceGraph setup deps).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup deps).EventId}
    (action : (serviceGraph setup deps).Action event)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (selected : execution.application.publicView.ownTurn? owner = some event)
    (closed : ¬ (ownerTurns owner event execution = 0 ∧
      (eventRecorded (serviceTimeouts setup deps duration)) leaks (execution.logs owner) event =
        false ∧
      execution.application.publicView.InclusionFitsDeadline (serviceTimeouts setup deps duration)
        bound event)) :
    decidedTurnPolicy setup leaks bound owner event action (execution.logs owner)
        (execution.observe (serviceApplication setup deps duration leaks) owner) =
      PMF.pure ⟨none⟩ := by
  have turn := serviceTurn_of_turn execution selected
  unfold decidedTurnPolicy
  by_cases first : ownerTurns owner event execution = 0
  · rw [(serviceApplication setup deps duration leaks).turnScheduledPolicy_selected _ (0 : Fin 1)
      _ _ _ _ (by rw [turn, first]; rfl)]
    unfold fixedOpportunity
    by_cases recorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
        (execution.logs owner) event = true
    · simp only [recorded, ↓reduceIte, ReactiveApplication.silentPolicy_apply]
    · have unrecorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
          (execution.logs owner) event = false := by simpa using recorded
      have late : ¬ execution.application.publicView.InclusionFitsDeadline
          (serviceTimeouts setup deps duration) bound event := fun fits =>
        closed ⟨first, unrecorded, fits⟩
      have lateView : ¬ (execution.observe (serviceApplication setup deps duration leaks)
          owner).application.publicView.InclusionFitsDeadline
            (serviceTimeouts setup deps duration) bound event := late
      simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, lateView,
        ReactiveApplication.silentPolicy_apply]
  · rw [(serviceApplication setup deps duration leaks).turnScheduledPolicy_unselected _ _ _ _ _ _
      (by
        intro slot chosen
        rw [turn]
        intro equal
        exact first ((Option.some.inj equal).trans
          ((Fin.val_eq_zero slot).trans (by rfl))))]
    rfl

/-- At an unrecorded first turn, the decided policy is its opportunity. -/
theorem decidedTurnPolicy_open {bound : (serviceGraph setup deps).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup deps).EventId}
    (action : (serviceGraph setup deps).Action event)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (selected : execution.application.publicView.ownTurn? owner = some event)
    (first : ownerTurns owner event execution = 0) :
    decidedTurnPolicy setup leaks bound owner event action (execution.logs owner)
        (execution.observe (serviceApplication setup deps duration leaks) owner) =
      fixedOpportunity (serviceTimeouts setup deps duration) leaks
        bound owner event action (execution.logs owner)
        (execution.observe (serviceApplication setup deps duration leaks) owner) := by
  have turn := serviceTurn_of_turn execution selected
  unfold decidedTurnPolicy
  rw [(serviceApplication setup deps duration leaks).turnScheduledPolicy_selected _ (0 : Fin 1)
    _ _ _ _ (by rw [turn, first]; rfl)]

/-- An opportunity that transmits a given decision. -/
theorem decidedOpportunity_transmits {bound : (serviceGraph setup deps).EventId → Nat}
    {owner : Player} {event : (serviceGraph setup deps).EventId}
    (action : (serviceGraph setup deps).Action event)
    (execution : (serviceApplication setup deps duration leaks).Execution)
    (unrecorded : (eventRecorded (serviceTimeouts setup deps duration)) leaks
      (execution.logs owner) event = false)
    (fits : execution.application.publicView.InclusionFitsDeadline
      (serviceTimeouts setup deps duration) bound event)
    (material : (serviceApplication setup deps duration leaks).Submission)
    (decision : (canonicalServiceDecision (serviceTimeouts setup deps duration)) leaks owner
      (execution.logs owner) (execution.observe (serviceApplication setup deps duration leaks)
        owner) event action = ⟨some material⟩) :
    fixedOpportunity (serviceTimeouts setup deps duration) leaks
      bound owner event action (execution.logs owner)
        (execution.observe (serviceApplication setup deps duration leaks) owner) =
      PMF.pure ⟨some material⟩ := by
  have fitsView : (execution.observe (serviceApplication setup deps duration leaks)
      owner).application.publicView.InclusionFitsDeadline (serviceTimeouts setup deps duration)
        bound event := fits
  unfold fixedOpportunity
  simp only [unrecorded, Bool.false_eq_true, ↓reduceIte, fitsView, decision, reduceCtorEq]



theorem binding_response_matched
    {horizon leftRemaining rightRemaining : Nat}
    {scheduler : (serviceApplication setup deps duration leaks).Scheduler}
    {bound : (serviceGraph setup deps).EventId → Nat}
    {event : (serviceGraph setup deps).EventId} {owner focal : Player} {payload : L.Ty}
    (ownerSolitary : (serviceGraph setup deps).OwnerSolitary event)
    (foreign : owner ≠ focal)
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
      ((serviceGraph setup deps).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup deps) event = .bind owner payload outputEq codeEq)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    {left right : (serviceApplication setup deps duration leaks).Execution}
    (same : foreignReadout (leaks := leaks) focal owner event left =
      foreignReadout (leaks := leaks) focal owner event right)
    (leftTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨leftRemaining + 1, none, left⟩))
    (rightTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨rightRemaining + 1, none, right⟩))
    (leftReady : left.application.config.cut.Ready event)
    (rightReady : right.application.config.cut.Ready event)
    (leftOwn : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks left owner)
    (leftSlots : EventGraphRuntime.CanonicalSlotsUsed
      (serviceTimeouts setup deps duration) leaks left owner)
    (rightOwn : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks right owner)
    (rightSlots : EventGraphRuntime.CanonicalSlotsUsed
      (serviceTimeouts setup deps duration) leaks right owner)
    (selected : (.activate owner : (serviceApplication setup deps duration leaks).Command) ∈
      (scheduler left.environmentRecall
        (left.observeEnvironment (serviceApplication setup deps duration leaks))).support)
    (sample : Finset (MessageId Player))
    (sampled : sample ∈ ((serviceApplication setup deps duration leaks).observePending owner
      left.network.pending).support) :
    let leftActive := left.sampledActivation (serviceApplication setup deps duration leaks)
      owner sample
    let rightActive := right.sampledActivation (serviceApplication setup deps duration leaks)
      owner sample
    ∃ leftResponse rightResponse,
      decidedTurnPolicy setup leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) leftChoice)
        (leftActive.logs owner) (leftActive.observe
          (serviceApplication setup deps duration leaks) owner) = PMF.pure leftResponse ∧
      decidedTurnPolicy setup leaks bound owner event
        (cast (congrArg EventField.Action outputEq.symm) rightChoice)
        (rightActive.logs owner) (rightActive.observe
          (serviceApplication setup deps duration leaks) owner) = PMF.pure rightResponse ∧
      (submittedEvent? (serviceTimeouts setup deps duration)) leaks leftResponse =
        (submittedEvent? (serviceTimeouts setup deps duration)) leaks rightResponse ∧
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
        (leftActive.respond (serviceApplication setup deps duration leaks) owner leftResponse) =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal
        (rightActive.respond (serviceApplication setup deps duration leaks) owner
          rightResponse) := by
  rw [serviceInitialLaw_eq_inputs setup] at leftTrace rightTrace
  exact EventGraphRuntime.binding_response_matched (timeouts := serviceTimeouts setup deps duration)
    ownerSolitary foreign outputEq codeEq node leftChoice rightChoice admitted same
    leftTrace rightTrace leftReady rightReady leftOwn leftSlots rightOwn rightSlots selected
    sample sampled

/-- Decided foreign bindings of equal admission, run until the binding completes from
equal starting readouts, give equal stopped readout laws. -/
theorem binding_stopped_readout_congr
    (serial : (serviceGraph setup deps).ActorSerial)
    {horizon count leftRemaining rightRemaining : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (bound : (serviceGraph setup deps).EventId → Nat)
    {event : (serviceGraph setup deps).EventId} {owner : Player} {payload : L.Ty}
    (foreign : owner ≠ focal)
    (outputEq : (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup deps).layout) outputEq)
      ((serviceGraph setup deps).nodes event) = .bind owner payload)
    (node : nodeView (serviceGraph setup deps) event = .bind owner payload outputEq codeEq)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    (alone : ∀ (cut : (serviceGraph setup deps).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (leftStart rightStart : (serviceApplication setup deps duration leaks).Execution)
    (leftTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftReady : leftStart.application.config.cut.Ready event)
    (rightReady : rightStart.application.config.cut.Ready event)
    (leftOwn : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks leftStart owner)
    (leftSlots : EventGraphRuntime.CanonicalSlotsUsed
      (serviceTimeouts setup deps duration) leaks leftStart owner)
    (rightOwn : OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks rightStart owner)
    (rightSlots : EventGraphRuntime.CanonicalSlotsUsed
      (serviceTimeouts setup deps duration) leaks rightStart owner)
    (same : foreignReadout (leaks := leaks) focal owner event leftStart =
      foreignReadout (leaks := leaks) focal owner event rightStart) :
    ((serviceApplication setup deps duration leaks).runUntil scheduler
      (Function.update
        (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) leftChoice)))
      (fun final => event ∈ final.application.config.cut.completed) count leftStart).map
        (foreignReadout (leaks := leaks) focal owner event) =
    ((serviceApplication setup deps duration leaks).runUntil scheduler
      (Function.update
        (focalPlayers (serviceTimeouts setup deps duration) leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) rightChoice)))
      (fun final => event ∈ final.application.config.cut.completed) count rightStart).map
        (foreignReadout (leaks := leaks) focal owner event) := by
  rw [serviceInitialLaw_eq_inputs setup] at leftTrace rightTrace
  exact EventGraphRuntime.binding_stopped_readout_congr
    (timeouts := serviceTimeouts setup deps duration) serial scheduler focal deviation bound
    foreign outputEq codeEq node leftChoice rightChoice admitted alone leftStart rightStart
    leftTrace rightTrace leftReady rightReady leftOwn leftSlots rightOwn rightSlots same

/-- An honest foreign binding has the same focal traffic law at equal public
admission choices and equal initial focal traffic. -/
theorem sourceService_binding_traffic_congr
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup timeouts leaks).Policy) (foreign : owner ≠ focal)
    (event : setup.informationGraph.EventId) {payload : L.Ty}
    (outputEq : setup.informationGraph.outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
      (setup.informationGraph.nodes event) = .bind owner payload)
    (node : nodeView setup.informationGraph event = .bind owner payload outputEq codeEq)
    (leftChoice rightChoice : Option (PublicationResult (L.Val payload)))
    (admitted : leftChoice.isSome = rightChoice.isSome)
    (left right : (application setup timeouts leaks).Execution)
    (leftBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val left)
    (rightBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val right)
    (leftBounded : left.environmentRecall.length ≤ horizon)
    (rightBounded : right.environmentRecall.length ≤ horizon)
    (same : (bindingTraffic timeouts) leaks focal left = (bindingTraffic timeouts) leaks focal
      right) :
    (((application setup timeouts leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) leftChoice)))
      (fun final => event ∈ final.application.config.cut.completed) horizon left).map
        ((bindingTraffic timeouts) leaks focal)) =
    (((application setup timeouts leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) rightChoice)))
      (fun final => event ∈ final.application.config.cut.completed) horizon right).map
        ((bindingTraffic timeouts) leaks focal)) := by
  have serial : setup.informationGraph.ActorSerial :=
    (toInformationGraph_barrierOrdered setup.program).revealRelaxedOrdered.actorSerial
  have solitary : setup.informationGraph.Solitary event := by
    intro cut other otherReady ready
    exact setup.informationGraph.sequentialize_ready_unique cut otherReady ready
  let players := Function.update
    (serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks bound turns
      (firstTurnTiming setup turns) wholeProfile) focal deviation
  have leftPrefix : PrefixBoundary (timeouts := timeouts) (leaks := leaks)
      ((setup.initialLaw.map setup.eventInputs).map EventGraphRuntime.State.initial)
      scheduler players event.val left := by
    simpa only [← serviceInitialLaw_eq_inputs setup] using leftBoundary
  have rightPrefix : PrefixBoundary (timeouts := timeouts) (leaks := leaks)
      ((setup.initialLaw.map setup.eventInputs).map EventGraphRuntime.State.initial)
      scheduler players event.val right := by
    simpa only [← serviceInitialLaw_eq_inputs setup] using rightBoundary
  exact EventGraphRuntime.foreign_binding_fixed_traffic_congr
    (timeouts := timeouts) (turns := turns) serial scheduler bound
    (compileEventProfile setup.program wholeProfile) focal owner deviation foreign event solitary
    outputEq codeEq node leftChoice rightChoice admitted left right leftPrefix rightPrefix
    leftBounded rightBounded same

/-- Before the ready event completes, fixing its owner's first source choice
agrees with the decided client while every other honest owner is idle. -/
theorem sourceService_foreign_fixedRun
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (focal : Player)
    (deviation : (application setup timeouts leaks).Policy)
    (owner : Player) (event : setup.informationGraph.EventId)
    (owned : setup.informationGraph.actor? event = some owner)
    (action : setup.informationGraph.Action event)
    (execution : (application setup timeouts leaks).Execution)
    (ready : execution.application.config.cut.Ready event) :
    let players := Function.update
      (serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) profile) focal deviation
    let baseline := serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks
      bound turns
      (firstTurnTiming setup turns) profile
    let member := fun past view =>
      if turnIndex timeouts leaks owner event past
        view = some 0 then
        fixedOpportunity timeouts leaks bound owner event action past view
      else baseline owner past view
    ((application setup timeouts leaks).runUntilHorizon scheduler
      (Function.update players owner member)
      (fun final => event ∈ final.application.config.cut.completed) horizon execution) =
    (application setup timeouts leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event action))
      (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
  exact EventGraphRuntime.foreign_firstTurn_fixedRun
    (timeouts := timeouts) (leaks := leaks) scheduler bound turns
    (compileEventProfile setup.program profile) focal deviation owner event owned
    (by
      intro cut other otherReady ready
      exact setup.informationGraph.sequentialize_ready_unique cut otherReady ready)
    action execution ready

/-- An honest foreign owner's stopped native law is its source head mixture
of decided native clients against the arbitrary focal policy. -/
theorem sourceService_foreign_mixture
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (focal : Player)
    (deviation : (application setup timeouts leaks).Policy)
    (owner : Player) (event : setup.informationGraph.EventId)
    (owned : setup.informationGraph.actor? event = some owner) (foreign : owner ≠ focal)
    (execution : (application setup timeouts leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns
        (firstTurnTiming setup turns) profile) focal deviation) event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon)
    (law : PMF (setup.informationGraph.Action event))
    (callback : ∀ current : (application setup timeouts leaks).Execution,
      current.application.config = execution.application.config →
      sourceServiceCanonicalPolicy setup timeouts leaks profile owner (current.logs owner)
        (current.observe (application setup timeouts leaks) owner) =
      law.map (fun action => (canonicalServiceDecision timeouts) leaks owner (current.logs owner)
        (current.observe (application setup timeouts leaks) owner) event action)) :
    let players := Function.update
      (serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks bound turns
        (firstTurnTiming setup turns) profile) focal deviation
    ((application setup timeouts leaks).runUntilHorizon scheduler players
      (fun final => event ∈ final.application.config.cut.completed) horizon execution) =
    law.bind fun action => (application setup timeouts leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event action))
      (fun final => event ∈ final.application.config.cut.completed) horizon execution := by
  intro players
  let baseline := serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks
    bound turns
    (firstTurnTiming setup turns) profile
  have follows : players owner = baseline owner := Function.update_of_ne foreign _ _
  have mixed := sourceService_firstTurn_mixture timeouts leaks scheduler bound profile owner event
    owned players follows execution boundary bounded law callback
  rw [mixed]
  apply bind_congr_on_support _
  intro action _chosen
  exact sourceService_foreign_fixedRun timeouts leaks scheduler bound turns profile focal deviation
    owner event owned action execution (boundary.ordered.ready event.isLt)

/-- An honest true disclosure of the same bound value has equal stopped
focal traffic from equal initial focal traffic at actual initialized boundaries. -/
theorem sourceService_opening_traffic_congr
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup timeouts leaks).Policy) (foreign : owner ≠ focal)
    (event : setup.informationGraph.EventId) {payload : L.Ty}
    (binding : FieldRef setup.informationGraph.layout (.binding owner payload))
    (checks : List (GuardCheck setup.informationGraph.layout payload))
    (outputEq : setup.informationGraph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
      (setup.informationGraph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView setup.informationGraph event =
      .resolve owner payload binding checks outputEq codeEq)
    (left right : (application setup timeouts leaks).Execution)
    (leftBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val left)
    (rightBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val right)
    (leftBounded : left.environmentRecall.length ≤ horizon)
    (rightBounded : right.environmentRecall.length ≤ horizon)
    (value : L.Val payload)
    (leftStored : binding.get? left.application.config.store = some (.success value))
    (rightStored : binding.get? right.application.config.store = some (.success value))
    (same : (bindingTraffic timeouts) leaks focal left = (bindingTraffic timeouts) leaks focal
      right) :
    (((application setup timeouts leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) true)))
      (fun final => event ∈ final.application.config.cut.completed) horizon left).map
        ((bindingTraffic timeouts) leaks focal)) =
    (((application setup timeouts leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) true)))
      (fun final => event ∈ final.application.config.cut.completed) horizon right).map
        ((bindingTraffic timeouts) leaks focal)) := by
  have serial : setup.informationGraph.ActorSerial :=
    (toInformationGraph_barrierOrdered setup.program).revealRelaxedOrdered.actorSerial
  have solitary : setup.informationGraph.Solitary event := by
    intro cut other otherReady ready
    exact setup.informationGraph.sequentialize_ready_unique cut otherReady ready
  let players := Function.update
    (serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks bound turns
      (firstTurnTiming setup turns) wholeProfile) focal deviation
  have leftPrefix : PrefixBoundary (timeouts := timeouts) (leaks := leaks)
      ((setup.initialLaw.map setup.eventInputs).map EventGraphRuntime.State.initial)
      scheduler players event.val left := by
    simpa only [← serviceInitialLaw_eq_inputs setup] using leftBoundary
  have rightPrefix : PrefixBoundary (timeouts := timeouts) (leaks := leaks)
      ((setup.initialLaw.map setup.eventInputs).map EventGraphRuntime.State.initial)
      scheduler players event.val right := by
    simpa only [← serviceInitialLaw_eq_inputs setup] using rightBoundary
  exact EventGraphRuntime.foreign_publication_fixed_traffic_congr (timeouts := timeouts)
    serial scheduler bound turns (firstTurnTiming setup turns)
    (compileEventProfile setup.program wholeProfile) focal owner deviation foreign event solitary
    binding checks outputEq codeEq node true left right (fun _ => ⟨value, leftStored, rightStored⟩)
    leftPrefix rightPrefix leftBounded rightBounded same

/-- An honest false disclosure emits no opening at its actual initialized
boundary, so its stopped focal traffic depends only on initial focal traffic. -/
theorem sourceService_withholding_traffic_congr
    (timeouts : EventTimeouts setup.informationGraph)
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket setup.informationGraph))
    {horizon : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (bound : setup.informationGraph.EventId → Nat) (turns : Nat)
    (wholeProfile : BehavioralProfile setup.program) (focal owner : Player)
    (deviation : (application setup timeouts leaks).Policy) (foreign : owner ≠ focal)
    (event : setup.informationGraph.EventId) {payload : L.Ty}
    (binding : FieldRef setup.informationGraph.layout (.binding owner payload))
    (checks : List (GuardCheck setup.informationGraph.layout payload))
    (outputEq : setup.informationGraph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode setup.informationGraph.layout) outputEq)
      (setup.informationGraph.nodes event) = .resolve owner payload binding checks)
    (node : nodeView setup.informationGraph event =
      .resolve owner payload binding checks outputEq codeEq)
    (left right : (application setup timeouts leaks).Execution)
    (leftBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val left)
    (rightBoundary : CompletionBoundary setup leaks scheduler
      (Function.update (serviceTurnPolicy setup setup.informationDependencies timeouts.duration
        leaks bound turns
        (firstTurnTiming setup turns) wholeProfile) focal deviation) event.val right)
    (leftBounded : left.environmentRecall.length ≤ horizon)
    (rightBounded : right.environmentRecall.length ≤ horizon)
    (same : (bindingTraffic timeouts) leaks focal left = (bindingTraffic timeouts) leaks focal
      right) :
    (((application setup timeouts leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) false)))
      (fun final => event ∈ final.application.config.cut.completed) horizon left).map
        ((bindingTraffic timeouts) leaks focal)) =
    (((application setup timeouts leaks).runUntilHorizon scheduler
      (Function.update
        (focalPlayers timeouts leaks focal deviation) owner
        (decidedTurnPolicy setup leaks bound owner event
          (cast (congrArg EventField.Action outputEq.symm) false)))
      (fun final => event ∈ final.application.config.cut.completed) horizon right).map
        ((bindingTraffic timeouts) leaks focal)) := by
  have serial : setup.informationGraph.ActorSerial :=
    (toInformationGraph_barrierOrdered setup.program).revealRelaxedOrdered.actorSerial
  have solitary : setup.informationGraph.Solitary event := by
    intro cut other otherReady ready
    exact setup.informationGraph.sequentialize_ready_unique cut otherReady ready
  let players := Function.update
    (serviceTurnPolicy setup setup.informationDependencies timeouts.duration leaks bound turns
      (firstTurnTiming setup turns) wholeProfile) focal deviation
  have leftPrefix : PrefixBoundary (timeouts := timeouts) (leaks := leaks)
      ((setup.initialLaw.map setup.eventInputs).map EventGraphRuntime.State.initial)
      scheduler players event.val left := by
    simpa only [← serviceInitialLaw_eq_inputs setup] using leftBoundary
  have rightPrefix : PrefixBoundary (timeouts := timeouts) (leaks := leaks)
      ((setup.initialLaw.map setup.eventInputs).map EventGraphRuntime.State.initial)
      scheduler players event.val right := by
    simpa only [← serviceInitialLaw_eq_inputs setup] using rightBoundary
  exact EventGraphRuntime.foreign_publication_fixed_traffic_congr (timeouts := timeouts)
    serial scheduler bound turns (firstTurnTiming setup turns)
    (compileEventProfile setup.program wholeProfile) focal owner deviation foreign event solitary
    binding checks outputEq codeEq node false left right (fun impossible => by cases impossible)
    leftPrefix rightPrefix leftBounded rightBounded same

end Vegas
