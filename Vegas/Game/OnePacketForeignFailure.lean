module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketMainActivation
public import Vegas.Game.OnePacketForeignActivation
public import Vegas.Game.OnePacketMainResponseSafety
public import Vegas.Game.OnePacketCountedService
public import Vegas.Game.OnePacketForeignSubmission
public import Vegas.Pending.ReactiveCompletion
public import Vegas.Game.OnePacketFilteredPrefix

@[expose] public section

/-! # First foreign failures under native counted pointwise service

Every service input concerns an actual clear counted prefix. Failing exits
identify a genuine future non-main foreign response without a recovery-wide
or unrestricted native raw service contract.
-/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {timeouts : EventTimeouts (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}

/-- A first foreign public failure before focal debt remembers an actual
non-main foreign first response after the comparison's focal source turn.
Both expiry and consumed opening traffic are attributed from actual execution. -/
theorem foreign_nonmain_prefix_of_firstFailure
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (start : (application setup timeouts leaks).Control)
    (startTrace : (onePacketProtocol setup timeouts leaks bounds horizon
      scheduler).Trace (some start))
    (remaining : Nat) (execution : (application setup timeouts leaks).Execution)
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon
      scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current failedEvent : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : execution.application.config.defaulted = ∅)
    (regular : RegularTrace setup timeouts leaks bounds horizon
      scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? failedEvent = some owner)
    (command : (application setup timeouts leaks).Command) (next : (application setup timeouts
      leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup timeouts leaks)
      command).support)
    (target : (onePacketProtocol setup timeouts leaks bounds horizon
      scheduler).Trace
        (some ⟨remaining, command.actor? (application setup timeouts leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure failedEvent) :
    ∃ (event : (graph setup).EventId) (before : (application setup timeouts leaks).Control)
      (prior : (onePacketProtocol setup timeouts leaks bounds horizon
        scheduler).Trace (some before))
      (response : (application setup timeouts leaks).Action)
      (joint : Player → Option (application setup timeouts leaks).Action)
      (legal : (onePacketProtocol setup timeouts leaks bounds horizon
        scheduler).Legal
          (some before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup timeouts leaks) owner response⟩ ∈
        ((onePacketProtocol setup timeouts leaks bounds horizon
          scheduler).step
            (some before) ⟨joint, legal⟩).support),
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) target ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup timeouts leaks owner (some (before.execution.logs owner,
        before.execution.observe (application setup timeouts leaks) owner)) = some event ∧
      (∀ previous ∈ before.execution.logs owner,
        ¬ ActivatedAt setup timeouts leaks owner event previous) ∧
      responseChoice setup timeouts leaks bounds (initialLaw setup) horizon
        scheduler owner
        (some (before.execution.logs owner,
          before.execution.observe (application setup timeouts leaks) owner)) response ∉
        (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon
          scheduler source owner
          (some (before.execution.logs owner,
            before.execution.observe (application setup timeouts leaks) owner))).support := by
  have rawPrior := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup)
    horizon scheduler trace
  have rawTarget := (bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup)
    horizon scheduler target
  have initialEq : initialLaw setup = (setup.initialLaw.map setup.eventInputs).map
      (EventGraphRuntime.State.initial (graph := graph setup)) :=
    serviceInitialLaw_eq_inputs (mode := .sequential) setup
  rw [initialEq] at rawPrior rawTarget
  have priorEvidence := ExclusionEvidence.history timeouts leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler rawPrior
  have targetEvidence := ExclusionEvidence.history timeouts leaks
    (setup.initialLaw.map setup.eventInputs) horizon scheduler rawTarget
  have active : owner ∉ execution.application.config.defaulted := by simp [clear]
  have introduced : owner ∈ next.application.config.defaulted :=
    (targetEvidence.defaulted_zero owner).mpr ⟨failedEvent, owned, failed⟩
  obtain ⟨event, owned, ready, failed, origin⟩ := ExclusionEvidence.new_default_origin timeouts
    leaks execution next command reached owner active introduced priorEvidence
  have extracted : ∃ (before : (application setup timeouts leaks).Control)
      (prior : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some
        before))
      (response : (application setup timeouts leaks).Action)
      (joint : Player → Option (application setup timeouts leaks).Action)
      (legal : (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Legal
        (some before) joint)
      (realized : some ⟨before.remaining, none,
        before.execution.respond (application setup timeouts leaks) owner response⟩ ∈
        ((onePacketProtocol setup timeouts leaks bounds horizon scheduler).step
          (some before) ⟨joint, legal⟩).support),
      TracePrefix startTrace prior ∧ TracePrefix (prior.extend joint legal realized) trace ∧
      before.actor = some owner ∧ joint owner = some response ∧
      pendingEvent setup timeouts leaks owner (some (before.execution.logs owner,
        before.execution.observe (application setup timeouts leaks) owner)) = some event ∧
      ∀ previous ∈ before.execution.logs owner,
        ¬ ActivatedAt setup timeouts leaks owner event previous := by
    rcases origin with ⟨message, member, _included, sender, named⟩ | ⟨_, entered, activated, due⟩
    · have recorded := eventRecorded_of_pending setup leaks
          ((bounds.onePacketMenu timeouts leaks).toRawTrace (initialLaw setup) horizon
            scheduler trace) owner event message
        member sender named
      exact foreign_firstActivation_prefix_of_recorded (timeouts := timeouts) wellFormed source
        focal owner different
        start ⟨remaining + 1, none, execution⟩ startTrace trace startPrefix current event turn clear
        regular notOwed owned ready recorded
    · exact foreign_firstActivation_prefix_of_due (timeouts := timeouts) wellFormed source focal
        owner different timely
        start ⟨remaining + 1, none, execution⟩ startTrace trace
        (opportunity ⟨remaining + 1, none, execution⟩ trace clear) startPrefix current event turn
        clear regular notOwed rfl owned ready entered activated due
  obtain ⟨before, prior, response, joint, legal, realized, future, afterPrefix, acting, chosen,
    pending, never⟩ := extracted
  have priorPrefix : TracePrefix prior trace :=
    (TracePrefix.extend .refl joint legal realized).trans afterPrefix
  obtain ⟨earlierClear, earlierRegular, earlierNotOwed⟩ := clear_regular_notOwes_of_tracePrefix
    (timeouts := timeouts)
    wellFormed source focal owner different prior trace priorPrefix clear regular notOwed
  have targetPrefix := afterPrefix.trans tracePrefix
  have localLegal := legal.2 owner
  rw [chosen] at localLegal
  have offered : response ∈ bounds.onePacketActions timeouts leaks owner
      (before.execution.logs owner) (before.execution.observe (application setup timeouts leaks)
        owner) :=
    localLegal.2
  have selected : (responseChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
      owner (some (before.execution.logs owner,
        before.execution.observe (application setup timeouts leaks) owner)) response).1 = some
          response := by
    simp only [responseChoice, dite_eq_left offered]
  have notMain : responseChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler
    owner
      (some (before.execution.logs owner,
        before.execution.observe (application setup timeouts leaks) owner)) response ∉
      (honestChoice setup timeouts leaks bounds (initialLaw setup) horizon scheduler source owner
        (some (before.execution.logs owner,
          before.execution.observe (application setup timeouts leaks) owner))).support := by
    rcases before with ⟨responsesLeft, actor, earlierExecution⟩
    dsimp only at acting
    subst actor
    have fits := firstActivation_inclusionFits_of_counted_opportunity setup timeouts leaks bounds
      horizon
      scheduler delay bound opportunity timely prior rfl earlierClear event
      (pendingEvent_spec (timeouts := timeouts) pending).1 never
    have settles := settlesFreshCalls_counted_clear_environment setup timeouts leaks bounds horizon
      scheduler
      bound inclusion owner event owned remaining execution trace clear command next reached
    exact firstResponse_not_main_of_publicFailure_of_settles (timeouts := timeouts) bounds
      wellFormed covers capacity
      source
      focal horizon scheduler bound prior earlierClear earlierRegular earlierNotOwed event pending
      fits _ response selected (prior.extend joint legal realized) next settles _ rfl target
      targetPrefix failed
  exact ⟨event, before, prior, response, joint, legal, realized, future, targetPrefix, acting,
    chosen,
    pending, never, notMain⟩

/-- A first foreign failure violates the future first-activation main condition. -/
theorem firstForeignFailure_not_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {horizon : Nat} {scheduler : (application setup timeouts leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      OpportunityAt timeouts leaks control.execution delay)
    (inclusion : ∀ control : (application setup timeouts leaks).Control,
      (onePacketProtocol setup timeouts leaks bounds horizon scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt timeouts leaks control.execution bound)
    (timely : (AsyncTimely timeouts) delay bound)
    (start : (application setup timeouts leaks).Control)
    (startTrace : (onePacketProtocol setup timeouts leaks bounds horizon
      scheduler).Trace (some start))
    (remaining : Nat) (execution : (application setup timeouts leaks).Execution)
    (trace : (onePacketProtocol setup timeouts leaks bounds horizon
      scheduler).Trace
        (some ⟨remaining + 1, none, execution⟩))
    (startPrefix : TracePrefix startTrace trace)
    (current event : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : execution.application.config.defaulted = ∅)
    (regular : RegularTrace setup timeouts leaks bounds horizon
      scheduler source focal trace)
    (notOwed : ∀ point, decodedPoint setup execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (owned : (graph setup).actor? event = some owner)
    (command : (application setup timeouts leaks).Command) (next : (application setup timeouts
      leaks).Execution)
    (reached : next ∈ (execution.environmentStep (application setup timeouts leaks)
      command).support)
    (target : (onePacketProtocol setup timeouts leaks bounds horizon
      scheduler).Trace
        (some ⟨remaining, command.actor? (application setup timeouts leaks), next⟩))
    (tracePrefix : TracePrefix trace target) (failed : next.application.PublicFailure event) :
    ¬ MainActivationTraceAfter setup timeouts leaks bounds horizon
      scheduler source focal
      startTrace.length target := by
  intro main
  obtain ⟨originEvent, before, prior, response, joint, legal, realized, future, afterPrefix,
    acting, chosen,
    pending, never, outside⟩ :=
    foreign_nonmain_prefix_of_firstFailure (timeouts := timeouts) wellFormed covers
      capacity source focal owner different opportunity inclusion timely start
      startTrace remaining execution trace startPrefix current event turn clear regular notOwed
      owned
      command next reached target tracePrefix failed
  have supported := mainActivationStep_of_tracePrefix (timeouts := timeouts) source focal
    startTrace.length prior joint
    legal realized afterPrefix main future.length_le
  apply outside
  have first : FirstActivation setup timeouts leaks owner (some (before.execution.logs owner,
      before.execution.observe (application setup timeouts leaks) owner)) :=
    ⟨before.execution.logs owner, before.execution.observe (application setup timeouts leaks)
      owner, originEvent,
      rfl, pending, never⟩
  have selected := supported owner acting different first
  simpa only [chosen, Option.getD_some] using selected


end Vegas
