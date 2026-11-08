/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceServiceAsyncTimeliness
import Vegas.Pending.ExclusionPolicyLaw
import Vegas.Pending.ReactiveSignedCommitments
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveStopping

/-! # Accepted source continuation through native automatic service -/

noncomputable section
namespace Vegas
open SourceProgram EventGraphRuntime EventGraph GameTheory.Protocol
  GameTheory.Math.Probability Interaction
variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

private theorem settlesFreshCalls_raw
    (timeouts : EventTimeouts (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {horizon : Nat} {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    {bound : (serviceGraph setup mode).EventId → Nat}
    (inclusion : ProtectedInclusion timeouts leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (owned : (serviceGraph setup mode).actor? event = some owner) :
    ∀ {state} (_trace : (((reactiveApplication timeouts) leaks).protocol (serviceInitialLaw setup
      mode)
      horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant
        (SettlesFreshCalls setup leaks owner event bound) state
  | _, .start => trivial
  | _, .extend (source := before) prior joint _ reached => by
      have valid := settlesFreshCalls_raw timeouts leaks inclusion owner event owned prior
      cases before with
      | none =>
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ reached
          intro earlier entry later message split
          simp [ReactiveApplication.Execution.initial] at split
      | some control =>
          rcases control with ⟨remaining, actor, execution⟩
          cases actor with
          | some who =>
              cases (PMF.mem_support_pure_iff _ _).mp reached
              exact settlesFreshCalls_respond setup leaks owner event bound execution
                (legalFacts setup leaks horizon scheduler _ prior) who _ valid
          | none =>
              cases remaining with
              | zero => cases (PMF.mem_support_pure_iff _ _).mp reached; exact valid
              | succ remaining =>
                  obtain ⟨command, _, moved⟩ :=
                    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
                  obtain ⟨next, supported, rfl⟩ := PMF.support_map .. ▸ moved
                  exact SettlesFreshCalls.environment setup leaks owner event owned remaining
                    execution (ProtectedInclusion.at timeouts leaks inclusion _ prior) prior valid
                    command next supported

private theorem recorded_fresh_call
    (timeouts : EventTimeouts (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {horizon : Nat} {scheduler : ((reactiveApplication timeouts) leaks).Scheduler}
    {control : ((reactiveApplication timeouts) leaks).Control}
    (trace : (((reactiveApplication timeouts) leaks).protocol (serviceInitialLaw setup mode)
      horizon scheduler).Trace (some control))
    (owner : Player) (event : (serviceGraph setup mode).EventId) (bound :
      (serviceGraph setup mode).EventId → Nat)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (recorded : entry ∈ control.execution.logs owner)
    (call : FreshCall setup leaks owner event bound entry message) :
    (submittedEvent? timeouts) leaks entry.action = some event := by
  have signed := signedCommitments_history timeouts leaks (serviceInitialLaw setup mode)
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  obtain ⟨_sender, material, transmitted, packet⟩ :=
    signed.emissions owner entry recorded message call.emitted
  simp only [EventGraphRuntime.submittedEvent?, transmitted]
  rw [← packet]
  exact call.addressed

private theorem respond_sole_call
    (timeouts : EventTimeouts (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (owner : Player) (event : (serviceGraph setup mode).EventId)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry) (id : MessageId Player)
    (submitted : (submittedEvent? timeouts) leaks entry.action = some event)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      (eventRecorded timeouts) leaks past event = true →
      (submittedEvent? timeouts) leaks response ≠ some event)
    (execution : ((reactiveApplication timeouts) leaks).Execution) (actor : Player)
    (response : ((reactiveApplication timeouts) leaks).Action)
    (member : response ∈ (players actor (execution.logs actor)
      (execution.observe ((reactiveApplication timeouts) leaks) actor)).support)
    (recorded : entry ∈ execution.logs owner)
    (sole : ∀ other ∈ execution.logs owner, ¬ EmitsOtherFor timeouts leaks other event id) :
    ∀ other ∈ (execution.respond ((reactiveApplication timeouts) leaks) actor response).logs owner,
      ¬ EmitsOtherFor timeouts leaks other event id := by
  let app := (reactiveApplication timeouts) leaks
  by_cases same : actor = owner
  · subst actor
    intro other present emits
    rw [(respond_recall timeouts) leaks] at present
    simp only [↓reduceIte] at present
    rcases List.mem_append.mp present with old | new
    · exact sole other old emits
    · obtain rfl := List.mem_singleton.mp new
      have forbidden := noRepeat _ _ response member
        (((eventRecorded_iff timeouts) leaks _ event).mpr ⟨entry, recorded, submitted⟩)
      obtain ⟨message, emitted, _sender, named, _different⟩ := emits
      rcases response with ⟨transmission⟩
      cases transmission with
      | none => cases emitted
      | some material =>
          cases Option.some.inj emitted
          exact forbidden named
  · rw [app.respond_recall_other execution actor owner (Ne.symm same) response]
    exact sole

private theorem settled_of_recorded
    (timeouts : EventTimeouts (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    (owner : Player) (event : (serviceGraph setup mode).EventId) (bound :
      (serviceGraph setup mode).EventId → Nat)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (valid : SettlesFreshCalls setup leaks owner event bound execution)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (recorded : entry ∈ execution.logs owner)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ execution.logs owner,
      ¬ EmitsOtherFor timeouts leaks other event message.id) :
    Settled setup leaks event message.id execution := by
  obtain ⟨earlier, later, split⟩ := List.mem_iff_append.mp recorded
  apply valid earlier entry later message split call
  intro other member
  apply sole other
  rw [split]
  rcases List.mem_append.mp member with before | after
  · exact List.mem_append_left _ before
  · exact List.mem_append_right _ (List.mem_cons_of_mem _ after)

private theorem round_accepted_result
    (timeouts : EventTimeouts (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {Result : Type*} (continuation : (serviceGraph setup mode).Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State (serviceGraph setup mode),
      continuation state.drain.config = continuation state.config)
    {horizon remaining : Nat} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (inclusion : ProtectedInclusion timeouts leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (event : (serviceGraph setup mode).EventId) (solitary :
      (serviceGraph setup mode).Solitary event) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (sent : (serviceGraph setup mode).Config) (ready : sent.cut.Ready event)
    (action : (serviceGraph setup mode).Action event)
    (output : ((serviceGraph setup mode).outputLayout event).Value)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (call : FreshCall setup leaks owner event bound entry message)
    (submitted : (submittedEvent? timeouts) leaks entry.action = some event)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      (eventRecorded timeouts) leaks past event = true →
      (submittedEvent? timeouts) leaks response ≠ some event)
    (execution next : ((reactiveApplication timeouts) leaks).Execution)
    (trace : (((reactiveApplication timeouts) leaks).protocol (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (sameConfig : execution.application.config = sent)
    (recorded : entry ∈ execution.logs owner)
    (sole : ∀ other ∈ execution.logs owner,
      ¬ EmitsOtherFor timeouts leaks other event message.id)
    (witness : AcceptanceWitness event message sent action output execution.application)
    (reached : next ∈
      (((reactiveApplication timeouts) leaks).round scheduler players execution).support) :
    (next.application.config = sent ∧ entry ∈ next.logs owner ∧
      (∀ other ∈ next.logs owner, ¬ EmitsOtherFor timeouts leaks other event message.id) ∧
      AcceptanceWitness event message sent action output next.application) ∨
    (event ∈ next.application.config.cut.completed ∧
      continuation next.application.config =
        (sent.step event ready action).bind fun after =>
          continuation after) := by
  let app := (reactiveApplication timeouts) leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have readyBefore : execution.application.config.cut.Ready event := sameConfig ▸ ready
  have settledBefore := settled_of_recorded timeouts leaks owner event bound execution
    (settlesFreshCalls_raw timeouts leaks inclusion owner event owned trace) entry message
    recorded call sole
  have fresh : (message.id, true) ∉ execution.receipts := fun receipt =>
    readyBefore.1 (settledBefore.2.2 receipt)
  have input : message ∈ execution.network.inputs := by
    have recalled : message ∈ app.outputs (execution.logs owner) :=
      List.mem_filterMap.mpr ⟨entry, recorded, call.emitted⟩
    rw [← facts.inputs owner] at recalled
    exact (List.mem_filter.mp recalled).1
  obtain ⟨command, selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (serviceInitialLaw setup mode) horizon scheduler
    remaining execution middle command trace selected moved
  have recallEq := app.environmentStep_recall execution middle command moved
  have recordedMiddle : entry ∈ middle.logs owner := by rw [recallEq]; exact recorded
  have soleMiddle : ∀ other ∈ middle.logs owner,
      ¬ EmitsOtherFor timeouts leaks other event message.id := by rw [recallEq]; exact sole
  have witnessMiddle := witness.keep
    ((keepsFixedCandidates_step timeouts leaks).environmentStep execution middle command moved)
  by_cases completed : event ∈ middle.application.config.cut.completed
  · have receipt := (settled_of_recorded timeouts leaks owner event bound middle
      (settlesFreshCalls_raw timeouts leaks inclusion owner event owned middleTrace) entry message
      recordedMiddle call soleMiddle).1 completed
    obtain ⟨state, handled, stateEq⟩ := app.environmentStep_newly_accepted execution middle command
      facts.unique moved input fresh receipt
    rw [← stateEq] at handled
    have noActor : command.actor? app = none := by
      cases command with
      | wait | «include» | application => rfl
      | activate who =>
          obtain ⟨updated, supported, rfl⟩ := PMF.support_map .. ▸ moved
          obtain ⟨seen, _, rfl⟩ := PMF.support_map .. ▸ supported
          exact (readyBefore.1 completed).elim
    change next ∈ (app.resume players (command.actor? app) middle).support at resumed
    rw [noActor] at resumed
    cases (PMF.mem_support_pure_iff _ _).mp resumed
    refine Or.inr ⟨completed, ?_⟩
    obtain ⟨actualReady, _decision, continuation⟩ :=
      witness.reactive_continuation timeouts leaks continuation drained sameConfig handled
    have active : owner ∉ sent.defaulted := by
      rw [← sameConfig]
      exact execution.application.active_of_ready_owned facts.quiescent readyBefore owned
    have supported := witness.complete_mem_step sameConfig ready owner owned active
    obtain ⟨target, law⟩ := sent.step_eq_pure_of_actor event ready action owner owned
    rw [law, PMF.mem_support_pure_iff] at supported
    rw [law, PMF.pure_bind, ← supported]
    exact continuation
  · have sameMiddle : middle.application.config = sent :=
      (EventGraph.Config.Step.path_eq_of_ready_of_not_completed event
        (fun _ otherReady => solitary _ otherReady readyBefore)
        completed (((reactiveApplication_graphSteps timeouts) leaks).environmentStep
          execution middle command moved)).trans sameConfig
    change next ∈ (app.resume players (command.actor? app) middle).support at resumed
    cases actor : command.actor? app with
    | none =>
        rw [actor] at resumed
        cases (PMF.mem_support_pure_iff _ _).mp resumed
        exact Or.inl ⟨sameMiddle, recordedMiddle, soleMiddle, witnessMiddle⟩
    | some who =>
        rw [actor] at resumed
        obtain ⟨response, member, rfl⟩ := PMF.support_map .. ▸ resumed
        refine Or.inl ⟨(((reactive_respond_application timeouts) leaks middle who response).1).trans
          sameMiddle, app.respond_recall_mono middle who owner response recordedMiddle, ?_, ?_⟩
        · exact respond_sole_call timeouts leaks players owner event entry message.id submitted
            noRepeat middle who response member recordedMiddle soleMiddle
        · exact witnessMiddle.keep
            ((keepsFixedCandidates_step timeouts leaks).respond middle who response)

private theorem runUntil_accepted_result
    (timeouts : EventTimeouts (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {Result : Type*} (continuation : (serviceGraph setup mode).Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State (serviceGraph setup mode),
      continuation state.drain.config = continuation state.config)
    {horizon : Nat} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (inclusion : ProtectedInclusion timeouts leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (event : (serviceGraph setup mode).EventId) (solitary :
      (serviceGraph setup mode).Solitary event) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (sent : (serviceGraph setup mode).Config) (ready : sent.cut.Ready event)
    (action : (serviceGraph setup mode).Action event)
    (output : ((serviceGraph setup mode).outputLayout event).Value)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (call : FreshCall setup leaks owner event bound entry message)
    (submitted : (submittedEvent? timeouts) leaks entry.action = some event)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      (eventRecorded timeouts) leaks past event = true →
      (submittedEvent? timeouts) leaks response ≠ some event) :
    ∀ (count remaining : Nat) (execution stopped : ((reactiveApplication timeouts)
      leaks).Execution),
      count ≤ remaining →
      (((reactiveApplication timeouts) leaks).protocol
        (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining, none, execution⟩) →
      execution.application.config = sent →
      entry ∈ execution.logs owner →
      (∀ other ∈ execution.logs owner, ¬ EmitsOtherFor timeouts leaks other event message.id) →
      AcceptanceWitness event message sent action output execution.application →
      stopped ∈ (((reactiveApplication timeouts) leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).support →
      event ∈ stopped.application.config.cut.completed →
      continuation stopped.application.config =
        (sent.step event ready action).bind fun after =>
          continuation after := by
  let app := (reactiveApplication timeouts) leaks
  intro count
  induction count with
  | zero =>
      intro remaining execution stopped _ _ sameConfig _ _ _ reached completed
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact (ready.1 (sameConfig ▸ completed)).elim
  | succ count ih =>
      intro remaining execution stopped enough trace sameConfig recorded sole witness reached done
      cases remaining with
      | zero => omega
      | succ remaining =>
          have pending : ¬ event ∈ execution.application.config.cut.completed := by
            rw [sameConfig]
            exact ready.1
          simp only [ReactiveApplication.runUntil, pending, ↓reduceIte] at reached
          obtain ⟨middle, moved, rest⟩ :=
            Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
          rcases round_accepted_result timeouts leaks continuation drained scheduler players bound
              inclusion event solitary owner owned sent ready action output entry message call
                submitted noRepeat
              execution middle trace sameConfig recorded sole witness moved with
            ⟨sameMiddle, recordedMiddle, soleMiddle, witnessMiddle⟩ | ⟨completed, continuation⟩
          · obtain ⟨middleTrace⟩ := app.raw_trace_round (serviceInitialLaw setup mode) horizon
              scheduler players remaining execution middle trace moved
            exact ih remaining middle stopped (by omega) middleTrace sameMiddle recordedMiddle
              soleMiddle witnessMiddle rest done
          · rw [app.runUntil_of_stop scheduler players _ count middle completed,
              PMF.mem_support_pure_iff] at rest
            subst stopped
            exact continuation

/-- A protected recorded call has the continuation of its fixed graph action,
including a failed result and subsequent automatic completions, for every
continuation that automatic completion leaves unchanged. -/
theorem FreshCall.accepted_continuation
    (timeouts : EventTimeouts (serviceGraph setup mode))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode)))
    {Result : Type*} (continuation : (serviceGraph setup mode).Config → PMF Result)
    (drained : ∀ state : EventGraphRuntime.State (serviceGraph setup mode),
      continuation state.drain.config = continuation state.config)
    {horizon remaining : Nat} (scheduler : ((reactiveApplication timeouts) leaks).Scheduler)
    (players : Player → ((reactiveApplication timeouts) leaks).Policy)
    (bound : (serviceGraph setup mode).EventId → Nat)
    (inclusion : ProtectedInclusion timeouts leaks
      (serviceInitialLaw setup mode) horizon scheduler bound)
    (complete : CompletesPlay timeouts leaks (serviceInitialLaw setup mode) horizon scheduler)
    (event : (serviceGraph setup mode).EventId) (solitary :
      (serviceGraph setup mode).Solitary event) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (execution : ((reactiveApplication timeouts) leaks).Execution)
    (trace : (((reactiveApplication timeouts) leaks).protocol (serviceInitialLaw setup mode) horizon
      scheduler).Trace (some ⟨remaining, none, execution⟩))
    (ready : execution.application.config.cut.Ready event)
    (action : (serviceGraph setup mode).Action event)
    (output : ((serviceGraph setup mode).outputLayout event).Value)
    (entry : ((reactiveApplication timeouts) leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (serviceGraph setup mode)))
    (recorded : entry ∈ execution.logs owner)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ execution.logs owner,
      ¬ EmitsOtherFor timeouts leaks other event message.id)
    (witness : AcceptanceWitness event message execution.application.config action output
      execution.application)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      (eventRecorded timeouts) leaks past event = true →
      (submittedEvent? timeouts) leaks response ≠ some event) :
    ((((reactiveApplication timeouts) leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        continuation stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        continuation after := by
  let app := (reactiveApplication timeouts) leaks
  have accounted : execution.environmentRecall.length + remaining = horizon :=
    app.raw_trace_horizon (serviceInitialLaw setup mode) horizon scheduler trace
  have countEq : horizon - execution.environmentRecall.length = remaining := by omega
  have submitted := recorded_fresh_call timeouts leaks trace owner event bound entry message
    recorded call
  apply (bind_congr_on_support _ fun stopped reached => ?_).trans (PMF.bind_const _ _)
  change stopped ∈ (app.runUntil scheduler players
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - execution.environmentRecall.length) execution).support at reached
  rw [countEq] at reached
  apply runUntil_accepted_result timeouts leaks continuation drained scheduler players bound
    inclusion event solitary owner owned execution.application.config ready action output entry
      message call submitted
    noRepeat remaining remaining execution stopped le_rfl trace rfl recorded sole witness reached
  rcases app.runUntil_stopped scheduler players _ remaining execution stopped reached with
    done | spent
  · exact done
  · obtain ⟨used, enough, rounds, lengthEq⟩ := app.runUntil_runRounds scheduler players _
      remaining execution stopped reached
    obtain ⟨stoppedTrace⟩ := app.raw_trace_runRounds
      (serviceInitialLaw setup mode) horizon scheduler players
      (remaining - used) used execution stopped (by
        simpa only [Nat.sub_add_cancel enough] using trace) rounds
    have terminal := complete _ stoppedTrace (by
      change remaining - used = 0 ∧ _
      exact ⟨by omega, rfl⟩)
    change stopped.application.config.cut.completed = Finset.univ at terminal
    rw [terminal]
    exact Finset.mem_univ _

/-- A protected recorded call has the full graph continuation of its fixed
graph action, including a failed result and subsequent automatic completions. -/
theorem FreshCall.accepted_runPlan
    (timeouts : EventTimeouts (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    {horizon remaining : Nat} (scheduler : (application setup timeouts leaks).Scheduler)
    (players : Player → (application setup timeouts leaks).Policy)
    (bound : (graph setup).EventId → Nat)
    (inclusion : ProtectedInclusion timeouts leaks (initialLaw setup) horizon scheduler bound)
    (complete : CompletesPlay timeouts leaks (initialLaw setup) horizon scheduler)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (execution : (application setup timeouts leaks).Execution)
    (trace : ((application setup timeouts leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution⟩))
    (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (output : ((graph setup).outputLayout event).Value)
    (entry : (application setup timeouts leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (recorded : entry ∈ execution.logs owner)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ execution.logs owner,
      ¬ EmitsOtherFor timeouts leaks other event message.id)
    (witness : AcceptanceWitness event message execution.application.config action output
      execution.application)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      (eventRecorded timeouts) leaks past event = true →
      (submittedEvent? timeouts) leaks response ≠ some event) :
    (((application setup timeouts leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          after.remaining after :=
  FreshCall.accepted_continuation timeouts leaks
    (fun config => (graph setup).runPlan
      ((graph setup).policyPlan profile (graph setup).canonicalScheduler) config.remaining config)
    (fun state => (EventGraphRuntime.State.drain_runPlan_canonical setup.eventGraph profile
      state).symm) scheduler players bound inclusion complete event
    (setup.eventGraph.sequentialize_solitary event) owner owned execution trace ready action output
    entry message recorded call sole witness noRepeat

end Vegas
