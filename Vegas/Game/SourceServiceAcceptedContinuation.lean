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
  {setup : Setup (Player := Player) (L := L)}

private theorem settlesFreshCalls_raw
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    {bound : (graph setup).EventId → Nat}
    (inclusion : ProtectedInclusion runtime leaks (initialLaw setup) horizon scheduler bound)
    (owner : Player) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner) :
    ∀ {state} (_trace : ((application setup runtime leaks).protocol (initialLaw setup)
      horizon scheduler).Trace state),
      ReactiveApplication.serviceInvariant
        (SettlesFreshCalls setup leaks owner event bound) state
  | _, .start => trivial
  | _, .extend (source := before) prior joint _ reached => by
      have valid := settlesFreshCalls_raw runtime leaks inclusion owner event owned prior
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
                    execution (ProtectedInclusion.at runtime leaks inclusion _ prior) prior valid
                    command next supported

private theorem recorded_fresh_call
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    {horizon : Nat} {scheduler : (application setup runtime leaks).Scheduler}
    {control : (application setup runtime leaks).Control}
    (trace : ((application setup runtime leaks).protocol (initialLaw setup)
      horizon scheduler).Trace (some control))
    (owner : Player) (event : (graph setup).EventId) (bound : (graph setup).EventId → Nat)
    (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (recorded : entry ∈ control.execution.recall owner)
    (call : FreshCall setup leaks owner event bound entry message) :
    runtime.submittedEvent? leaks entry.action = some event := by
  have signed := signedCommitments_history runtime leaks (initialLaw setup)
    (fun state supported => by
      obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
      exact ⟨_, rfl⟩) horizon scheduler trace
  obtain ⟨_sender, material, transmitted, packet⟩ :=
    signed.emissions owner entry recorded message call.emitted
  simp only [EventGraphRuntime.submittedEvent?, transmitted]
  rw [← packet]
  exact call.addressed

private theorem respond_sole_call
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (players : Player → (application setup runtime leaks).Policy)
    (owner : Player) (event : (graph setup).EventId)
    (entry : (application setup runtime leaks).PlayerEntry) (id : MessageId Player)
    (submitted : runtime.submittedEvent? leaks entry.action = some event)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      runtime.eventRecorded leaks past event = true →
      runtime.submittedEvent? leaks response ≠ some event)
    (execution : (application setup runtime leaks).Execution) (actor : Player)
    (response : (application setup runtime leaks).Action)
    (member : response ∈ (players actor (execution.recall actor)
      (execution.observe (application setup runtime leaks) actor)).support)
    (recorded : entry ∈ execution.recall owner)
    (sole : ∀ other ∈ execution.recall owner, ¬ EmitsOtherFor runtime leaks other event id) :
    ∀ other ∈ (execution.respond (application setup runtime leaks) actor response).recall owner,
      ¬ EmitsOtherFor runtime leaks other event id := by
  let app := application setup runtime leaks
  by_cases same : actor = owner
  · subst actor
    intro other present emits
    rw [runtime.respond_recall leaks] at present
    simp only [↓reduceIte] at present
    rcases List.mem_append.mp present with old | new
    · exact sole other old emits
    · obtain rfl := List.mem_singleton.mp new
      have forbidden := noRepeat _ _ response member
        ((runtime.eventRecorded_iff leaks _ event).mpr ⟨entry, recorded, submitted⟩)
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
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (owner : Player) (event : (graph setup).EventId) (bound : (graph setup).EventId → Nat)
    (execution : (application setup runtime leaks).Execution)
    (valid : SettlesFreshCalls setup leaks owner event bound execution)
    (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (recorded : entry ∈ execution.recall owner)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ execution.recall owner,
      ¬ EmitsOtherFor runtime leaks other event message.id) :
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
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    {horizon remaining : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (bound : (graph setup).EventId → Nat)
    (inclusion : ProtectedInclusion runtime leaks (initialLaw setup) horizon scheduler bound)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (sent : (graph setup).Config) (ready : sent.cut.Ready event)
    (action : (graph setup).Action event)
    (output : ((graph setup).outputLayout event).Value)
    (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (call : FreshCall setup leaks owner event bound entry message)
    (submitted : runtime.submittedEvent? leaks entry.action = some event)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      runtime.eventRecorded leaks past event = true →
      runtime.submittedEvent? leaks response ≠ some event)
    (execution next : (application setup runtime leaks).Execution)
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining + 1, none, execution⟩))
    (sameConfig : execution.application.config = sent)
    (recorded : entry ∈ execution.recall owner)
    (sole : ∀ other ∈ execution.recall owner,
      ¬ EmitsOtherFor runtime leaks other event message.id)
    (witness : AcceptanceWitness event message sent action output execution.application)
    (reached : next ∈
      ((application setup runtime leaks).round scheduler players execution).support) :
    (next.application.config = sent ∧ entry ∈ next.recall owner ∧
      (∀ other ∈ next.recall owner, ¬ EmitsOtherFor runtime leaks other event message.id) ∧
      AcceptanceWitness event message sent action output next.application) ∨
    (event ∈ next.application.config.cut.completed ∧
      (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          next.application.config.remaining next.application.config =
        (sent.step event ready action).bind fun after =>
          (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
            after.remaining after) := by
  let app := application setup runtime leaks
  have facts := legalFacts setup leaks horizon scheduler _ trace
  have readyBefore : execution.application.config.cut.Ready event := sameConfig ▸ ready
  have settledBefore := settled_of_recorded runtime leaks owner event bound execution
    (settlesFreshCalls_raw runtime leaks inclusion owner event owned trace) entry message
    recorded call sole
  have fresh : (message.id, true) ∉ execution.receipts := fun receipt =>
    readyBefore.1 (settledBefore.2.2 receipt)
  have input : message ∈ execution.network.inputs := by
    have recalled : message ∈ app.outputs (execution.recall owner) :=
      List.mem_filterMap.mpr ⟨entry, recorded, call.emitted⟩
    rw [← facts.inputs owner] at recalled
    exact (List.mem_filter.mp recalled).1
  obtain ⟨command, selected, dispatched⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  obtain ⟨middle, moved, resumed⟩ :=
    Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ dispatched)
  obtain ⟨middleTrace⟩ := app.raw_trace_environment (initialLaw setup) horizon scheduler
    remaining execution middle command trace selected moved
  have recallEq := app.environmentStep_recall execution middle command moved
  have recordedMiddle : entry ∈ middle.recall owner := by rw [recallEq]; exact recorded
  have soleMiddle : ∀ other ∈ middle.recall owner,
      ¬ EmitsOtherFor runtime leaks other event message.id := by rw [recallEq]; exact sole
  have witnessMiddle := witness.keep
    ((keepsFixedCandidates_step runtime leaks).environmentStep execution middle command moved)
  by_cases completed : event ∈ middle.application.config.cut.completed
  · have receipt := (settled_of_recorded runtime leaks owner event bound middle
      (settlesFreshCalls_raw runtime leaks inclusion owner event owned middleTrace) entry message
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
      witness.reactive_runPlan setup.eventGraph runtime leaks profile sameConfig handled
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
        (fun _ otherReady => setup.eventGraph.sequentialize_ready_unique _ otherReady readyBefore)
        completed ((runtime.reactiveApplication_graphSteps leaks).environmentStep
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
        refine Or.inl ⟨((runtime.reactive_respond_application leaks middle who response).1).trans
          sameMiddle, app.respond_recall_mono middle who owner response recordedMiddle, ?_, ?_⟩
        · exact respond_sole_call runtime leaks players owner event entry message.id submitted
            noRepeat middle who response member recordedMiddle soleMiddle
        · exact witnessMiddle.keep
            ((keepsFixedCandidates_step runtime leaks).respond middle who response)

private theorem runUntil_accepted_result
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    {horizon : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (bound : (graph setup).EventId → Nat)
    (inclusion : ProtectedInclusion runtime leaks (initialLaw setup) horizon scheduler bound)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (sent : (graph setup).Config) (ready : sent.cut.Ready event)
    (action : (graph setup).Action event)
    (output : ((graph setup).outputLayout event).Value)
    (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (call : FreshCall setup leaks owner event bound entry message)
    (submitted : runtime.submittedEvent? leaks entry.action = some event)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      runtime.eventRecorded leaks past event = true →
      runtime.submittedEvent? leaks response ≠ some event) :
    ∀ (count remaining : Nat) (execution stopped : (application setup runtime leaks).Execution),
      count ≤ remaining →
      ((application setup runtime leaks).protocol (initialLaw setup) horizon scheduler).Trace
        (some ⟨remaining, none, execution⟩) →
      execution.application.config = sent →
      entry ∈ execution.recall owner →
      (∀ other ∈ execution.recall owner, ¬ EmitsOtherFor runtime leaks other event message.id) →
      AcceptanceWitness event message sent action output execution.application →
      stopped ∈ ((application setup runtime leaks).runUntil scheduler players
        (fun final => event ∈ final.application.config.cut.completed) count execution).support →
      event ∈ stopped.application.config.cut.completed →
      (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          stopped.application.config.remaining stopped.application.config =
        (sent.step event ready action).bind fun after =>
          (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
            after.remaining after := by
  let app := application setup runtime leaks
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
          rcases round_accepted_result runtime leaks profile scheduler players bound inclusion
              event owner owned sent ready action output entry message call submitted noRepeat
              execution middle trace sameConfig recorded sole witness moved with
            ⟨sameMiddle, recordedMiddle, soleMiddle, witnessMiddle⟩ | ⟨completed, continuation⟩
          · obtain ⟨middleTrace⟩ := app.raw_trace_round (initialLaw setup) horizon scheduler players
              remaining execution middle trace moved
            exact ih remaining middle stopped (by omega) middleTrace sameMiddle recordedMiddle
              soleMiddle witnessMiddle rest done
          · rw [app.runUntil_of_stop scheduler players _ count middle completed,
              PMF.mem_support_pure_iff] at rest
            subst stopped
            exact continuation

/-- A protected recorded call has the full graph continuation of its fixed
graph action, including a failed result and subsequent automatic completions. -/
theorem FreshCall.accepted_runPlan
    (runtime : EventGraphRuntime (graph setup))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (profile : (graph setup).BehavioralProfile)
    {horizon remaining : Nat} (scheduler : (application setup runtime leaks).Scheduler)
    (players : Player → (application setup runtime leaks).Policy)
    (bound : (graph setup).EventId → Nat)
    (inclusion : ProtectedInclusion runtime leaks (initialLaw setup) horizon scheduler bound)
    (complete : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (event : (graph setup).EventId) (owner : Player)
    (owned : (graph setup).actor? event = some owner)
    (execution : (application setup runtime leaks).Execution)
    (trace : ((application setup runtime leaks).protocol (initialLaw setup) horizon
      scheduler).Trace (some ⟨remaining, none, execution⟩))
    (ready : execution.application.config.cut.Ready event)
    (action : (graph setup).Action event)
    (output : ((graph setup).outputLayout event).Value)
    (entry : (application setup runtime leaks).PlayerEntry)
    (message : Message Player (WitnessedPacket (graph setup)))
    (recorded : entry ∈ execution.recall owner)
    (call : FreshCall setup leaks owner event bound entry message)
    (sole : ∀ other ∈ execution.recall owner,
      ¬ EmitsOtherFor runtime leaks other event message.id)
    (witness : AcceptanceWitness event message execution.application.config action output
      execution.application)
    (noRepeat : ∀ past view response,
      response ∈ (players owner past view).support →
      runtime.eventRecorded leaks past event = true →
      runtime.submittedEvent? leaks response ≠ some event) :
    (((application setup runtime leaks).runUntilHorizon scheduler players
        (fun final => event ∈ final.application.config.cut.completed) horizon execution).bind
      fun stopped =>
        (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          stopped.application.config.remaining stopped.application.config) =
      (execution.application.config.step event ready action).bind fun after =>
        (graph setup).runPlan ((graph setup).policyPlan profile (graph setup).canonicalScheduler)
          after.remaining after := by
  let app := application setup runtime leaks
  have accounted : execution.environmentRecall.length + remaining = horizon :=
    app.raw_trace_horizon (initialLaw setup) horizon scheduler trace
  have countEq : horizon - execution.environmentRecall.length = remaining := by omega
  have submitted := recorded_fresh_call runtime leaks trace owner event bound entry message
    recorded call
  apply (bind_congr_on_support _ fun stopped reached => ?_).trans (PMF.bind_const _ _)
  change stopped ∈ (app.runUntil scheduler players
    (fun final => event ∈ final.application.config.cut.completed)
    (horizon - execution.environmentRecall.length) execution).support at reached
  rw [countEq] at reached
  apply runUntil_accepted_result runtime leaks profile scheduler players bound inclusion event
    owner owned execution.application.config ready action output entry message call submitted
    noRepeat remaining remaining execution stopped le_rfl trace rfl recorded sole witness reached
  rcases app.runUntil_stopped scheduler players _ remaining execution stopped reached with
    done | spent
  · exact done
  · obtain ⟨used, enough, rounds, lengthEq⟩ := app.runUntil_runRounds scheduler players _
      remaining execution stopped reached
    obtain ⟨stoppedTrace⟩ := app.raw_trace_runRounds (initialLaw setup) horizon scheduler players
      (remaining - used) used execution stopped (by
        simpa only [Nat.sub_add_cancel enough] using trace) rounds
    have terminal := complete _ stoppedTrace (by
      change remaining - used = 0 ∧ _
      exact ⟨by omega, rfl⟩)
    change stopped.application.config.cut.completed = Finset.univ at terminal
    rw [terminal]
    exact Finset.mem_univ _

end Vegas
