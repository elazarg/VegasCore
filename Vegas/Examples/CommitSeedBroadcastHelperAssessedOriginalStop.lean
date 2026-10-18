/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperSentResponse
import Interaction.ReactiveMixtureRounds
import Interaction.ReactiveRawRoundTrace
import Interaction.ReactiveRoundTrace
import Interaction.ReactiveMenuImplementation

/-! # Actual assessed original helper continuation before retirement -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem round_retains_output (players : Player → app.Policy)
    (before after : app.Execution) (reached : after ∈ (app.round scheduler players before).support)
    (owner : Player) (message : Message Player app.Payload)
    (member : message ∈ app.outputs (before.recall owner)) :
    message ∈ app.outputs (after.recall owner) := by
  rw [ReactiveApplication.round, PMF.support_bind] at reached
  obtain ⟨command, _selected, dispatched⟩ := Set.mem_iUnion₂.mp reached
  rw [ReactiveApplication.dispatch, PMF.support_bind] at dispatched
  obtain ⟨middle, moved, resumed⟩ := Set.mem_iUnion₂.mp dispatched
  have recalled := app.environmentStep_recall before middle command moved
  have old : message ∈ app.outputs (middle.recall owner) := by
    rw [congrFun recalled owner]
    exact member
  cases active : command.actor? app with
  | none =>
      simp only [active, ReactiveApplication.resume] at resumed
      cases (PMF.mem_support_pure_iff _ _).mp resumed
      exact old
  | some actor =>
      simp only [active, ReactiveApplication.resume, ReactiveApplication.invoke, PMF.support_map]
        at resumed
      obtain ⟨action, _chosen, equal⟩ := resumed
      rw [← equal]
      obtain ⟨entry, recorded, emitted⟩ := List.mem_filterMap.mp old
      exact List.mem_filterMap.mpr ⟨entry,
        app.respond_recall_mono middle actor owner action recorded, emitted⟩

private theorem counted_idle_trace_aligned (remaining : Nat) (execution : app.Execution)
    (raw : (app.protocol initial horizon scheduler).Trace
      (some ⟨remaining, none, execution⟩))
    (counted : ∃ fuel, Nonempty
      (countedProtocol.Trace (some ⟨fuel, none, execution⟩))) :
    Nonempty (countedProtocol.Trace (some ⟨remaining, none, execution⟩)) := by
  obtain ⟨fuel, ⟨trace⟩⟩ := counted
  have originalLength := app.raw_trace_horizon initial horizon scheduler raw
  have countedLength := app.raw_trace_horizon initial horizon scheduler
    (countedMenu.toRawTrace initial horizon scheduler trace)
  have sameFuel : fuel = remaining := by
    change execution.environmentRecall.length + remaining = horizon at originalLength
    change execution.environmentRecall.length + fuel = horizon at countedLength
    omega
  subst fuel
  exact ⟨trace⟩

open Classical in
/-- Replacing the sent helper's later responses by WAIT changes no original
stopped continuation under the actual raw equilibrium profile. The local
response equality and continued counted legality are derived from the audit;
they are not hypotheses on the incumbent foreign strategies. -/
theorem assessed_sent_helper_original_stopped_law
    (assessment : rawModel.BehavioralAssessment)
    (equilibrium : assessment.IsSequentialEquilibrium
      (rawMenu.decisionInformationAntichain initial horizon scheduler)
      canonicalCertificate rawPayoff)
    (hidden : Player) (count remaining : Nat) (execution : app.Execution)
    (trace : countedProtocol.Trace (some ⟨remaining + count, none, execution⟩))
    (sent : ∃ message ∈ app.outputs (execution.recall hidden),
      PhaseCount.event? message.payload = some (originalCoordinate hidden)) :
    app.runUntil scheduler (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
        (fun current => current.application.attempt ≠ originalAttempt) count execution =
      app.runUntil scheduler
        (Function.update (rawMenu.decodeProfile initial horizon scheduler assessment.strategy)
          hidden (fun _ _ => PMF.pure ⟨none⟩))
        (fun current => current.application.attempt ≠ originalAttempt) count execution := by
  classical
  let players := rawMenu.decodeProfile initial horizon scheduler assessment.strategy
  let stop := fun current : app.Execution => current.application.attempt ≠ originalAttempt
  let invariant := fun current : app.Execution =>
    (∃ fuel, Nonempty (countedProtocol.Trace (some ⟨fuel, none, current⟩))) ∧
      ∃ message ∈ app.outputs (current.recall hidden),
        PhaseCount.event? message.payload = some (originalCoordinate hidden)
  have admissible (who : Player) : countedMenu.Admissible initial horizon scheduler who
      (players who) :=
    countedInRaw.decoded_admissible initial horizon scheduler (countedAssessmentProfile assessment)
      assessment.strategy (raw_equilibrium_extends_counted assessment equilibrium) who
  have agree (fuel : Nat) (before : app.Execution)
      (raw : (app.protocol initial horizon scheduler).Trace
        (some ⟨fuel + 1, none, before⟩))
      (holds : invariant before) (notStopped : ¬ stop before)
      (command : app.Command)
      (selected : command ∈ (scheduler before.environmentRecall
        (before.observeEnvironment app)).support)
      (middle : app.Execution) (moved : middle ∈ (before.environmentStep app command).support)
      (who : Player) (acting : command.actor? app = some who) :
      players who (middle.recall who) (middle.observe app who) =
        Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩) who
          (middle.recall who) (middle.observe app who) := by
    by_cases own : who = hidden
    · subst who
      rw [Function.update_self]
      obtain ⟨prior⟩ := counted_idle_trace_aligned (fuel + 1) before raw holds.1
      obtain ⟨current⟩ := countedMenu.trace_environment initial horizon scheduler fuel before
        middle command prior selected moved
      cases command with
      | wait => cases acting
      | «include» identifier => cases acting
      | application operation => cases acting
      | activate actor =>
          have sameActor : actor = hidden := Option.some.inj acting
          subst actor
          have original : before.application.attempt = originalAttempt :=
            Classical.not_not.mp notStopped
          have recalled := app.environmentStep_recall before middle (.activate hidden) moved
          have output : ∃ message ∈ app.outputs (middle.recall hidden),
              PhaseCount.event? message.payload = some (originalCoordinate hidden) := by
            rw [congrFun recalled hidden]
            exact holds.2
          have sameApplication : middle.application = before.application := by
            rw [completeActivation_law] at moved
            cases (PMF.mem_support_pure_iff _ _).mp moved
            rfl
          exact assessed_original_sent_helper_wait assessment equilibrium fuel middle hidden
            current ((congrArg PhaseRuntimeState.attempt sameApplication).trans original) output
    · rw [Function.update_of_ne own]
  have preserved (fuel : Nat) (before : app.Execution)
      (raw : (app.protocol initial horizon scheduler).Trace
        (some ⟨fuel + 1, none, before⟩))
      (holds : invariant before) (_notStopped : ¬ stop before)
      (after : app.Execution) (reached : after ∈ (app.round scheduler players before).support) :
      invariant after := by
    obtain ⟨prior⟩ := counted_idle_trace_aligned (fuel + 1) before raw holds.1
    obtain ⟨next⟩ := countedMenu.trace_round_of_admissible initial horizon scheduler players
      admissible fuel before after prior reached
    obtain ⟨message, member, named⟩ := holds.2
    exact ⟨⟨fuel, ⟨next⟩⟩,
      message, round_retains_output players before after reached hidden message member, named⟩
  exact app.runUntil_congr_of_agree_on_traces initial horizon scheduler players
    (Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩)) stop invariant agree preserved
    count remaining execution (countedMenu.toRawTrace initial horizon scheduler trace)
      ⟨⟨remaining + count, ⟨trace⟩⟩, sent⟩

end Vegas.Examples.CommitSeedBroadcast
