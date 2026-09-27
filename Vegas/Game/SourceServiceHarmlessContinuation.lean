/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedReachability
import Vegas.Game.SourceServiceTimedSample
import Vegas.Pending.ReactiveReplayApplication

/-! # Harmless choices retain the full source continuation law

At a public sample opportunity, every retained response is transport-only.
The proof retains all physical sampling and recall, then uses the actual
timed suffix law at each resulting retained boundary. No correspondence
between foreign information sites and source information sites is assumed.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- A current replay choice and the remaining player visits do not change the
application law of public sampling and its clock/expiry suffix. -/
theorem sourceService_sample_response_application_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : ∀ event who, (graph setup).actor? event = some who →
      FinDist (Fin ((rosters event).count who)))
    (profile : BehavioralProfile setup.program)
    (network : (runtime setup).NetworkPolicy leaks)
    (event : (graph setup).EventId) (chance : (graph setup).actor? event = none)
    (who : Player) (execution : (application setup leaks).Execution)
    (granted : execution.application.serviceGrant = some event)
    (response : (application setup leaks).Action)
    (transport : response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩)
    (visits : List Player) (ticks : Nat) :
    let players := sourceServiceTimedPolicy setup leaks rosters timing profile
    let ending := .sample event :: List.replicate ticks .tick ++ [.expire event]
    ((runtime setup).runInteractionPlan leaks players network
      (visits.map ServiceInstruction.player ++ ending)
      (execution.respond (application setup leaks) who response)).map
        ReactiveApplication.Execution.application =
      ((runtime setup).runInteractionPlan leaks players network ending execution).map
        ReactiveApplication.Execution.application := by
  intro players ending
  let app := application setup leaks
  let after := execution.respond app who response
  have same := ((runtime setup).replay_response_preserves leaks (fun _ => True) execution
    ⟨by simp, by simp, by simp, by simp⟩ who response transport).1
  have grant : after.application.serviceGrant = some event := by rw [same]; exact granted
  have passive : ∀ instruction ∈ ending, instruction ≠ .wire ∧
      (∀ actor, instruction ≠ .player actor) ∧
      ∀ selected actor, instruction ≠ .includeLatest selected actor := by
    intro instruction member
    simp only [ending, List.mem_cons, List.mem_append, List.mem_replicate,
      List.not_mem_nil, or_false] at member
    rcases member with (rfl | ⟨_, rfl⟩) | rfl <;> simp
  rw [runInteractionPlan_append, sourceServiceTimedPolicy_sample_window setup leaks rosters
    timing profile event chance network visits after grant, FinDist.map_bind]
  calc
    _ = ((runtime setup).runInteractionPlan leaks (fun _ => app.replayPolicy) network
        (visits.map ServiceInstruction.player) after).bind (fun _ =>
          ((runtime setup).runInteractionPlan leaks players network ending execution).map
            ReactiveApplication.Execution.application) := by
      apply FinDist.bind_congr
      intro current reached
      have unchanged := ((runtime setup).replay_window_preserves leaks
        (fun _ => app.replayPolicy) network who after
        (fun next actor action _ _ supported => app.replayPolicy_cases _ _ action supported)
        (fun _ => True) ⟨by simp, by simp, by simp, by simp⟩ visits current reached).1
      exact (runtime setup).application_service_law leaks players network ending passive
        current execution (unchanged.trans same)
    _ = _ := FinDist.bind_const _ _

variable [Fintype Player]

section

variable (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (values : bounds.CoversBindingValues)
  (capacity : (graph setup).order.eventCount ≤ bounds.candidateCount)
  (rosters : (graph setup).EventId → List Player)
  (opportunities : ∀ event owner payload,
    (graph setup).outputLayout event = .binding owner payload → owner ∈ rosters event)
  (timing : ∀ event who, (graph setup).actor? event = some who →
    FinDist (Fin ((rosters event).count who)))
  (network : (runtime setup).NetworkPolicy leaks)
  (profile : BehavioralProfile setup.program)
  (covered : ∀ who, (sourceServiceMenu setup leaks bounds rosters).Admissible
    (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) who
    (sourceServiceTimedPolicy setup leaks rosters timing profile who))
  (effective : ∀ who, (profile who).EffectiveDisclosures setup.program []
    (Revelations.initial setup.context))
  (assessment : ((sourceServiceMenu setup leaks bounds rosters).information (initialLaw setup)
    (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).BehavioralAssessment)
  (strategy : assessment.strategy = fun who =>
    (sourceServiceMenu setup leaks bounds rosters).restrictPolicy (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) who
        (sourceServiceTimedPolicy setup leaks rosters timing profile who))
  (mixed : assessment.IsFullyMixed)

include values capacity opportunities covered effective strategy mixed in
/-- Equal application laws at the next phase boundary imply equal full typed
terminal laws for two actual legal responses. The required suffix reachability
is derived from native full mixing, including responses used as deviations. -/
theorem sourceService_response_continuation_congr
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some who, execution⟩))
    (count : Nat) (within : count ≤ eventCount setup.program)
    (before tail : List (ServiceInstruction (graph setup)))
    (split : rosterPlanPrefix setup rosters count = before ++ .player who :: tail)
    (position : execution.environmentRecall.length = before.length + 1)
    (first second : (application setup leaks).Action)
    (firstAllowed : first ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (secondAllowed : second ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (same :
      ((runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing profile) network tail
        (execution.respond (application setup leaks) who first)).map
          ReactiveApplication.Execution.application =
      ((runtime setup).runInteractionPlan leaks
        (sourceServiceTimedPolicy setup leaks rosters timing profile) network tail
        (execution.respond (application setup leaks) who second)).map
          ReactiveApplication.Execution.application) :
    let players := sourceServiceTimedPolicy setup leaks rosters timing profile
    let later := ((List.finRange (graph setup).order.eventCount).drop count).flatMap
      (rosterBlock setup rosters)
    ((runtime setup).runInteractionPlan leaks players network (tail ++ later)
      (execution.respond (application setup leaks) who first)).map
        (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
      ((runtime setup).runInteractionPlan leaks players network (tail ++ later)
        (execution.respond (application setup leaks) who second)).map
          (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) := by
  intro players later
  let phase := fun response => (runtime setup).runInteractionPlan leaks players network tail
    (execution.respond (application setup leaks) who response)
  let continuation := fun state : EventGraphRuntime.State (graph setup) =>
    (setup.continuationLaw profile (sourceServicePrefix? setup count state.config)).map some
  have law (response : (application setup leaks).Action)
      (allowed : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
        (execution.recall who) (execution.observe (application setup leaks) who)) :
      ((runtime setup).runInteractionPlan leaks players network (tail ++ later)
        (execution.respond (application setup leaks) who response)).map
          (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
        ((phase response).map ReactiveApplication.Execution.application).bind continuation := by
    rw [runInteractionPlan_append, FinDist.map_bind, FinDist.bind_map]
    apply FinDist.bind_congr
    intro final reached
    have supported := roster_fullyMixed_response_prefix_support setup leaks rosters network
      (sourceServiceMenu setup leaks bounds rosters) players covered assessment strategy mixed
      who remaining execution trace count before tail split position response allowed final reached
    exact sourceServiceTimedPolicy_continuation_law setup leaks bounds values capacity rosters
      opportunities timing network profile covered effective who count within final supported
  rw [law first firstAllowed, law second secondAllowed]
  exact congrArg (fun law => law.bind continuation) same

include values capacity opportunities covered effective strategy mixed in
/-- Every legal current response in an actorless sample phase gives the same
full source terminal law, through all later source phases. -/
theorem sourceService_sample_response_source_law
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (trace : ((sourceServiceMenu setup leaks bounds rosters).protocol (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)).Trace
        (some ⟨remaining, some who, execution⟩))
    (event : (graph setup).EventId) (chance : (graph setup).actor? event = none)
    (granted : execution.application.serviceGrant = some event)
    (before : List (ServiceInstruction (graph setup))) (visits : List Player)
    (split : rosterPlanPrefix setup rosters (event.val + 1) = before ++ .player who ::
      (visits.map ServiceInstruction.player ++
        (.sample event :: List.replicate (event.val + 1) .tick ++ [.expire event])))
    (position : execution.environmentRecall.length = before.length + 1)
    (first second : (application setup leaks).Action)
    (firstAllowed : first ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (execution.recall who) (execution.observe (application setup leaks) who))
    (secondAllowed : second ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
      (execution.recall who) (execution.observe (application setup leaks) who)) :
    let players := sourceServiceTimedPolicy setup leaks rosters timing profile
    let tail := visits.map ServiceInstruction.player ++
      (.sample event :: List.replicate (event.val + 1) .tick ++ [.expire event]) ++
      ((List.finRange (graph setup).order.eventCount).drop (event.val + 1)).flatMap
        (rosterBlock setup rosters)
    ((runtime setup).runInteractionPlan leaks players network tail
      (execution.respond (application setup leaks) who first)).map
        (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
      ((runtime setup).runInteractionPlan leaks players network tail
        (execution.respond (application setup leaks) who second)).map
          (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) := by
  intro players tail
  have transport (response : (application setup leaks).Action)
      (allowed : response ∈ (sourceServiceMenu setup leaks bounds rosters).actions who
        (execution.recall who) (execution.observe (application setup leaks) who)) :
      response = ⟨none⟩ ∨ ∃ id, response = ⟨some (.replay id)⟩ := by
    have present := roster_fullyMixed_response_support setup leaks rosters network
      (sourceServiceMenu setup leaks bounds rosters) players covered assessment strategy mixed
      who remaining execution trace response allowed
    have grant : PublicView.serviceGrant
        (execution.observe (application setup leaks) who).application.publicView =
          some event := granted
    simp only [players, sourceServiceTimedPolicy, grant, chance, reduceCtorEq, ↓reduceDIte]
      at present
    exact (application setup leaks).replayPolicy_cases _ _ response present
  have left := sourceService_sample_response_application_law setup leaks rosters timing profile
    network event chance who execution granted first (transport first firstAllowed) visits
    (event.val + 1)
  have right := sourceService_sample_response_application_law setup leaks rosters timing profile
    network event chance who execution granted second (transport second secondAllowed) visits
    (event.val + 1)
  exact sourceService_response_continuation_congr setup leaks bounds values capacity rosters
    opportunities timing network profile covered effective assessment strategy mixed
    who remaining execution trace (event.val + 1) event.isLt _ _ split position first second
    firstAllowed secondAllowed (left.trans right.symm)

end

end Vegas.SourceProgram.RevealService
