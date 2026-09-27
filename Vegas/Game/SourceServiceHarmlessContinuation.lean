/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedSample
import Vegas.Pending.ReactiveReplayApplication

/-! # Transport-only responses before public sampling

A transport-only response and the remaining roster visits leave the application
law of public sampling, the clock and expiry unchanged. All physical sampling
and recall are retained; only the application law is compared.
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

end Vegas.SourceProgram.RevealService
