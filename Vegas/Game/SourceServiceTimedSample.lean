/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedPolicy
import Vegas.Game.SourceServiceSampleFactorization
import Vegas.Pending.ReactiveSilentSettlement
import GameTheoryExtensions.Math.Probability.Support

/-! # Actual public sampling under the timed source policy

An actorless phase retains all passive observations and silent responses. Its
public sample has exactly the source distribution, followed by the actual
clock and expiry commands. The law retains the full native execution.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

theorem sourceServiceTimedPolicy_sample_window
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program) (event : (graph setup).EventId)
    (chance : (graph setup).actor? event = none)
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (execution : (application setup leaks).Execution)
    (sole : execution.application.publicView.SoleReady event) :
    (runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network
      (visits.map ServiceInstruction.player) execution =
      (runtime setup).runInteractionPlan leaks (fun _ => (application setup leaks).silentPolicy)
        network (visits.map ServiceInstruction.player) execution := by
  let app := application setup leaks
  induction visits generalizing execution with
  | nil => rfl
  | cons actor rest ih =>
      simp only [List.map_cons, runInteractionPlan, interactionStep, interactionInstruction,
        PMF.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Command.actor?,
        ReactiveApplication.resume, ReactiveApplication.invoke,
        ReactiveApplication.Execution.activation_samples, PMF.bind_map, PMF.bind_bind,
        Function.comp_def]
      apply bind_congr_on_support _
      intro sample _
      let activated := execution.sampledActivation app actor sample
      have law : sourceServiceTimedPolicy setup leaks rosters timing profile actor
          (activated.recall actor) (activated.observe app actor) =
            app.silentPolicy (activated.recall actor) (activated.observe app actor) := by
        have idle : (activated.observe app actor).application.publicView.ownTurn? actor = none :=
          sole.ownTurn?_foreign (by rw [chance]; simp)
        simp only [sourceServiceTimedPolicy, idle]
        rfl
      change (sourceServiceTimedPolicy setup leaks rosters timing profile actor
        (activated.recall actor) (activated.observe app actor)).bind _ = _
      rw [law]
      apply bind_congr_on_support _
      intro response _
      apply ih
      have unchanged := (runtime setup).reactive_respond_application leaks activated actor response
      rw [unchanged.2]
      exact sole

private theorem silent_window_application
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (network : (runtime setup).NetworkPolicy leaks) (visits : List Player)
    (initial final : (application setup leaks).Execution)
    (reached : final ∈ ((runtime setup).runInteractionPlan leaks
      (fun _ => (application setup leaks).silentPolicy) network
        (visits.map ServiceInstruction.player) initial).support) :
    final.application = initial.application := by
  cases visits with
  | nil => cases (PMF.mem_support_pure_iff _ _).mp reached; rfl
  | cons first rest =>
      exact ((runtime setup).silent_window_preserves leaks
        (fun _ => (application setup leaks).silentPolicy) network first initial
        (fun current who response _ _ supported =>
          (application setup leaks).silentPolicy_cases _ _ response supported)
        (fun _ => True) ⟨by simp, by simp, by simp, by simp⟩ (first :: rest) final reached).1

/-- The source draw and actual silent window disintegrate the full timed
sampling phase. Only the application component is fixed across silence; all
network observations, recalls and receipt effects remain in the execution. -/
theorem sourceServiceTimedPolicy_sample_phase_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program)
    {Γ : SourceCtx Player L} {payload : L.Ty}
    (source : Config Player L Γ) (refs : ContextRefs (graph setup).layout Γ)
    (execution : (application setup leaks).Execution)
    (agree : refs.Agrees source.state execution.application.config.store)
    (event : (graph setup).EventId) (ready : execution.application.config.cut.Ready event)
    (outputEq : (graph setup).outputLayout event = .publicData payload)
    (law : L.DistExpr (SourcePublicCtx L Γ) payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .sample payload (compilePublicDist refs law))
    (node : nodeView (graph setup) event =
      .sample payload (compilePublicDist refs law) outputEq codeEq)
    (chance : (graph setup).actor? event = none)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) :
    let app := application setup leaks
    let silentPlayers := fun _ => app.silentPolicy
    let completed := fun (current : app.Execution) value =>
      { current with
        application := execution.application.complete event ready
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) PUnit.unit)
          (cast (congrArg EventGraph.EventField.Value outputEq.symm) value)
        environmentRecall := current.environmentRecall ++
          [⟨current.observeEnvironment app, .application (.executeSample event)⟩] }
    (runtime setup).runInteractionPlan leaks
      (sourceServiceTimedPolicy setup leaks rosters timing profile) network
      ((rosters event).map ServiceInstruction.player ++
        (.sample event :: List.replicate ticks .tick ++ [.expire event])) execution =
      ((runtime setup).runInteractionPlan leaks silentPlayers network
        ((rosters event).map ServiceInstruction.player) execution).bind fun current =>
          (L.evalDist law (sourcePublicEnv source.state)).bind fun value =>
            (runtime setup).runInteractionPlan leaks silentPlayers network
              (List.replicate ticks .tick ++ [.expire event]) (completed current value) := by
  intro app silentPlayers completed
  rw [runInteractionPlan_append,
    sourceServiceTimedPolicy_sample_window setup leaks rosters timing profile event chance network
      (rosters event) execution (soleReady_of_ready setup execution.application ready)]
  apply bind_congr_on_support _
  intro current reached
  have same := silent_window_application setup leaks network (rosters event) execution current
    reached
  rw [servicePlan_players_eq setup leaks _ silentPlayers network _ (by simp) (by intro who; simp)]
  change ((runtime setup).interactionStep leaks silentPlayers network (.sample event)
    current).bind _ = _
  have sampleLaw :
      (runtime setup).interactionStep leaks silentPlayers network (.sample event) current =
      (L.evalDist law (sourcePublicEnv source.state)).map (completed current) := by
    rw [(runtime setup).interactionStep_sample]
    have currentReady : current.application.config.cut.Ready event := by rw [same]; exact ready
    have currentAgree : refs.Agrees source.state current.application.config.store := by
      rw [same]; exact agree
    rw [source_sample_environment (runtime setup) current.application event currentReady outputEq
      refs law codeEq node source.state currentAgree, PMF.map_comp]
    apply map_congr_on_support _
    intro value _
    simp only [completed, same]
    rfl
  rw [sampleLaw, PMF.bind_map]
  rfl

end Vegas
