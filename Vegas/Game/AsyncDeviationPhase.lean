/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceDeviationTraffic
import Vegas.Game.ServiceAssignedPolicy
import Vegas.Game.ServiceTimingCoupling

/-! # One deviating player through an event ready alone

Against the first-turn clients of a source profile, one player follows an
arbitrary native policy while the scheduler satisfies the asynchronous
contract. While an event is ready alone, as a public event is on a
barrier-ordered graph, every other player is silent unless it owns that event:
in a phase of the deviator or of chance the deviated profile runs as the
deviator against silence (`Vegas.runUntil_deviation_focal`), and in a phase of
another owner as a mixture of runs in which that owner decides a fixed action
(`Vegas.runUntil_deviation_decided`). This holds in every dependency mode.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}
  {deadline : (serviceGraph setup mode).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup mode))}

section Phases

/-- While an event is ready alone, no player but its actor has a turn. -/
theorem ownTurn?_none_of_alone {event : (serviceGraph setup mode).EventId}
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (state : EventGraphRuntime.State (serviceGraph setup mode))
    (ready : state.config.cut.Ready event) (player : Player)
    (other : (serviceGraph setup mode).actor? event ≠ some player) :
    state.publicView.ownTurn? player = none := by
  cases turn : state.publicView.ownTurn? player with
  | none => rfl
  | some current =>
      obtain ⟨seen, owned⟩ := PublicView.ownTurn?_spec _ player current turn
      have same := alone _ current ready ((state.publicView_eventReady current).mp seen)
      subst same
      exact (other owned).elim

/-- A running phase of an event ready alone is at the event's prefix with the
event ready. -/
private theorem phase_running {event : (serviceGraph setup mode).EventId}
    {execution : (serviceApplication setup mode deadline leaks).Execution}
    (holds : PhaseOpen event execution)
    (running : event ∉ execution.application.config.cut.completed) :
    execution.application.config.cut.Ready event := (holds.running running).2

/-- **A phase without another owner.** While an event ready alone, of the
deviator or of chance, has not completed, the deviated first-turn profile runs
as the deviator against silence. -/
theorem runUntil_deviation_focal
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId)
    (focal : (serviceGraph setup mode).actor? event = none ∨ (serviceGraph setup mode).actor?
        event = some who)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event → cut.Ready
        other → other = event) (count : Nat)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (holds : PhaseOpen event execution) : (serviceApplication setup mode deadline leaks).runUntil
    scheduler
    (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) profile who deviation)
    (fun final => event ∈ final.application.config.cut.completed) count execution =
    (serviceApplication setup mode deadline leaks).runUntil scheduler
    (focalPlayers setup leaks who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := serviceApplication setup mode deadline leaks
  apply app.runUntil_congr_of_agree scheduler _ _ _ (PhaseOpen event)
  · intro current currentHolds running command _ middle moved player active
    by_cases same : player = who
    · subst same
      simp only [deviatedTurnProfile, focalPlayers, Function.update_self]
    · simp only [deviatedTurnProfile, focalPlayers, Function.update_of_ne same]
      have activateIs : command = .activate player := by
        cases command with
        | activate actor => cases active; rfl
        | «include» => cases active
        | application => cases active
        | wait => cases active
      subst activateIs
      have sameApp := activation_application setup leaks current middle player moved
      have idle : (middle.observe app player).application.publicView.ownTurn? player = none := by
        change middle.application.publicView.ownTurn? player = none
        rw [sameApp]
        apply ownTurn?_none_of_alone alone _ (phase_running currentHolds running) player
        rcases focal with actorless | owned
        · rw [actorless]
          exact fun impossible => by cases impossible
        · rw [owned]
          exact fun equal => same (Option.some.inj equal).symm
      simp only [serviceTurnPolicy, idle]
  · intro current currentHolds running next reached
    exact currentHolds.round alone running reached
  · exact holds

/-- **A phase of another owner.** While an event ready alone of another owner
has not completed, from a legal raw history at its prefix where the owner has
had no turn at it, if that owner's source decision at the configuration is
`law` compiled to native responses, the deviated first-turn profile runs as the
`law`-mixture of the profiles in which the owner decides one fixed action and
the deviator plays against silence. -/
theorem runUntil_deviation_decided {horizon : Nat}
    (scheduler : (serviceApplication setup mode deadline leaks).Scheduler)
    (bound : (serviceGraph setup mode).EventId → Nat) (turns : Nat)
    (profile : BehavioralProfile setup.program) (who : Player)
    (deviation : (serviceApplication setup mode deadline leaks).Policy)
    (event : (serviceGraph setup mode).EventId) (owner : Player)
    (owned : (serviceGraph setup mode).actor? event = some owner)
    (honestOwner : deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) profile who
      deviation owner = serviceTurnPolicy setup mode deadline leaks bound turns
        (firstTurnTiming setup turns mode) profile owner)
    (alone : ∀ (cut : (serviceGraph setup mode).order.Cut) other, cut.Ready event →
      cut.Ready other → other = event)
    (execution : (serviceApplication setup mode deadline leaks).Execution)
    (holds : PhaseOpen event execution)
    (clean : ∀ entry ∈ execution.recall owner,
      entry.beforeView.application.publicView.ownTurn? owner ≠ some event)
    (law : PMF ((serviceGraph setup mode).Action event))
    (policy : ∀ current : (serviceApplication setup mode deadline leaks).Execution,
      current.application.config = execution.application.config →
      serviceCanonicalPolicy setup mode deadline leaks profile owner (current.recall owner)
          (current.observe (serviceApplication setup mode deadline leaks) owner) =
        law.map fun action => (serviceRuntime setup mode deadline).canonicalServiceDecision leaks
          owner (current.recall owner)
          (current.observe (serviceApplication setup mode deadline leaks) owner) event action)
    (count remaining : Nat)
    (trace : ((serviceApplication setup mode deadline leaks).protocol
      (serviceInitialLaw setup mode) horizon scheduler).Trace
        (some ⟨remaining + count, none, execution⟩)) :
    (serviceApplication setup mode deadline leaks).runUntil scheduler
        (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) profile who deviation)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      law.bind fun action => (serviceApplication setup mode deadline leaks).runUntil scheduler
        (Function.update (focalPlayers setup leaks who deviation) owner
          (decidedTurnPolicy setup leaks bound owner event action))
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  let app := serviceApplication setup mode deadline leaks
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  -- Every other player is silent: the phase runs the owner's client against the deviator.
  have others : app.runUntil scheduler
      (deviatedTurnProfile bound turns (firstTurnTiming setup turns mode) profile who deviation)
      stop count execution =
      app.runUntil scheduler (Function.update (focalPlayers setup leaks who deviation) owner
        (assignedTurnPolicy bound turns profile owner (fun _ => none))) stop count execution := by
    apply app.runUntil_congr_of_agree scheduler _ _ _ (PhaseOpen event)
    · intro current currentHolds running command _ middle moved player active
      by_cases isOwner : player = owner
      · subst isOwner
        rw [honestOwner]
        simp only [Function.update_self, assignedTurnPolicy_empty]
      · rw [Function.update_of_ne isOwner]
        by_cases isWho : player = who
        · subst isWho
          simp only [deviatedTurnProfile, focalPlayers, Function.update_self]
        · simp only [deviatedTurnProfile, focalPlayers, Function.update_of_ne isWho]
          have activateIs : command = .activate player := by
            cases command with
            | activate actor => cases active; rfl
            | «include» => cases active
            | application => cases active
            | wait => cases active
          subst activateIs
          have sameApp := activation_application setup leaks current middle player moved
          have idle : (middle.observe app player).application.publicView.ownTurn? player =
              none := by
            change middle.application.publicView.ownTurn? player = none
            rw [sameApp]
            apply ownTurn?_none_of_alone alone _ (phase_running currentHolds running) player
            rw [owned]
            exact fun equal => isOwner (Option.some.inj equal).symm
          simp only [serviceTurnPolicy, idle]
    · intro current currentHolds running next reached
      exact currentHolds.round alone running reached
    · exact holds
  -- The owner's client is the mixture of its decided clients.
  let invariant := fun current : app.Execution =>
    PhaseOpen event current ∧
      (event ∉ current.application.config.cut.completed →
        current.application.config = execution.application.config)
  have mixture := assignedTurnPolicy_runUntil_mixture (serviceInitialLaw setup mode) horizon
    scheduler (focalPlayers setup leaks who deviation) bound turns profile owner (fun _ => none)
    event rfl owned law stop invariant
    (fun rest current _ currentHolds running command _ middle moved active _ => by
      have activateIs : command = .activate owner := by
        cases command with
        | activate actor => cases active; rfl
        | «include» => cases active
        | application => cases active
        | wait => cases active
      subst activateIs
      have sameApp := activation_application setup leaks current middle owner moved
      exact policy middle (by rw [sameApp]; exact currentHolds.2 running))
    (fun rest current _ currentHolds running next reached => by
      refine ⟨currentHolds.1.round alone running reached, fun nextRunning => ?_⟩
      rcases round_configStep setup leaks scheduler _ current next reached with
        same | ⟨other, otherReady, action, member⟩
      · rw [same]
        exact currentHolds.2 running
      · have otherIs : other = event := alone _ other (phase_running currentHolds.1 running)
          otherReady
        subst otherIs
        exfalso
        apply nextRunning
        rw [current.application.config.step_cut other otherReady action _ member,
          EventOrder.Cut.mem_complete]
        exact Or.inl rfl)
    count remaining execution trace ⟨holds, fun _ => rfl⟩ clean
  rw [others, mixture]
  apply bind_congr_on_support _
  intro action _
  -- A client deciding one action at the event is the decided policy while it is ready.
  apply app.runUntil_congr_of_agree scheduler _ _ _ (PhaseOpen event)
  · intro current currentHolds running command _ middle moved player active
    by_cases isOwner : player = owner
    · subst isOwner
      simp only [Function.update_self]
      have activateIs : command = .activate player := by
        cases command with
        | activate actor => cases active; rfl
        | «include» => cases active
        | application => cases active
        | wait => cases active
      subst activateIs
      have sameApp := activation_application setup leaks current middle player moved
      have ready : middle.application.config.cut.Ready event := by
        rw [sameApp]
        exact phase_running currentHolds running
      have turn : (middle.observe app player).application.publicView.ownTurn? player =
          some event := serviceOwnTurn?_of_ready setup middle.application ready owned
      rw [assignedTurnPolicy_assigned turn (Function.update_self ..)]
    · simp only [Function.update_of_ne isOwner]
  · intro current currentHolds running next reached
    exact currentHolds.round alone running reached
  · exact holds

end Phases

end Vegas
