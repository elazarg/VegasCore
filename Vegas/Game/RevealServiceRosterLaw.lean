/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRoster

/-! # Separating the source choice from actual roster traffic

One complete granted phase of the global native policy is exactly the source
Boolean choice followed by an actual-runtime conditional timing/replay law.
The conditional branch does not mention the source policy. This is a law of
the existing interpreter, including private recall and all network state.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

theorem servicePlan_players_eq
    (left right : Player → (application setup leaks).Policy)
    (network : (runtime setup).NetworkPolicy leaks)
    (plan : List (ServiceInstruction (graph setup)))
    (noWire : ServiceInstruction.wire ∉ plan)
    (noPlayers : ∀ who, ServiceInstruction.player who ∉ plan)
    (execution : (application setup leaks).Execution) :
    (runtime setup).runInteractionPlan leaks left network plan execution =
      (runtime setup).runInteractionPlan leaks right network plan execution := by
  induction plan generalizing execution with
  | nil => rfl
  | cons instruction rest ih =>
      have step : (runtime setup).interactionStep leaks left network instruction execution =
          (runtime setup).interactionStep leaks right network instruction execution := by
        cases instruction with
        | player who => exact False.elim (noPlayers who (by simp))
        | wire => exact False.elim (noWire (by simp))
        | grant event | sample event | tick | expire event =>
            simp only [EventGraphRuntime.interactionStep, EventGraphRuntime.interactionInstruction,
              PMF.pure_bind, ReactiveApplication.dispatch,
              ReactiveApplication.Command.actor?]
            apply bind_congr_on_support _
            intro next _
            rfl
        | includeLatest event owner =>
            unfold EventGraphRuntime.interactionStep EventGraphRuntime.interactionInstruction
            simp only [PMF.pure_bind]
            unfold EventGraphRuntime.reactiveLatest
            split <;> rfl
      simp only [EventGraphRuntime.runInteractionPlan, step]
      apply bind_congr_on_support _
      intro next _
      exact ih (fun member => noWire (List.mem_cons_of_mem _ member))
        (fun who member => noPlayers who (List.mem_cons_of_mem _ member)) next

/-- The exact full phase law, including eventual inclusion and deadline
settlement. Conditioning on the source Boolean leaves only the public timing
law and replay policy; the entire native execution is retained. -/
theorem rosterPolicy_phase_law
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (profile : BehavioralProfile setup.program)
    (initial : (application setup leaks).Execution)
    (event : (graph setup).EventId) (owner : Player)
    (ready : initial.application.config.cut.Ready event)
    (owned : (graph setup).actor? event = some owner)
    (candidate : Handle (graph setup)) (raw : Raw L)
    (opening : rosterOpening? setup leaks owner event
      (initial.observe (application setup leaks) owner) = some (candidate, raw))
    (offset : (initial.recall owner).length ≤ rosterOffset setup rosters owner event)
    (network : (runtime setup).NetworkPolicy leaks) (ticks : Nat) :
    let window := (rosters event).map ServiceInstruction.player
    let tail := [.includeLatest event owner] ++ List.replicate ticks .tick ++ [.expire event]
    let phase := window ++ tail
    (runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
        network phase initial =
      (sourceChoiceLaw setup leaks profile owner
        (initial.observe (application setup leaks) owner)).bind fun disclose =>
        if disclose then (timing event owner owned).bind fun slot =>
          (runtime setup).runInteractionPlan leaks
            ((runtime setup).openingWindowPlayers leaks owner event candidate raw
              (rosterOffset setup rosters owner event) (some slot)) network phase initial
        else (runtime setup).runInteractionPlan leaks
          ((runtime setup).openingWindowPlayers leaks owner event candidate raw
            (rosterOffset setup rosters owner event)
              (none : Option (Fin ((rosters event).count owner)))) network phase initial := by
  intro window tail phase
  let choices := rosterSelection
    (sourceChoiceLaw setup leaks profile owner (initial.observe (application setup leaks) owner))
      (timing event owner owned)
  let mixed := (runtime setup).openingWindowMixturePlayers leaks owner event candidate raw
    (rosterOffset setup rosters owner event) choices
  have noWire : ServiceInstruction.wire ∉ tail := by simp [tail]
  have noPlayers : ∀ who, ServiceInstruction.player who ∉ tail := by intro who; simp [tail]
  have mixedLaw : (runtime setup).runInteractionPlan leaks
        (rosterPolicy setup leaks rosters timing profile) network phase initial =
      (runtime setup).runInteractionPlan leaks mixed network phase initial := by
    rw [show phase = window ++ tail from rfl, runInteractionPlan_append, runInteractionPlan_append]
    rw [rosterPolicy_window_eq setup leaks rosters timing profile initial initial event owner
      (soleReady_of_ready setup initial.application ready) owned candidate raw opening rfl network
      (rosters event)]
    apply bind_congr_on_support _
    intro current _
    exact servicePlan_players_eq setup leaks _ _ network tail noWire noPlayers current
  rw [mixedLaw, openingWindowMixture_law _ _ _ _ _ _ _ _ _ _ _ offset]
  change (rosterSelection _ _).bind _ = _
  rw [rosterSelection, PMF.bind_bind]
  apply bind_congr_on_support _
  intro disclose _
  cases disclose <;> simp only [Bool.false_eq_true, ↓reduceIte,
    PMF.pure_bind, PMF.bind_map, Function.comp_def]

end Vegas
