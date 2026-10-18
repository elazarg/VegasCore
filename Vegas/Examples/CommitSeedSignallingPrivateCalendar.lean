/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedSignallingTailExhaustion

/-! # The complete original coordinate-relative service calendar -/

noncomputable section

namespace Vegas.Examples.CommitSeedSignalling

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability
open OnePacketCommitRevealHypotheses (Player alice bob setup program)

theorem original_request_coordinate (seeds : Seeds) (current : app.Control)
    (trace : (app.protocol initial horizon (family seeds)).Trace (some current))
    (coordinate : CommitAttemptEvent graph) (owner : Player)
    (original : coordinate.attempt = originalAttempt)
    (request : current.execution.application.SeedRequest owner coordinate) :
    coordinate = originalCoordinate owner := by
  have phases := original_phases (family seeds) current trace (request.1.symm.trans original)
  obtain ⟨phase, installed, inside⟩ := request.2.1
  rw [phases] at installed
  have samePhase : phase = commitmentPhase := (Option.some.inj installed).symm
  subst phase
  have interval := (RuntimePhase.mem_events commitmentPhase coordinate.event).mp inside
  change 0 ≤ coordinate.event.val ∧ coordinate.event.val < 2 at interval
  have actor := request.2.2.2.1
  rcases coordinate with ⟨attempt, event⟩
  change attempt = originalAttempt at original
  subst attempt
  change Fin 4 at event
  fin_cases event
  · have sameOwner : owner = alice := Option.some.inj (actor.symm.trans binding_actors.1)
    subst owner
    rfl
  · have sameOwner : owner = bob := Option.some.inj (actor.symm.trans binding_actors.2)
    subst owner
    rfl
  · change 0 ≤ 2 ∧ 2 < 2 at interval
    omega
  · change 0 ≤ 3 ∧ 3 < 2 at interval
    omega

def relativeCalendar (coordinate : PhaseSeedAddress graph) (_seed : Bool) : List Nat :=
  if coordinate.1.attempt = originalAttempt then
    if coordinate.1.event = aliceBinding then [0, 2, 3] else [0, 4, 5]
  else [0]

private theorem original_calendar_value (coordinate : PhaseSeedAddress graph) (owner : Player)
    (seed : Bool) (same : coordinate.1 = originalCoordinate owner) :
    relativeCalendar coordinate seed = if owner = alice then [0, 2, 3] else [0, 4, 5] := by
  unfold relativeCalendar
  rw [same]
  fin_cases owner <;> decide

/-- The selected original scheduler family has an exact potential calendar on
all counted histories, including the no-emission exhaustion requirement. -/
theorem family_privateActivationCalendar :
    PhaseService.PrivateActivationCalendar runtime leaks bounds plan
      (setup.initialLaw.map encodeInputs) horizon seedPrior family := by
  classical
  refine ⟨relativeCalendar, ?_, ?_⟩
  · intro seeds _supported remaining owner execution trace coordinate request _unsent
    by_cases original : coordinate.1.attempt = originalAttempt
    · have same := original_request_coordinate seeds _
        (countedMenu.toRawTrace initial horizon (family seeds) trace) coordinate.1 owner original
          request
      rw [original_calendar_value coordinate owner _ same]
      rw [same] at request ⊢
      exact original_service_clocks_prefix countedMenu seeds _ trace owner rfl request
    · rw [relativeCalendar, ite_eq_right original]
      rw [tail_service_clocks countedMenu (PhaseCount.silence_onePacket runtime leaks bounds)
        seeds _ trace owner rfl coordinate.1 original request]
  · intro seeds _supported current trace coordinate owner genuine resolved empty
    obtain ⟨before, beforeTrace, kept, request⟩ := genuine
    by_cases original : coordinate.1.attempt = originalAttempt
    · have same := original_request_coordinate seeds before
        (countedMenu.toRawTrace initial horizon (family seeds) beforeTrace) coordinate.1 owner
          original request
      rw [original_calendar_value coordinate owner _ same]
      rw [same] at resolved empty ⊢
      exact original_binding_exhausted_clocks seeds current trace owner resolved empty
    · rw [relativeCalendar, ite_eq_right original]
      exact tail_episode_exhausted_clocks seeds before current beforeTrace trace kept coordinate.1
        owner original request resolved empty

end Vegas.Examples.CommitSeedSignalling
