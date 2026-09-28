/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRosterClock
import Interaction.ReactiveRestrictedContinuation

/-! # Actual roster continuations after one local response alternative

The finite assessment evaluator, its remaining-depth fuel, and the existing
physical service-plan evaluator agree at every legal decision history. The
baseline needs only all-history admissibility, not coverage at artificial inputs.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

open Classical in
/-- A local response lottery followed by the physical baseline runs exactly
the unconsumed service suffix. The remaining horizon is derived from the actual
legal history and the service recall already present in the runtime. -/
theorem roster_local_law_state
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, menu.Admissible (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who))
    (history : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).History)
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (before rest : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ rest)
    (position : execution.environmentRecall.length = before.length)
    (law : FinDist ((menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Choice who
      ((menu.information (initialLaw setup) (rosterPlan setup rosters).length
        (rosterScheduler setup leaks rosters network)).infoOf who history.trace))) :
    let model := menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)
    let baseline := fun player => menu.restrictPolicy (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) player
        (players player)
    (model.runBehavioralFrom
      (Profile.update (sig := model.behavioralSignature) baseline who
        ((baseline who).withLaw (model.infoOf who history.trace) law))
      (2 * (rosterPlan setup rosters).length + 1 - history.trace.length) history).map
        History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        ((runtime setup).runInteractionPlan leaks players network rest
          (execution.respond (application setup leaks) who response)).map
            (application setup leaks).finished := by
  intro model baseline
  have physical := menu.run_local_law_restrict_remaining (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
      players covered history who remaining execution current law
  refine physical.trans ?_
  apply FinDist.bind_congr
  intro response _
  have traced : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Trace
      (some ⟨remaining, some who, execution⟩) := current ▸ history.trace
  have accounted := (menu.roundSupported_uniform (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
      traced).1
  change execution.environmentRecall.length + remaining = (rosterPlan setup rosters).length
    at accounted
  rw [position, split, List.length_append] at accounted
  have count : remaining = rest.length := by omega
  simp only [ReactiveApplication.finish, ReactiveApplication.resume, FinDist.pure_bind, count]
  rw [roster_segment_rounds setup leaks rosters network players before rest []
    (by simpa only [List.append_nil] using split) _
    (by rw [ReactiveApplication.respond_environmentRecall]; exact position)]

open Classical in
/-- The same physical suffix law at the complete assessment horizon used by
the standard sequential-equilibrium and continuation-comparison definitions. -/
theorem roster_local_law_complete_state
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (network : (runtime setup).NetworkPolicy leaks)
    (menu : (application setup leaks).ResponseMenu)
    (players : Player → (application setup leaks).Policy)
    (covered : ∀ who, menu.Admissible (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network) who (players who))
    (history : (menu.protocol (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).History)
    (who : Player) (remaining : Nat) (execution : (application setup leaks).Execution)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (before rest : List (ServiceInstruction (graph setup)))
    (split : rosterPlan setup rosters = before ++ rest)
    (position : execution.environmentRecall.length = before.length)
    {info : (menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).InfoState who}
    (observed : (menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).infoOf who history.trace = info)
    (law : FinDist ((menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)).Choice who info)) :
    let model := menu.information (initialLaw setup) (rosterPlan setup rosters).length
      (rosterScheduler setup leaks rosters network)
    let baseline := fun player => menu.restrictPolicy (initialLaw setup)
      (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network) player
        (players player)
    (model.runBehavioralFrom
      (Profile.update (sig := model.behavioralSignature) baseline who
        ((baseline who).withLaw info law))
      (2 * (rosterPlan setup rosters).length + 1) history).map History.state =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind fun response =>
        ((runtime setup).runInteractionPlan leaks players network rest
          (execution.respond (application setup leaks) who response)).map
            (application setup leaks).finished := by
  subst info
  intro model baseline
  let updated := Profile.update (sig := model.behavioralSignature) baseline who
    ((baseline who).withLaw (model.infoOf who history.trace) law)
  have bounded := (application setup leaks).trace_bound (initialLaw setup)
    (rosterPlan setup rosters).length (rosterScheduler setup leaks rosters network)
      (menu.toRawTrace _ _ _ history.trace)
  rw [menu.toRawTrace_length] at bounded
  have full := menu.run_eq_finish (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) updated
      (2 * (rosterPlan setup rosters).length + 1) history (by omega)
  have trimmed := menu.run_eq_finish (initialLaw setup) (rosterPlan setup rosters).length
    (rosterScheduler setup leaks rosters network) updated
      (2 * (rosterPlan setup rosters).length + 1 - history.trace.length) history (by omega)
  exact (full.trans trimmed.symm).trans
    (roster_local_law_state setup leaks rosters network menu players covered history who remaining
      execution current before rest split position law)

omit [Fintype Player] in
/-- The actual service plan splits immediately after any roster prefix into
remaining visits, protected settlement and the later source-event blocks. -/
theorem roster_phase_suffix
    (setup : Setup (Player := Player) (L := L))
    (rosters : (graph setup).EventId → List Player) (event : (graph setup).EventId)
    (owner : Player) (owned : (graph setup).actor? event = some owner) (visits : Nat) :
    rosterPlan setup rosters =
      (rosterPlanPrefix setup rosters event.val ++ [.grant event] ++
        ((rosters event).take visits).map ServiceInstruction.player) ++
      (((rosters event).drop visits).map ServiceInstruction.player ++
        (.includeLatest event owner :: List.replicate (event.val + 1) .tick ++ [.expire event]) ++
        ((List.finRange (graph setup).order.eventCount).drop (event.val + 1)).flatMap
          (rosterBlock setup rosters)) := by
  let events := List.finRange (graph setup).order.eventCount
  have split := congrArg (List.flatMap (rosterBlock setup rosters))
    (events.take_append_drop (event.val + 1))
  rw [List.flatMap_append] at split
  change rosterPlanPrefix setup rosters (event.val + 1) ++
    (events.drop (event.val + 1)).flatMap (rosterBlock setup rosters) =
      rosterPlan setup rosters at split
  rw [rosterPlanPrefix_succ] at split
  rw [← split, rosterBlock_of_owner setup rosters event owner owned]
  have divided : (rosters event).map (ServiceInstruction.player (graph := graph setup)) =
      ((rosters event).take visits).map ServiceInstruction.player ++
        ((rosters event).drop visits).map ServiceInstruction.player := by
    rw [← List.map_append, List.take_append_drop]
  rw [divided]
  simp only [List.append_assoc, List.cons_append, List.nil_append, events]

end Vegas
