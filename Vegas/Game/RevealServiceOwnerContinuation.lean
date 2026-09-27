/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceOwnerSupport
import Vegas.Game.RevealServicePrefixContinuation
import Vegas.Game.RevealServiceCollection

/-! # Actual continuation execution at owner decisions

Completing an owner history executes its immediate response and the remaining
calendar. Its preceding boundary executes the same response after the already
accounted grant and activation. This equality retains complete execution state.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

private theorem grant_owner_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (watcher owner : Player) (players : Player → (application setup leaks).Policy)
    (event : (graph setup).EventId) (execution : (application setup leaks).Execution)
    (published : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id) :
    (runtime setup).runInteractionPlan leaks players ((runtime setup).reportNetwork leaks watcher)
      [.grant event, .player owner] execution =
      (players owner (execution.recall owner)
        ((ownerOpportunity setup leaks event owner execution).observe
          (application setup leaks) owner)).map
        ((ownerOpportunity setup leaks event owner execution).respond
          (application setup leaks) owner) := by
  let app := application setup leaks
  let granted : app.Execution := { execution with
    application := { execution.application with serviceGrant := some event }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.grant event)⟩] }
  have first : (runtime setup).interactionStep leaks players
      ((runtime setup).reportNetwork leaks watcher) (.grant event) execution =
      FinDist.pure granted := by
    simp only [interactionStep, interactionInstruction, FinDist.pure_bind,
      ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
      reactiveApplication, environmentStep, FinDist.map_pure,
      ReactiveApplication.Command.actor?, ReactiveApplication.resume]
    rfl
  simp only [runInteractionPlan, first, FinDist.pure_bind, FinDist.bind_pure]
  exact (runtime setup).player_instruction_published leaks players
    ((runtime setup).reportNetwork leaks watcher) granted owner published

/-- Finishing the actual active-owner state equals running the source suffix
from its preceding boundary. The two paths have identical final recalls. -/
theorem owner_finish_from_boundary
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (watcher owner : Player) (reveals : setup.program.RevealOnly)
    (players : Player → (application setup leaks).Policy)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner)
    (execution : (application setup leaks).Execution)
    (position : execution.environmentRecall.length = blockOffset event.val)
    (published : ∀ message ∈ execution.network.pending,
      message.id ∈ execution.network.ledger.map Message.id) :
    (application setup leaks).finish (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) players
      (some ⟨horizon setup watcher - blockOffset event.val - 2, some owner,
        ownerOpportunity setup leaks event owner execution⟩) =
      ((runtime setup).runInteractionPlan leaks players
        ((runtime setup).reportNetwork leaks watcher)
        (((List.finRange (eventCount setup.program)).drop event.val).flatMap
          (block setup watcher)) execution).map (application setup leaks).finished := by
  obtain ⟨rest, split⟩ := plan_split_at setup watcher event
  let after := [.includeLatest event owner, .player watcher, .wire] ++
    List.replicate (event.val + 1) .tick ++ [.expire event] ++ rest
  have split' : plan setup watcher =
      planPrefix setup watcher event.val ++ .grant event :: .player owner :: after := by
    rw [split, block_of_owner setup watcher owner event owned]
    simp only [after, List.append_assoc, List.cons_append, List.nil_append]
  have sourceSplit : plan setup watcher = planPrefix setup watcher event.val ++
      (((List.finRange (eventCount setup.program)).drop event.val).flatMap
        (block setup watcher)) := by
    change (List.finRange (eventCount setup.program)).flatMap (block setup watcher) =
      ((List.finRange (eventCount setup.program)).take event.val).flatMap
          (block setup watcher) ++ _
    rw [← List.flatMap_append, List.take_append_drop]
  have suffixEq := List.append_cancel_left (sourceSplit.symm.trans split')
  have lengthPrefix := planPrefix_length setup watcher reveals event.val event.isLt.le
  have remaining : horizon setup watcher - blockOffset event.val - 2 = after.length := by
    have lengths := congrArg List.length split'
    simp only [List.length_append, List.length_cons, lengthPrefix] at lengths
    change (plan setup watcher).length - blockOffset event.val - 2 = _
    omega
  rw [remaining, suffixEq]
  have finish := finish_owner_response setup leaks watcher owner players
    (planPrefix setup watcher event.val ++ [.grant event]) after
    (by simpa only [List.append_assoc, List.singleton_append] using split')
    (ownerOpportunity setup leaks event owner execution) (by
      simp only [ownerOpportunity, List.length_append, List.length_singleton,
        position, lengthPrefix])
  rw [finish]
  change _ = ((runtime setup).runInteractionPlan leaks players
    ((runtime setup).reportNetwork leaks watcher) ([.grant event, .player owner] ++ after)
      execution).map _
  rw [runInteractionPlan_append, grant_owner_law setup leaks watcher owner players event
    execution published, FinDist.bind_map, FinDist.map_bind]
  rfl

end Vegas.SourceProgram.RevealService
