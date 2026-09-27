/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefixBehavioral

/-! # Source-state readout before an owner's response

Granting the event and sampling passive observations consume native transitions
without changing the source-state readout. The statement retains the sampling
law and does not assume that all pending traffic is public.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem grant_activate_readout
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (watcher owner : Player) (players : Player → (application setup leaks).Policy)
    (event : (graph setup).EventId) (rank remaining cursor : Nat)
    (execution : (application setup leaks).Execution)
    (position : execution.environmentRecall.length = cursor)
    (grantAt : (plan setup watcher)[cursor]? = some (.grant event))
    (ownerAt : (plan setup watcher)[cursor + 1]? = some (.player owner)) :
    ((fun law => law.bind ((application setup leaks).controlStep (initialLaw setup)
      (horizon setup watcher) (scheduler setup leaks watcher) players))^[2]
        (FinDist.pure (some ⟨remaining + 2, none, execution⟩))).map
          (prefixReadout setup leaks rank) =
      FinDist.pure (sourcePrefix? setup rank execution.application.config) := by
  let app := application setup leaks
  let granted : app.Execution := { execution with
    application := { execution.application with serviceGrant := some event }
    environmentRecall := execution.environmentRecall ++
      [⟨execution.observeEnvironment app, .application (.grant event)⟩] }
  have first : (scheduler setup leaks watcher) execution.environmentRecall
      (execution.observeEnvironment app) = FinDist.pure (.application (.grant event)) := by
    simp only [scheduler, position, grantAt, interactionInstruction]
  have second : (scheduler setup leaks watcher) granted.environmentRecall
      (granted.observeEnvironment app) = FinDist.pure (.activate owner) := by
    simp only [scheduler, granted, List.length_append, List.length_singleton, position,
      ownerAt, interactionInstruction]
  have grantLaw : execution.environmentStep app (.application (.grant event)) =
      FinDist.pure granted := by
    simp only [ReactiveApplication.Execution.environmentStep, app, application, reactiveApplication,
      environmentStep, FinDist.map_pure]
    rfl
  have one : app.controlStep (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) players (some ⟨remaining + 2, none, execution⟩) =
      FinDist.pure (some ⟨remaining + 1, none, granted⟩) := by
    change ((scheduler setup leaks watcher) execution.environmentRecall
      (execution.observeEnvironment app)).bind _ = _
    rw [first, FinDist.pure_bind, grantLaw, FinDist.map_pure]
    rfl
  have two : app.controlStep (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher) players (some ⟨remaining + 1, none, granted⟩) =
      (granted.environmentStep app (.activate owner)).map
        (fun next => some ⟨remaining, some owner, next⟩) := by
    change ((scheduler setup leaks watcher) granted.environmentRecall
      (granted.observeEnvironment app)).bind _ = _
    rw [second, FinDist.pure_bind]
    rfl
  simp only [Function.iterate_succ_apply', Function.iterate_zero_apply, FinDist.pure_bind]
  rw [one, FinDist.pure_bind, two, FinDist.map_comp]
  simp only [ReactiveApplication.Execution.environmentStep, FinDist.map_comp, Function.comp_def,
    prefixReadout, granted]
  exact FinDist.map_const _ _

/-- The actual owner decision has the same source-state marginal as its
preceding source boundary. The two intervening native transitions grant the
event and activate the owner; they do not execute the owner's response. -/
theorem menu_owner_readout
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (responses : (application setup leaks).ResponseMenu) (watcher owner : Player)
    (reveals : setup.program.RevealOnly)
    (profile : Profile (responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).behavioralSignature)
    (event : (graph setup).EventId) (owned : (graph setup).actor? event = some owner) :
    ((responses.information (initialLaw setup) (horizon setup watcher)
      (scheduler setup leaks watcher)).runBehavioral profile
        (blockOffset event.val + 2 * event.val + 3)).map
          (fun history => prefixReadout setup leaks event.val history.state) =
      ((responses.information (initialLaw setup) (horizon setup watcher)
        (scheduler setup leaks watcher)).runBehavioral profile
          (blockOffset event.val + 2 * event.val + 1)).map
            (fun history => prefixReadout setup leaks event.val history.state) := by
  let model := responses.information (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher)
  let players := responses.decodeProfile (initialLaw setup) (horizon setup watcher)
    (scheduler setup leaks watcher) profile
  let depth := blockOffset event.val + 2 * event.val + 1
  have prefixes := menu_prefix_state setup leaks responses watcher reveals profile event.val
    event.isLt.le
  obtain ⟨rest, planEq⟩ := plan_split_at setup watcher event
  have prefixLength := planPrefix_length setup watcher reveals event.val event.isLt.le
  have grantAt : (plan setup watcher)[blockOffset event.val]? = some (.grant event) := by
    rw [planEq, List.append_assoc, List.getElem?_append_right (by omega), prefixLength,
      Nat.sub_self, block_of_owner setup watcher owner event owned]
    rfl
  have ownerAt : (plan setup watcher)[blockOffset event.val + 1]? = some (.player owner) := by
    rw [planEq, List.append_assoc, List.getElem?_append_right (by omega), prefixLength,
      Nat.add_sub_cancel_left, block_of_owner setup watcher owner event owned]
    rfl
  have room : 2 ≤ horizon setup watcher - blockOffset event.val := by
    have lengths := congrArg List.length planEq
    rw [List.length_append, List.length_append, prefixLength,
      block_length setup watcher reveals] at lengths
    change (plan setup watcher).length - blockOffset event.val ≥ 2
    omega
  change (model.runBehavioral profile (depth + 2)).map _ =
    (model.runBehavioral profile depth).map _
  rw [InformationModel.runBehavioral, InformationModel.runBehavioralFrom_add,
    FinDist.map_bind, FinDist.map_eq_bind]
  apply FinDist.bind_congr
  intro history supported
  have seen : history.state ∈
      ((model.runBehavioral profile depth).map History.state).support := by
    rw [FinDist.support_map]
    exact ⟨history, supported, rfl⟩
  rw [prefixes, FinDist.support_bind] at seen
  obtain ⟨initial, _initialSupport, reached⟩ := Set.mem_iUnion₂.mp seen
  obtain ⟨execution, executed, stateEq⟩ := FinDist.support_map .. ▸ reached
  have position : execution.environmentRecall.length = blockOffset event.val := by
    have counted := (runtime setup).runInteractionPlan_recall leaks players
      ((runtime setup).reportNetwork leaks watcher) (planPrefix setup watcher event.val)
      (ReactiveApplication.Execution.initial (application setup leaks) initial) execution executed
    simpa only [ReactiveApplication.Execution.initial, List.length_nil, Nat.zero_add,
      prefixLength] using counted
  change (model.runBehavioralFrom profile 2 history).map
    (prefixReadout setup leaks event.val ∘ History.state) = _
  rw [← FinDist.map_comp, menu_run_control_steps]
  rw [← stateEq]
  have remaining : horizon setup watcher - blockOffset event.val =
      (horizon setup watcher - blockOffset event.val - 2) + 2 := by omega
  rw [remaining]
  exact grant_activate_readout setup leaks watcher owner players event event.val _ _ execution
    position grantAt ownerAt

end Vegas.SourceProgram.RevealService
