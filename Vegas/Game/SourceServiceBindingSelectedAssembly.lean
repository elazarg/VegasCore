/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceBindingSelectedInput
import Vegas.Game.SourceServiceTimingMixture

/-! # The original binding timing lottery stopped at its actual selected input

The physical completion law is the marginal of one explicit timing lottery.
Each family first runs to its actual selected input or earlier completion.
Earlier completion contributes the real typed failure and existing public and
foreign traffic. A selected input retains its original before-response recall
and continues from the same actual after-response execution. Its response is
not drawn again or conditioned on an assumed visit to the selected slot.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

/-- The actual stopped typed/public law is the marginal of the original
timing lottery and actual selected-input stop. The auxiliary input is the real
before-response input, with its original own recall. A missing selected input
is actual completed failure, rather than a hypothetical absent visit. -/
theorem sourceService_binding_selected_assembly
    {Parameter : Type} (parameter : Parameter)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (players : Player → (application setup leaks).Policy)
    (turns : Nat) (timing : TurnTiming setup turns) (profile : BehavioralProfile setup.program)
    (owner : Player)
    (follows : players owner = sourceServiceTurnPolicy setup leaks bound turns timing profile owner)
    (event : (graph setup).EventId) (payload : L.Ty)
    (owned : (graph setup).actor? event = some owner)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (execution : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler players event.val execution)
    (bounded : execution.environmentRecall.length ≤ horizon) :
    let app := application setup leaks
    let output : EventGraph.FieldRef (graph setup).layout (.binding owner payload) :=
      ⟨.inr event, outputEq⟩
    let completed := fun final : app.Execution => event ∈ final.application.config.cut.completed
    let traffic := (runtime setup).bindingPublicTraffic leaks owner
    let joint := (timing event owner owned).bind fun slot =>
      let familyPlayers := Function.update players owner
        (sourceServiceTurnFamily setup leaks bound profile owner event turns slot)
      (app.runUntilHorizon scheduler familyPlayers
        (fun final => completed final ∨
          sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) ≠ none)
        horizon execution).bind fun next =>
          match sourceServiceSelectedInput? setup leaks owner event slot.val
            (next.recall owner) with
          | none => PMF.pure (slot, none, parameter, some .failure, traffic next)
          | some input =>
              (app.runUntilHorizon scheduler familyPlayers completed horizon next).map fun final =>
                (slot, some input, parameter, output.get? final.application.config.store,
                  traffic final)
    ((app.runUntilHorizon scheduler players completed horizon execution).map fun final =>
      (parameter, output.get? final.application.config.store, traffic final)) =
      joint.map (fun selected =>
        (selected.2.2.1, selected.2.2.2.1, selected.2.2.2.2)) := by
  classical
  dsimp only
  let app := application setup leaks
  let output : EventGraph.FieldRef (graph setup).layout (.binding owner payload) :=
    ⟨.inr event, outputEq⟩
  let completed := fun final : app.Execution => event ∈ final.application.config.cut.completed
  let traffic := (runtime setup).bindingPublicTraffic leaks owner
  rw [sourceService_timing_mixture scheduler players bound turns timing profile
    owner follows event owned execution boundary horizon]
  simp only [PMF.map_bind]
  apply bind_congr_on_support (timing event owner owned)
  intro slot _chosen
  let familyPlayers := Function.update players owner
    (sourceServiceTurnFamily setup leaks bound profile owner event turns slot)
  let earlier := fun final : app.Execution => completed final ∨
    sourceServiceSelectedInput? setup leaks owner event slot.val (final.recall owner) ≠ none
  have ordered := app.runUntilHorizon_eq_runUntilHorizon_bind scheduler familyPlayers earlier
    completed (fun _ done => Or.inl done) horizon execution
  have mapped := congrArg (fun law => law.map (fun final =>
    (parameter, output.get? final.application.config.store, traffic final))) ordered
  rw [mapped]
  simp only [PMF.map_bind]
  apply bind_congr_on_support
    (app.runUntilHorizon scheduler familyPlayers earlier horizon execution)
  intro next reached
  cases input : sourceServiceSelectedInput? setup leaks owner event slot.val
    (next.recall owner) with
  | none =>
      have outcome := sourceService_binding_selected_stop contract players turns timing profile
        owner follows event payload outputEq slot execution boundary bounded next reached
      have missed : completed next ∧ output.get? next.application.config.store = some .failure :=
        by
          rcases outcome with selected | missed
          · obtain ⟨_used, _before, middle, _response, _within, _actual, _config, _trace, _chosen,
              _observed, _current, _absent, _unrecorded, _canonical, _result, original⟩ := selected
            rw [input] at original
            cases original
          · exact ⟨missed.1, missed.2.2.2.2.2⟩
      have stopped : app.runUntilHorizon scheduler familyPlayers completed horizon next =
          PMF.pure next := by
        unfold ReactiveApplication.runUntilHorizon
        exact app.runUntil_of_stop scheduler familyPlayers completed _ next missed.1
      simp only [stopped, PMF.pure_map]
      rw [missed.2]
  | some original =>
      simp only [PMF.map_comp, Function.comp_def]
      rfl

end Vegas
