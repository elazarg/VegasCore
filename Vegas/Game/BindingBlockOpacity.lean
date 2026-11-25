module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.BindingWindowTransport
public import Vegas.EventGraph.BarrierBlocks

@[expose] public section

/-! # Native opacity across private binding runs

Jointly varying private inputs and submitting reference kernels have the same focal traffic
law through a private binding run. The ready anchor may change. Stops are determined
by focal traffic and occur no later than completion of the whole binding block.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime EventGraph GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {deps : setup.dataflowGraph.Dependencies}
  {duration : (serviceGraph setup deps).EventId → Nat}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (serviceGraph setup deps))}

/-- Private-binding opacity holds through every traffic-determined stop no later than
completion of the whole binding block. -/
theorem bindingBlock_stopped_traffic_congr
    (relaxed : (serviceGraph setup deps).RevealRelaxedOrdered)
    {horizon count leftRemaining rightRemaining turns : Nat}
    (scheduler : (serviceApplication setup deps duration leaks).Scheduler)
    (bound : (serviceGraph setup deps).EventId → Nat)
    (start finish : Nat)
    (bindings : ∀ event : (serviceGraph setup deps).EventId, start ≤ event.val →
      event.val < finish → ∃ owner payload,
        (serviceGraph setup deps).outputLayout event = .binding owner payload)
    (barrier : ∀ event : (serviceGraph setup deps).EventId, event.val = finish →
      ((serviceGraph setup deps).outputLayout event).IsPublic)
    (focal : Player) (deviation : (serviceApplication setup deps duration leaks).Policy)
    (stop : (serviceApplication setup deps duration leaks).Execution → Prop)
    [DecidablePred stop]
    (completedStops : ∀ current : (serviceApplication setup deps duration leaks).Execution,
      BlockDone finish current.application.config → stop current)
    (determinedStop : ∀ left right : (serviceApplication setup deps duration leaks).Execution,
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal left =
        (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal right →
      (stop left ↔ stop right))
    (leftReference rightReference : (serviceGraph setup deps).BehavioralProfile)
    (leftSubmits : (serviceGraph setup deps).SubmitsBindings leftReference)
    (rightSubmits : (serviceGraph setup deps).SubmitsBindings rightReference)
    (leftStart rightStart : (serviceApplication setup deps duration leaks).Execution)
    (same : (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal leftStart =
      (bindingTraffic (serviceTimeouts setup deps duration)) leaks focal rightStart)
    (leftTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨leftRemaining + count, none, leftStart⟩))
    (rightTrace : ((serviceApplication setup deps duration leaks).protocol
      (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨rightRemaining + count, none, rightStart⟩))
    (leftInside : InBlock start finish leftStart.application.config)
    (rightInside : InBlock start finish rightStart.application.config)
    (leftCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks leftStart actor ∧
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks leftStart actor)
    (rightCanonical : ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn (serviceTimeouts setup deps duration) leaks rightStart actor ∧
        CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks rightStart actor) :
    let app := serviceApplication setup deps duration leaks
    let players := fun reference => Function.update
      (turnPolicy (serviceTimeouts setup deps duration) leaks bound turns
        (firstTurnTiming setup turns deps) reference) focal deviation
    (app.runUntil scheduler (players leftReference)
        stop count leftStart).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) =
      (app.runUntil scheduler (players rightReference)
        stop count rightStart).map
        ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) := by
  classical
  intro app players
  have shaped := bindingInterval_shaped relaxed start finish bindings barrier
  let invariant := fun (n : Nat) (current : app.Execution) =>
    (∃ remaining, Nonempty ((app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
      (some ⟨remaining + n, none, current⟩))) ∧
    (¬ BlockDone finish current.application.config →
      InBlock start finish current.application.config) ∧
    ∀ actor, actor ≠ focal →
      OwnSubmissionsAtTurn
        (serviceTimeouts setup deps duration) leaks current actor ∧
          CanonicalSlotsUsed (serviceTimeouts setup deps duration) leaks current actor
  have advance (reference : (serviceGraph setup deps).BehavioralProfile) (n : Nat)
      (current : app.Execution) (valid : invariant (n + 1) current)
      (running : ¬ BlockDone finish current.application.config)
      (next : app.Execution)
      (reached : next ∈ (app.round scheduler (players reference) current).support) :
      invariant n next := by
    obtain ⟨⟨remaining, ⟨trace⟩⟩, inside, canonical⟩ := valid
    have before : (app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨(remaining + n) + 1, none, current⟩) := by
      simpa only [Nat.add_assoc] using trace
    obtain ⟨nextTrace⟩ := app.raw_trace_round (serviceInitialLaw setup deps) horizon scheduler
      (players reference) (remaining + n) current next before reached
    have path := reactive_round_graph_steps (serviceTimeouts setup deps duration) leaks scheduler
      (players reference) current next reached
    refine ⟨⟨remaining, ⟨nextTrace⟩⟩, ?_, ?_⟩
    · intro unfinished
      exact (inside running).path shaped path unfinished
    · intro actor foreign
      obtain ⟨own, slots⟩ := canonical actor foreign
      exact canonicalSlots_round relaxed.actorSerial (by
        simpa only [players, Function.update_of_ne foreign] using
          (turnPolicy_submitsCanonically (serviceTimeouts setup deps duration) leaks bound turns
            (firstTurnTiming setup turns deps) reference actor)) (by
        simpa only [players, Function.update_of_ne foreign] using
          (sourceServiceTurnPolicy_submitsAtTurn_reference setup leaks bound turns
            (firstTurnTiming setup turns deps) reference actor)) before own slots reached
  apply ReactiveApplication.runUntil_map_congr_of_rounds app scheduler (players leftReference)
    (players rightReference) stop
    ((bindingTraffic (serviceTimeouts setup deps duration)) leaks focal) invariant invariant
  · intro n left right _leftValid _rightValid equal
    exact determinedStop left right equal
  · intro n left right leftValid rightValid equal notStopped
    have running : ¬ BlockDone finish left.application.config :=
      fun completed => notStopped (completedStops left completed)
    obtain ⟨⟨leftRest, ⟨leftCurrentTrace⟩⟩, currentLeftInside, currentLeftCanonical⟩ := leftValid
    obtain ⟨⟨rightRest, ⟨rightCurrentTrace⟩⟩, currentRightInside, currentRightCanonical⟩ :=
      rightValid
    have publics : left.application.publicView = right.application.publicView :=
      congrArg (fun value => value.2.2.2.2.2) equal
    have rightRunning : ¬ BlockDone finish right.application.config := by
      change ¬ ∀ event, event.val < finish → event ∈ right.application.config.cut.completed
      rw [← cut_eq_of_publicView_eq publics]
      exact running
    have leftBefore : (app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨(leftRest + n) + 1, none, left⟩) := by
      simpa only [Nat.add_assoc] using leftCurrentTrace
    have rightBefore : (app.protocol (serviceInitialLaw setup deps) horizon scheduler).Trace
        (some ⟨(rightRest + n) + 1, none, right⟩) := by
      simpa only [Nat.add_assoc] using rightCurrentTrace
    have unfinished : ¬ BlockDone finish left.application.config := running
    obtain ⟨anchor, owner, payload, anchorReady, outputEq⟩ :=
      exists_ready_binding_of_block_pending start finish bindings left.application.config
        (currentLeftInside running) unfinished
    have rightReady : right.application.config.cut.Ready anchor := by
      rw [← cut_eq_of_publicView_eq publics]
      exact anchorReady
    exact bindingWindow_round_opacity (turns := turns) relaxed scheduler bound outputEq
      leftReference rightReference leftSubmits rightSubmits focal deviation equal leftBefore
      rightBefore anchorReady rightReady currentLeftCanonical currentRightCanonical
  · intro n current valid notStopped next reached
    exact advance leftReference n current valid
      (fun completed => notStopped (completedStops current completed)) next reached
  · intro n current valid notStopped next reached
    exact advance rightReference n current valid
      (fun completed => notStopped (completedStops current completed)) next reached
  · exact ⟨⟨leftRemaining, ⟨leftTrace⟩⟩, fun _ => leftInside, leftCanonical⟩
  · exact ⟨⟨rightRemaining, ⟨rightTrace⟩⟩, fun _ => rightInside, rightCanonical⟩
  · exact same

end Vegas
