/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.SelectiveAssociation.SourceGuessSymmetry
import Interaction.ReactiveTraceDepth
import Vegas.Examples.SelectiveAssociation.SourceEvaluation

/-! # The source guess-prefix laws in the canonical behavioral protocol

The evaluator equations in this file use the existing source interaction
kernel. They connect finite behavioral histories to the concrete response
samples used by the conditional-fairness proof.
-/

noncomputable section

namespace Vegas.Examples.SelectiveAssociation.NamedSource

open Vegas Vegas.SourceProgram Interaction GameTheory GameTheory.Protocol
open GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

def controlLaw {Claim : Type} (players : Player → (application Claim).Policy) (fuel : Nat)
    (state : (application Claim).ProtocolState) : PMF (application Claim).ProtocolState :=
  (fun law => law.bind ((application Claim).controlStep (PMF.pure initial)
    horizon (scheduler Claim) players))^[fuel] (PMF.pure state)

theorem model_run_state (Claim : Type) [Fintype Claim]
    (strategy : ∀ who, (model Claim).BehavioralPolicy who) (fuel : Nat) :
    ((model Claim).runBehavioral strategy fuel).map History.state =
      controlLaw ((menu Claim).decodeProfile (PMF.pure initial)
        horizon (scheduler Claim) strategy) fuel none := by
  let players := (menu Claim).decodeProfile (PMF.pure initial)
    horizon (scheduler Claim) strategy
  have encoded : (fun who => (application Claim).encodePolicy (players who)) =
      fun who => (menu Claim).embedPolicy (PMF.pure initial) horizon (scheduler Claim)
        who (strategy who) := by
    funext who
    exact (application Claim).encode_decodePolicy _
  calc
    _ = (((model Claim).runBehavioral strategy fuel).map
        ((menu Claim).toRawHistory (PMF.pure initial) horizon (scheduler Claim))).map
          History.state := by rw [PMF.map_comp]; rfl
    _ = (InformationModel.runBehavioralFrom
        ((application Claim).information (PMF.pure initial) horizon (scheduler Claim))
        (fun who => (menu Claim).embedPolicy (PMF.pure initial)
          horizon (scheduler Claim) who (strategy who)) fuel
          ((application Claim).protocol (PMF.pure initial) horizon
            (scheduler Claim)).initHistory).map History.state := by
      rw [InformationModel.runBehavioral, (menu Claim).run_embed]
      rfl
    _ = _ := by
      rw [← InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom
        ((application Claim).information (PMF.pure initial) horizon (scheduler Claim))
        ((application Claim).singleMover (PMF.pure initial) horizon (scheduler Claim)),
        ← encoded, ReactiveApplication.run_map_state]
      rfl

theorem controlLaw_zero {Claim : Type} (players : Player → (application Claim).Policy)
    (state : (application Claim).ProtocolState) :
    controlLaw players 0 state = PMF.pure state := rfl

theorem controlLaw_succ {Claim : Type} (players : Player → (application Claim).Policy)
    (count : Nat) (state : (application Claim).ProtocolState) :
    controlLaw players (count + 1) state = (controlLaw players count state).bind
      ((application Claim).controlStep (PMF.pure initial)
        horizon (scheduler Claim) players) := by
  exact Function.iterate_succ_apply' _ _ _

theorem controlStep_initial {Claim : Type} (players : Player → (application Claim).Policy) :
    (application Claim).controlStep (PMF.pure initial) horizon (scheduler Claim) players none =
      PMF.pure (some ⟨horizon, none, root Claim⟩) := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_none,
    ReactiveApplication.transition, PMF.pure_map]
  rfl

theorem controlStep_response {Claim : Type} (players : Player → (application Claim).Policy)
    (remaining : Nat) (who : Player) (execution : (application Claim).Execution) :
    (application Claim).controlStep (PMF.pure initial) horizon (scheduler Claim) players
        (some ⟨remaining, some who, execution⟩) =
      (chooseAt players who execution).map fun action =>
        some ⟨remaining, none, execution.respond (application Claim) who action⟩ := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
    ReactiveApplication.transition, ↓reduceIte, Option.getD_some, chooseAt, ← PMF.bind_pure_comp,
        Function.comp_def]

theorem controlStep_instruction {Claim : Type} (players : Player → (application Claim).Policy)
    (remaining : Nat) (execution : (application Claim).Execution) (next : Instruction)
    (selected : calendar[execution.environmentRecall.length]? = some next) :
    (application Claim).controlStep (PMF.pure initial) horizon (scheduler Claim) players
        (some ⟨remaining + 1, none, execution⟩) =
      PMF.pure (some ⟨remaining,
        (instruction (execution.observeEnvironment (application Claim)) next).actor?
          (application Claim),
        effect execution
          (instruction (execution.observeEnvironment (application Claim)) next)⟩) := by
  simp only [ReactiveApplication.controlStep, ReactiveApplication.actor, Option.bind_some,
    ReactiveApplication.transition, scheduler, selected, Option.elim_some,
    PMF.pure_bind, effect_law, PMF.pure_map]

theorem controlLaw_add {Claim : Type} (players : Player → (application Claim).Policy)
    (first second : Nat) (state : (application Claim).ProtocolState) :
    controlLaw players (first + second) state =
      (controlLaw players first state).bind (controlLaw players second) := by
  induction second with
  | zero =>
      change controlLaw players first state = (controlLaw players first state).bind PMF.pure
      exact (PMF.bind_pure _).symm
  | succ second ih =>
      rw [Nat.add_succ, controlLaw_succ, ih, PMF.bind_bind]
      exact bind_congr_on_support _ fun next _ => (controlLaw_succ players second next).symm

def instructionCost : Instruction → Nat
  | .player _ => 2
  | _ => 1

def planCost (plan : List Instruction) : Nat := (plan.map instructionCost).sum

theorem controlLaw_dispatch {Claim : Type} (players : Player → (application Claim).Policy)
    (remaining : Nat) (execution : (application Claim).Execution) (next : Instruction)
    (selected : calendar[execution.environmentRecall.length]? = some next) :
    controlLaw players (instructionCost next) (some ⟨remaining + 1, none, execution⟩) =
      ((application Claim).dispatch players
        (instruction (execution.observeEnvironment (application Claim)) next) execution).map
          (fun execution => some ⟨remaining, none, execution⟩) := by
  cases next with
  | player who =>
      change controlLaw players (1 + 1) _ = _
      rw [controlLaw_succ, controlLaw_succ, controlLaw_zero, PMF.pure_bind,
        controlStep_instruction players remaining execution (.player who) selected]
      simp only [instruction, ReactiveApplication.Command.actor?, PMF.pure_bind]
      rw [controlStep_response]
      simp only [ReactiveApplication.dispatch, effect_law, PMF.pure_bind,
        ReactiveApplication.Command.actor?, ReactiveApplication.resume,
        ReactiveApplication.invoke, PMF.map_comp, chooseAt]
      rfl
  | application cmd =>
      change controlLaw players (0 + 1) _ = _
      rw [controlLaw_succ, controlLaw_zero, PMF.pure_bind,
        controlStep_instruction players remaining execution (.application cmd) selected]
      simp only [instruction, ReactiveApplication.Command.actor?, ReactiveApplication.dispatch,
        effect_law, PMF.pure_bind, ReactiveApplication.resume, PMF.pure_map]
  | record event =>
      have passive : (instruction (execution.observeEnvironment (application Claim))
          (.record event)).actor? (application Claim) = none := by
        change (latest (execution.observeEnvironment (application Claim)) event).actor?
          (application Claim) = none
        unfold latest
        split <;> rfl
      change controlLaw players (0 + 1) _ = _
      rw [controlLaw_succ, controlLaw_zero, PMF.pure_bind,
        controlStep_instruction players remaining execution (.record event) selected]
      simp only [ReactiveApplication.dispatch, effect_law, PMF.pure_bind, passive,
        ReactiveApplication.resume, PMF.pure_map]

theorem controlLaw_instructions {Claim : Type} (players : Player → (application Claim).Policy)
    (before rest after : List Instruction) (split : calendar = before ++ rest ++ after)
    (execution : (application Claim).Execution)
    (position : execution.environmentRecall.length = before.length)
    (remaining : Nat) (enough : rest.length ≤ remaining) :
    controlLaw players (planCost rest) (some ⟨remaining, none, execution⟩) =
      (runInstructions players rest execution).map
        (fun execution => some ⟨remaining - rest.length, none, execution⟩) := by
  induction rest generalizing before execution remaining with
  | nil =>
      simp only [planCost, List.map_nil, List.sum_nil, controlLaw_zero, runInstructions,
        PMF.pure_map, List.length_nil, Nat.sub_zero]
  | cons next rest ih =>
      have positive : 0 < remaining := by simp only [List.length_cons] at enough; omega
      obtain ⟨remaining, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : remaining ≠ 0)
      have selected : calendar[execution.environmentRecall.length]? = some next := by
        rw [position, split, List.append_assoc, List.getElem?_append_right (by omega), Nat.sub_self]
        rfl
      change controlLaw players (instructionCost next + planCost rest) _ = _
      rw [controlLaw_add, controlLaw_dispatch players remaining execution next selected,
        PMF.bind_map, runInstructions, PMF.map_bind]
      apply bind_congr_on_support _
      intro middle supported
      have cursor := (application Claim).dispatch_environmentRecall players
        (instruction (execution.observeEnvironment (application Claim)) next)
        execution middle supported
      have nextPosition : middle.environmentRecall.length = (before ++ [next]).length := by
        simp only [cursor, List.length_append, List.length_singleton, position]
      have restLaw := ih (before ++ [next])
        (by simpa only [List.append_assoc, List.singleton_append] using split)
        middle nextPosition remaining (by simpa only [List.length_cons, Nat.succ_le_succ_iff]
          using enough)
      simpa only [List.length_cons, Nat.succ_eq_add_one, Nat.add_sub_add_right,
        Function.comp_apply] using restLaw

theorem runInstructions_environmentCount {Claim : Type}
    (players : Player → (application Claim).Policy) (plan : List Instruction)
    (execution next : (application Claim).Execution)
    (reached : next ∈ (runInstructions players plan execution).support) :
    next.environmentRecall.length = execution.environmentRecall.length + plan.length := by
  induction plan generalizing execution with
  | nil =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      rfl
  | cons command rest ih =>
      obtain ⟨middle, moved, reached⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      have after := ih middle reached
      have step := (application Claim).dispatch_environmentRecall players
        (instruction (execution.observeEnvironment (application Claim)) command)
        execution middle moved
      simp only [step, List.length_append, List.length_singleton] at after
      simp only [List.length_cons]
      omega

theorem runInstructions_player {Claim : Type} (players : Player → (application Claim).Policy)
    (who : Player) (rest : List Instruction) (execution : (application Claim).Execution) :
    runInstructions players (.player who :: rest) execution =
      (chooseAt players who (effect execution (.activate who))).bind fun response =>
        runInstructions players rest
          ((effect execution (.activate who)).respond (application Claim) who response) := by
  simp only [runInstructions, instruction, ReactiveApplication.dispatch, effect_law,
    PMF.pure_bind, ReactiveApplication.Command.actor?, ReactiveApplication.resume,
    ReactiveApplication.invoke, PMF.bind_map, chooseAt, Function.comp_def]

theorem runInstructions_nil {Claim : Type} (players : Player → (application Claim).Policy)
    (execution : (application Claim).Execution) :
    runInstructions players [] execution = PMF.pure execution := rfl

theorem beforeResponse_short (event : Event) : (beforeResponse event).length < horizon := by
  fin_cases event <;> decide

theorem beforeResponse_selected (event : Event) :
    calendar[(beforeResponse event).length]? = some (.player (eventOwner event)) := by
  rw [response_split event, List.getElem?_append_right (by omega), Nat.sub_self]
  rfl

theorem controlLaw_at_response {Claim : Type} (players : Player → (application Claim).Policy)
    (event : Event) :
    controlLaw players (1 + planCost (beforeResponse event) + 1) none =
      (runInstructions players (beforeResponse event) (root Claim)).map fun execution =>
        some ⟨horizon - (beforeResponse event).length - 1, some (eventOwner event),
          effect execution (.activate (eventOwner event))⟩ := by
  have prefixLaw : controlLaw players (1 + planCost (beforeResponse event)) none =
      (runInstructions players (beforeResponse event) (root Claim)).map
        (fun execution => some ⟨horizon - (beforeResponse event).length, none, execution⟩) := by
    rw [controlLaw_add, controlLaw_succ, controlLaw_zero, PMF.pure_bind,
      controlStep_initial, PMF.pure_bind]
    exact controlLaw_instructions players [] (beforeResponse event)
      (.player (eventOwner event) :: afterResponse event) (response_split event)
      (root Claim) rfl horizon (beforeResponse_short event).le
  rw [controlLaw_succ, prefixLaw, PMF.bind_map, ← PMF.bind_pure_comp, Function.comp_def]
  apply bind_congr_on_support _
  intro execution reached
  have cursor := runInstructions_environmentCount players (beforeResponse event)
    (root Claim) execution reached
  change execution.environmentRecall.length = 0 + (beforeResponse event).length at cursor
  have selected : calendar[execution.environmentRecall.length]? =
      some (.player (eventOwner event)) := by rw [cursor, Nat.zero_add, beforeResponse_selected]
  have remaining : horizon - (beforeResponse event).length =
      (horizon - (beforeResponse event).length - 1) + 1 := by
    have bounded := beforeResponse_short event
    omega
  rw [remaining, controlStep_instruction players _ execution (.player (eventOwner event)) selected]
  rfl

theorem carol_prefix_law {Claim : Type} (players : Player → (application Claim).Policy) :
    ((runInstructions players (beforeResponse 1) (root Claim)).map
      (fun execution => effect execution (.activate carol))) =
    (bindingLaw players).map
      (fun sample => carolInput sample.first sample.second sample.binding) := by
  change (runInstructions players
    [.player alice, .player bob, .application (.grant 0), .player alice,
      .record 0, .application .tick, .application (.settle 0), .application (.grant 1)]
      (root Claim)).map _ = _
  simp only [runInstructions_player, runInstructions_application, runInstructions_record,
    runInstructions_nil, PMF.map_bind, PMF.pure_map,
    bindingLaw, PMF.map_comp]
  rfl

theorem bob_prefix_law {Claim : Type} (players : Player → (application Claim).Policy) :
    ((runInstructions players (beforeResponse 2) (root Claim)).map
      (fun execution => effect execution (.activate bob))) =
    (guessLaw players).map
      (fun sample => bobInput sample.1.first sample.1.second sample.1.binding sample.2) := by
  change (runInstructions players
    [.player alice, .player bob, .application (.grant 0), .player alice,
      .record 0, .application .tick, .application (.settle 0), .application (.grant 1),
      .player carol, .record 1, .application .tick, .application .tick,
      .application (.settle 1), .application (.grant 2)] (root Claim)).map _ = _
  simp only [runInstructions_player, runInstructions_application, runInstructions_record,
    runInstructions_nil, PMF.map_bind, PMF.pure_map,
    guessLaw, bindingLaw, PMF.bind_bind, PMF.bind_map, PMF.map_comp, Function.comp_def]
  rfl

theorem controlLaw_carol {Claim : Type} (players : Player → (application Claim).Policy) :
    controlLaw players 13 none = (bindingLaw players).map fun sample =>
      some ⟨80, some carol, carolInput sample.first sample.second sample.binding⟩ := by
  have atResponse := controlLaw_at_response players 1
  change controlLaw players 13 none =
    (runInstructions players (beforeResponse 1) (root Claim)).map (fun execution =>
      some ⟨80, some carol, effect execution (.activate carol)⟩) at atResponse
  rw [atResponse]
  have projected := congrArg (fun law => law.map fun execution =>
    some (ReactiveApplication.Control.mk 80 (some carol) execution)) (carol_prefix_law players)
  simpa only [PMF.map_comp, Function.comp_def] using projected

theorem controlLaw_bob {Claim : Type} (players : Player → (application Claim).Policy) :
    controlLaw players 20 none = (guessLaw players).map fun sample =>
      some ⟨74, some bob, bobInput sample.1.first sample.1.second sample.1.binding sample.2⟩ := by
  have atResponse := controlLaw_at_response players 2
  change controlLaw players 20 none =
    (runInstructions players (beforeResponse 2) (root Claim)).map (fun execution =>
      some ⟨74, some bob, effect execution (.activate bob)⟩) at atResponse
  rw [atResponse]
  have projected := congrArg (fun law => law.map fun execution =>
    some (ReactiveApplication.Control.mk 74 (some bob) execution)) (bob_prefix_law players)
  simpa only [PMF.map_comp, Function.comp_def] using projected

end Vegas.Examples.SelectiveAssociation.NamedSource
