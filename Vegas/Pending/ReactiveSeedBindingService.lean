/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveLocalSeedCountedLog
import Vegas.Pending.ReactiveLocalSeedReplay
import Vegas.Pending.ReactiveLocalSeedSurvivorLog
import Vegas.Pending.ReactiveLocalSeedEmissionPrefix
import Vegas.Pending.ReactiveSeedCompletion
import Vegas.Pending.ReactiveStateInvariant
import Vegas.Pending.ReactiveOnePacketMenu
import Vegas.Pending.ReactiveBindingServicePolicy

/-! # Canonical bindings under local service timing policies -/

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- A positive reply consumes precisely the current entry of the original
calendar, including repeated activations at the same clock. -/
theorem calendar_of_activation (seed : Seed) (query : CurrentSeedQuery graph)
    (answer : controller.reply seed query = .activation) :
    (controller.calendar seed)[query.activationIndex]? = some query.input.elapsed := by
  by_cases scheduled :
      (controller.calendar seed)[query.activationIndex]? = some query.input.elapsed
  · exact scheduled
  · unfold reply at answer
    rw [ite_eq_right scheduled] at answer
    cases service : controller.service seed query.input <;> rw [service] at answer <;>
      cases answer

/-- All previous activation clocks are recovered from the original seed and
the actual activation count. No remainder history is read by this recovery. -/
theorem CountedQueryLog.activation_clocks
    (seed : Seed) {log : List (LocalSeedEntry graph (app).Command)}
    (counted : CountedQueryLog log)
    (answers : ∀ entry ∈ log, controller.reply seed entry.query = entry.reply) :
    (positiveQueries log).map (fun query => query.input.elapsed) =
      (controller.calendar seed).take (positiveQueries log).length := by
  induction counted with
  | empty => rfl
  | @append past counted entry clock index ih =>
      have earlier := ih (fun prior member => answers prior (List.mem_append_left _ member))
      have current := answers entry (List.mem_append_right _ (by simp))
      cases answerEq : entry.reply with
      | activation =>
          have calendar := controller.calendar_of_activation seed entry.query
            (current.trans answerEq)
          rw [index] at calendar
          obtain ⟨within, value⟩ := List.getElem?_eq_some_iff.mp calendar
          simp only [positiveQueries, List.filterMap_append, List.filterMap_cons,
            List.filterMap_nil, answerEq, List.map_append, List.map_cons, List.map_nil,
            List.length_append, List.length_cons, List.length_nil, Nat.zero_add]
          change (positiveQueries past).map (fun query => query.input.elapsed) ++
            [entry.query.input.elapsed] =
              (controller.calendar seed).take ((positiveQueries past).length + 1)
          rw [earlier, List.take_succ_eq_append_getElem within, value]
      | resolution command | exhausted =>
          simpa only [positiveQueries, List.filterMap_append, List.filterMap_cons,
            List.filterMap_nil, answerEq, List.append_nil] using earlier

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- An actual evidence-free call appends its exact event-local envelope. Its
private registration and unrelated global traffic do not change the local clock. -/
theorem respond_environmentSeedInput_none (execution : (app).Execution)
    (owner : Player) (event : graph.EventId) (call : Submission graph)
    (named : call.packet.event? graph = some event)
    (ready : execution.application.publicView.EventReady event) :
    runtime.environmentSeedInput leaks owner event
        ((execution.respond app owner ⟨some ⟨call, .none⟩⟩).observeEnvironment app) =
      let before := runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)
      ⟨before.elapsed, before.emitted ++
        [⟨(owner, execution.network.nextSerial owner),
          ⟨call.packet, none, some ⟨event⟩⟩⟩]⟩ := by
  have publicEq := (runtime.reactive_respond_application leaks execution owner
    ⟨some ⟨call, .none⟩⟩).2
  have token := execution.application.publicView.tokenFor_of_eventReady
    call.packet event named ready
  have inputs : (execution.respond app owner ⟨some ⟨call, .none⟩⟩).network.inputs =
      execution.network.inputs ++ [⟨(owner, execution.network.nextSerial owner),
        ⟨call.packet, none, some ⟨event⟩⟩⟩] := by
    simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit]
    rw [runtime.reactiveApplication_packet_none, token]
  unfold environmentSeedInput
  change LocalSeedInput.mk _ _ = LocalSeedInput.mk _ _
  apply congrArg₂ LocalSeedInput.mk
  · exact congrArg (fun view : PublicView graph =>
      view.clock - (view.activatedAt event).getD view.clock) publicEq
  · change ((execution.respond app owner ⟨some ⟨call, .none⟩⟩).network.inputs.filter
        (fun message => message.sender = owner)).filter _ = _
    rw [inputs]
    simp [Message.sender, named]
    rfl

/-- A raw binding response uses one fixed envelope even when its private
preparation succeeds with a different value or fails. -/
theorem reactiveBinding_environmentSeedInput (execution : (app).Execution)
    (owner : Player) (event : graph.EventId) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (slot : Nat)
    (ready : execution.application.publicView.EventReady event) :
    runtime.environmentSeedInput leaks owner event
        ((execution.respond app owner
          (runtime.reactiveBinding leaks owner event payload result slot)).observeEnvironment app) =
      let before := runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)
      ⟨before.elapsed, before.emitted ++
        [⟨(owner, execution.network.nextSerial owner),
          ⟨.commitment event (owner, .prepared slot), none, some ⟨event⟩⟩⟩]⟩ := by
  exact runtime.respond_environmentSeedInput_none leaks execution owner event _ rfl ready

end Vegas.EventGraphRuntime

end


noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

/-- Apply one own-service wait/slot choice to the actual selected-event word.
A packet already emitted for this event cannot be replaced by a later choice. -/
def bindingEmissionUpdate (owner : Player) (event : graph.EventId) (serial : Nat)
    (before : List (Message Player (WitnessedPacket graph))) (choice : Option Nat) :
    List (Message Player (WitnessedPacket graph)) :=
  if before = [] then choice.toList.map fun slot =>
    ⟨(owner, serial), ⟨.commitment event (owner, .prepared slot), none, some ⟨event⟩⟩⟩
  else before

/-- A still-unused own serial is sufficient to compare the exact local
packet update; an already emitted event never allocates another envelope. -/
theorem bindingEmissionUpdate_serial_eq (owner : Player) (event : graph.EventId)
    (first second : Nat) (before : List (Message Player (WitnessedPacket graph)))
    (choice : Option Nat) (unused : before = [] → first = second) :
    bindingEmissionUpdate owner event first before choice =
      bindingEmissionUpdate owner event second before choice := by
  by_cases empty : before = []
  · rw [unused empty]
  · simp only [bindingEmissionUpdate, empty, ↓reduceIte]

/-- The exact packet word generated by all local activation-clock choices
under one original calendar, starting at an unsent activation index. -/
def bindingEmissionWord (calendar : List Nat) (choose : List Nat → Option Nat)
    (start : Nat) (owner : Player) (event : graph.EventId) (serial : Nat) :
    Nat → List (Message Player (WitnessedPacket graph))
  | 0 => []
  | index + 1 =>
      if index < start then [] else
        bindingEmissionUpdate owner event serial
          (bindingEmissionWord calendar choose start owner event serial index)
          (choose (calendar.take (index + 1)))

/-- Earlier activations contain no packet of this new unsent continuation. -/
theorem bindingEmissionWord_before (calendar : List Nat) (choose : List Nat → Option Nat)
    (start : Nat) (owner : Player) (event : graph.EventId) (serial index : Nat)
    (earlier : index ≤ start) :
    bindingEmissionWord calendar choose start owner event serial index = [] := by
  cases index with
  | zero => rfl
  | succ index => rw [bindingEmissionWord, ite_eq_left (by omega)]

end Vegas.EventGraphRuntime

end

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- The actual local update for an arbitrary pure wait-or-handle choice is
the exact envelope word determined by that choice and the unused own serial.
The private binding value does not occur in the update. -/
theorem bindingServiceResponse_environmentSeedInput (execution : (app).Execution)
    (recalled : execution.InputRecall app) (owner : Player) (event : graph.EventId)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option Nat) (ready : execution.application.publicView.EventReady event) :
    let before := runtime.environmentSeedInput leaks owner event
      (execution.observeEnvironment app)
    runtime.environmentSeedInput leaks owner event
        ((execution.respond app owner (runtime.bindingServiceResponse leaks owner event payload
          result choose (execution.recall owner)
            (execution.observe app owner))).observeEnvironment app) =
      ⟨before.elapsed, bindingEmissionUpdate owner event (execution.network.nextSerial owner)
        before.emitted (choose ((runtime.ownerActivationQueries leaks event
          (execution.recall owner)).map (fun query => query.input.elapsed) ++
            [before.elapsed]))⟩ := by
  let before := runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app)
  let history := (runtime.ownerActivationQueries leaks event (execution.recall owner)).map
    (fun query => query.input.elapsed) ++ [before.elapsed]
  let response := runtime.bindingServiceResponse leaks owner event payload result choose
    (execution.recall owner) (execution.observe app owner)
  have publicEq := (runtime.reactive_respond_application leaks execution owner response).2
  have same := runtime.seedInput_eq_of_inputRecall leaks execution recalled owner event
  have viewedReady : (execution.observe app owner).application.publicView.EventReady event := ready
  have actionEq : response = if before.emitted = [] then
      match choose history with
      | none => ⟨none⟩
      | some slot => runtime.reactiveBinding leaks owner event payload result slot
      else ⟨none⟩ := by
    unfold response bindingServiceResponse
    rw [← same]
    simp only [viewedReady, true_and]
    rfl
  have emissions : (runtime.environmentSeedInput leaks owner event
      ((execution.respond app owner response).observeEnvironment app)).emitted =
      bindingEmissionUpdate owner event (execution.network.nextSerial owner) before.emitted
        (choose history) := by
    rw [actionEq]
    by_cases empty : before.emitted = []
    · rw [ite_eq_left empty]
      cases selected : choose history with
      | none =>
          change before.emitted = _
          simp only [bindingEmissionUpdate, empty, ↓reduceIte, Option.toList_none, List.map_nil]
      | some slot =>
          rw [runtime.reactiveBinding_environmentSeedInput leaks execution owner event
            payload result slot ready]
          change before.emitted ++ _ = _
          simp only [bindingEmissionUpdate, empty, ↓reduceIte, Option.toList_some,
            List.map_cons, List.map_nil, List.nil_append]
    · rw [ite_eq_right empty]
      change before.emitted = _
      simp only [bindingEmissionUpdate, empty, ↓reduceIte]
  change LocalSeedInput.mk _ _ = LocalSeedInput.mk _ _
  apply congrArg₂ LocalSeedInput.mk
  · exact congrArg (fun view : PublicView graph =>
      view.clock - (view.activatedAt event).getD view.clock) publicEq
  · exact emissions

end Vegas.EventGraphRuntime

end


noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- Any actual remainder command without this owner's activation preserves
its complete response recall and next authored serial. -/
theorem dispatch_passive_owner (players : Player → (app).Policy)
    (owner : Player) (execution next : (app).Execution) (command : (app).Command)
    (passive : command ≠ .activate owner)
    (reached : next ∈ ((app).dispatch players command execution).support) :
    next.recall owner = execution.recall owner ∧
      next.network.nextSerial owner = execution.network.nextSerial owner := by
  obtain ⟨middle, moved, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
  have recallEq := (app).environmentStep_recall execution middle command moved
  have serialEq := (app).environmentStep_nextSerial execution middle command moved
  cases command with
  | activate actor =>
      have different : owner ≠ actor := by
        intro same
        exact passive (congrArg ReactiveApplication.Command.activate same.symm)
      change next ∈ ((players actor (middle.recall actor) (middle.observe app actor)).map
        (middle.respond app actor)).support at responded
      obtain ⟨action, chosen, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp responded
      constructor
      · rw [(app).respond_recall_other middle actor owner different action, recallEq]
      · rw [(app).respond_nextSerial, serialEq]
        simp only [different, false_and, ↓reduceIte, Nat.add_zero]
  | «include» id | application operation | wait =>
      cases (PMF.mem_support_pure_iff _ _).mp responded
      exact ⟨congrFun recallEq owner, congrFun serialEq owner⟩

end Vegas.EventGraphRuntime

end


noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- The actual response entry identifies its positive local query in the
replayed log, so the retained original seed gave that activation reply. -/
theorem replay_response_activation
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (seed : Seed) (rest : RestSeed) (execution : (app).Execution) (response : (app).Action)
    (ready : execution.application.publicView.EventReady event)
    (matched : positiveQueries (controller.replay remainder (initialMemory seed rest)
        (execution.respond app owner response).environmentRecall).log =
      runtime.ownerActivationQueries leaks event
        ((execution.respond app owner response).recall owner)) :
    controller.reply seed
      ⟨runtime.ownerSeedInput leaks event (execution.recall owner) (execution.observe app owner),
        runtime.readyActivationCount leaks event (execution.recall owner)⟩ = .activation := by
  let query : CurrentSeedQuery graph :=
    ⟨runtime.ownerSeedInput leaks event (execution.recall owner) (execution.observe app owner),
      runtime.readyActivationCount leaks event (execution.recall owner)⟩
  have member : query ∈ positiveQueries (controller.replay remainder (initialMemory seed rest)
      (execution.respond app owner response).environmentRecall).log := by
    rw [matched, runtime.respond_ownerActivationQueries, ite_eq_left ready]
    exact List.mem_append_right _ (by simp only [List.mem_singleton]; rfl)
  obtain ⟨entry, inLog, selected⟩ := List.mem_filterMap.mp member
  have answers := controller.replayFrom_answers remainder (initialMemory seed rest) []
    (execution.respond app owner response).environmentRecall (by simp only [initialMemory,
      List.not_mem_nil, false_implies, implies_true]) entry inLog
  cases answerEq : entry.reply with
  | activation =>
      change (match entry.reply with
        | .activation => some entry.query
        | _ => none) = some query at selected
      rw [answerEq] at selected
      have same := Option.some.inj selected
      change controller.reply seed query = .activation
      rw [← same]
      exact answers.trans answerEq
  | resolution command | exhausted =>
      change (match entry.reply with
        | .activation => some entry.query
        | _ => none) = some query at selected
      rw [answerEq] at selected
      cases selected

/-- Complete local activation-clock history through this response is exactly
the corresponding prefix of the immutable original calendar. -/
theorem replay_response_activation_clocks
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (seed : Seed) (rest : RestSeed) (execution : (app).Execution) (response : (app).Action)
    (ready : execution.application.publicView.EventReady event)
    (counted : CountedQueryLog (controller.replay remainder (initialMemory seed rest)
      (execution.respond app owner response).environmentRecall).log)
    (matched : positiveQueries (controller.replay remainder (initialMemory seed rest)
        (execution.respond app owner response).environmentRecall).log =
      runtime.ownerActivationQueries leaks event
        ((execution.respond app owner response).recall owner)) :
    (runtime.ownerActivationQueries leaks event (execution.recall owner)).map
        (fun query => query.input.elapsed) ++
      [(runtime.ownerSeedInput leaks event (execution.recall owner)
        (execution.observe app owner)).elapsed] =
      (controller.calendar seed).take
        (runtime.readyActivationCount leaks event (execution.recall owner) + 1) := by
  have answers := controller.replayFrom_answers remainder (initialMemory seed rest) []
    (execution.respond app owner response).environmentRecall (by simp only [initialMemory,
      List.not_mem_nil, false_implies, implies_true])
  have clocks := counted.activation_clocks controller seed answers
  rw [matched, runtime.respond_ownerActivationQueries, ite_eq_left ready,
    List.map_append, List.map_cons, List.map_nil, List.length_append, List.length_singleton,
    runtime.ownerActivationQueries_length] at clocks
  exact clocks

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- A genuine positive query advances the complete slot-choosing service
word by exactly one original-calendar activation. -/
theorem bindingServiceResponse_emissionWord_step
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (seed : Seed) (rest : RestSeed) (execution : (app).Execution)
    (recalled : execution.InputRecall app)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (start serial : Nat) (choose : List Nat → Option Nat)
    (ready : execution.application.publicView.EventReady event)
    (counted : LocalSeedController.CountedQueryLog (controller.replay remainder
      (LocalSeedController.initialMemory seed rest) (execution.respond app owner
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (execution.recall owner) (execution.observe app owner))).environmentRecall).log)
    (matched : LocalSeedController.positiveQueries (controller.replay remainder
        (LocalSeedController.initialMemory seed rest) (execution.respond app owner
          (runtime.bindingServiceResponse leaks owner event payload result choose
            (execution.recall owner) (execution.observe app owner))).environmentRecall).log =
      runtime.ownerActivationQueries leaks event ((execution.respond app owner
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (execution.recall owner) (execution.observe app owner))).recall owner))
    (started : start ≤ runtime.readyActivationCount leaks event (execution.recall owner))
    (word : (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
        (runtime.readyActivationCount leaks event (execution.recall owner)))
    (unused : (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).emitted = [] →
      execution.network.nextSerial owner = serial) :
    (runtime.environmentSeedInput leaks owner event
      ((execution.respond app owner (runtime.bindingServiceResponse leaks owner event payload
        result choose (execution.recall owner)
          (execution.observe app owner))).observeEnvironment app)).emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
        (runtime.readyActivationCount leaks event (execution.recall owner) + 1) := by
  have clocks := controller.replay_response_activation_clocks remainder seed rest execution
    (runtime.bindingServiceResponse leaks owner event payload result choose
      (execution.recall owner) (execution.observe app owner)) ready counted matched
  rw [← runtime.seedInput_eq_of_inputRecall leaks execution recalled owner event] at clocks
  have actual := congrArg LocalSeedInput.emitted
    (runtime.bindingServiceResponse_environmentSeedInput leaks execution recalled owner event
      payload result choose ready)
  rw [clocks] at actual
  rw [bindingEmissionWord, ite_eq_right (Nat.not_lt_of_ge started)]
  let selected := choose ((controller.calendar seed).take
    (runtime.readyActivationCount leaks event (execution.recall owner) + 1))
  have updated := bindingEmissionUpdate_serial_eq owner event
    (execution.network.nextSerial owner) serial _ selected unused
  have packetsEq := congrArg
    (fun packets => bindingEmissionUpdate owner event serial packets selected) word
  exact actual.trans (updated.trans packetsEq)

/-- The actual unsent response initializes the whole slot-choosing calendar
word without an initial emission-word hypothesis. -/
theorem bindingServiceResponse_initial_emissionWord
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (seed : Seed) (rest : RestSeed) (execution : (app).Execution)
    (recalled : execution.InputRecall app)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option Nat)
    (ready : execution.application.publicView.EventReady event)
    (unsent : (runtime.environmentSeedInput leaks owner event
      (execution.observeEnvironment app)).emitted = [])
    (counted : LocalSeedController.CountedQueryLog (controller.replay remainder
      (LocalSeedController.initialMemory seed rest) (execution.respond app owner
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (execution.recall owner) (execution.observe app owner))).environmentRecall).log)
    (matched : LocalSeedController.positiveQueries (controller.replay remainder
        (LocalSeedController.initialMemory seed rest) (execution.respond app owner
          (runtime.bindingServiceResponse leaks owner event payload result choose
            (execution.recall owner) (execution.observe app owner))).environmentRecall).log =
      runtime.ownerActivationQueries leaks event ((execution.respond app owner
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (execution.recall owner) (execution.observe app owner))).recall owner)) :
    (runtime.environmentSeedInput leaks owner event
      ((execution.respond app owner (runtime.bindingServiceResponse leaks owner event payload
        result choose (execution.recall owner)
          (execution.observe app owner))).observeEnvironment app)).emitted =
      bindingEmissionWord (controller.calendar seed) choose
        (runtime.readyActivationCount leaks event (execution.recall owner)) owner event
        (execution.network.nextSerial owner)
        (runtime.readyActivationCount leaks event (execution.recall owner) + 1) := by
  apply bindingServiceResponse_emissionWord_step controller remainder seed rest execution recalled
    payload result _ _ choose ready counted matched (Nat.le_refl _)
  · exact unsent.trans (bindingEmissionWord_before _ _ _ _ _ _ _ (Nat.le_refl _)).symm
  · intro _
    rfl

end Vegas.EventGraphRuntime

end


noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- An event still unsent after its concrete wait-or-slot response has not
allocated the initial own serial. -/
theorem bindingServiceResponse_unused_serial
    (execution : (app).Execution) (payload : L.Ty)
    (result : PublicationResult (L.Val payload)) (serial : Nat)
    (choose : List Nat → Option Nat)
    (ready : execution.application.publicView.EventReady event)
    (unused : (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).emitted = [] →
      execution.network.nextSerial owner = serial)
    (empty : (runtime.environmentSeedInput leaks owner event
      ((execution.respond app owner (runtime.bindingServiceResponse leaks owner event payload
        result choose (execution.recall owner)
          (execution.observe app owner))).observeEnvironment app)).emitted = []) :
    (execution.respond app owner (runtime.bindingServiceResponse leaks owner event payload result
      choose (execution.recall owner) (execution.observe app owner))).network.nextSerial owner =
        serial := by
  let before := runtime.ownerSeedInput leaks event (execution.recall owner)
    (execution.observe app owner)
  let history := (runtime.ownerActivationQueries leaks event (execution.recall owner)).map
    (fun query => query.input.elapsed) ++ [before.elapsed]
  have viewedReady : (execution.observe app owner).application.publicView.EventReady event := ready
  have actionEq : runtime.bindingServiceResponse leaks owner event payload result choose
      (execution.recall owner) (execution.observe app owner) = if before.emitted = [] then
      match choose history with
      | none => ⟨none⟩
      | some slot => runtime.reactiveBinding leaks owner event payload result slot
      else ⟨none⟩ := by
    simp only [bindingServiceResponse, viewedReady, true_and]
    rfl
  rw [actionEq] at empty ⊢
  by_cases unsentOwner : before.emitted = []
  · rw [ite_eq_left unsentOwner] at empty ⊢
    cases selected : choose history with
    | none =>
        rw [selected] at empty
        exact unused empty
    | some slot =>
        rw [selected, runtime.reactiveBinding_environmentSeedInput leaks execution owner event
          payload result slot ready] at empty
        have lengthEq := congrArg List.length empty
        simp only [List.length_append, List.length_singleton, List.length_nil] at lengthEq
        omega
  · rw [ite_eq_right unsentOwner] at empty ⊢
    exact unused empty

end Vegas.EventGraphRuntime.LocalSeedController

end


noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- A genuine command advances the original-calendar binding emission word
exactly at its owner's response. Every other command preserves that word. -/
theorem dispatch_bindingEmissionWord
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (seed : Seed) (rest : RestSeed) (execution next : (app).Execution)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (start serial : Nat) (choose : List Nat → Option Nat)
    (players : Player → (app).Policy)
    (focal : ∀ middle, middle ∈
      (execution.environmentStep app (.activate owner)).support →
      players owner (middle.recall owner) (middle.observe app owner) = PMF.pure
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (middle.recall owner) (middle.observe app owner)))
    (ready : execution.application.publicView.EventReady event)
    (genuine : controller.domain execution) (recalled : execution.InputRecall app)
    (counted : CountedQueryLog (controller.replay remainder (initialMemory seed rest)
      execution.environmentRecall).log)
    (matched : positiveQueries (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log =
      runtime.ownerActivationQueries leaks event (execution.recall owner))
    (indexed : (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner))
    (clocks : exhaustedClocks (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log =
      List.range (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed ++
        if (controller.replay remainder (initialMemory seed rest)
            execution.environmentRecall).closedAt = some
            (runtime.environmentSeedInput leaks owner event
              (execution.observeEnvironment app)).elapsed then
          [(runtime.environmentSeedInput leaks owner event
            (execution.observeEnvironment app)).elapsed] else [])
    (started : start ≤ runtime.readyActivationCount leaks event (execution.recall owner))
    (word : (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
          (runtime.readyActivationCount leaks event (execution.recall owner)))
    (unused : (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).emitted = [] →
      execution.network.nextSerial owner = serial)
    (reached : next ∈ ((app).dispatch players
      (controller.step remainder (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall) execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support) :
    (runtime.environmentSeedInput leaks owner event (next.observeEnvironment app)).emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
          (runtime.readyActivationCount leaks event (next.recall owner)) ∧
      ((runtime.environmentSeedInput leaks owner event (next.observeEnvironment app)).emitted = [] →
        next.network.nextSerial owner = serial) := by
  let memory := controller.replay remainder (initialMemory seed rest) execution.environmentRecall
  let command := (controller.step remainder memory execution.environmentRecall
    (execution.observeEnvironment app)).1
  change next ∈ ((app).dispatch players command execution).support at reached
  have indexedLength : memory.activationIndex = (positiveQueries memory.log).length := by
    rw [matched, runtime.ownerActivationQueries_length]
    exact indexed
  have nextCounted := controller.step_countedLog remainder memory execution.environmentRecall
    (execution.observeEnvironment app) counted indexedLength clocks
  have nextMatched := (controller.dispatch_ownerLog remainder memory execution next players genuine
    recalled matched indexed reached).1
  have replayEq : controller.replay remainder (initialMemory seed rest) next.environmentRecall =
      (controller.step remainder memory execution.environmentRecall
        (execution.observeEnvironment app)).2 := by
    rw [(app).dispatch_environmentRecall players command execution next reached]
    exact controller.replay_snoc remainder (initialMemory seed rest) execution.environmentRecall _
  have targetCounted : CountedQueryLog (controller.replay remainder (initialMemory seed rest)
      next.environmentRecall).log := by rw [replayEq]; exact nextCounted
  have targetMatched : positiveQueries (controller.replay remainder (initialMemory seed rest)
      next.environmentRecall).log =
      runtime.ownerActivationQueries leaks event (next.recall owner) :=
    by rw [replayEq]; exact nextMatched
  by_cases active : command = .activate owner
  · rw [active] at reached
    obtain ⟨middle, moved, responded⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
    change next ∈ ((players owner (middle.recall owner) (middle.observe app owner)).map
      (middle.respond app owner)).support at responded
    rw [focal middle moved, PMF.pure_map] at responded
    cases (PMF.mem_support_pure_iff _ _).mp responded
    have recallEq := (app).environmentStep_recall execution middle (.activate owner) moved
    have serialEq := (app).environmentStep_nextSerial execution middle (.activate owner) moved
    have middleRecall := (app).environment_inputRecall execution middle (.activate owner)
      recalled moved
    have applicationEq : middle.application = execution.application := by
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at moved
      obtain ⟨selected, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp moved
      rfl
    have middleReady : middle.application.publicView.EventReady event := by
      rw [applicationEq]
      exact ready
    have inputEq : runtime.environmentSeedInput leaks owner event (middle.observeEnvironment app) =
        runtime.environmentSeedInput leaks owner event (execution.observeEnvironment app) := by
      rw [runtime.seedInput_eq_of_inputRecall leaks middle middleRecall,
        runtime.seedInput_eq_of_inputRecall leaks execution recalled]
      exact runtime.environmentActivation_ownerSeedInput leaks execution middle owner owner event
        moved
    have countEq : runtime.readyActivationCount leaks event (middle.recall owner) =
        runtime.readyActivationCount leaks event (execution.recall owner) := by rw [recallEq]
    have afterCount : runtime.readyActivationCount leaks event
        ((middle.respond app owner (runtime.bindingServiceResponse leaks owner event payload result
          choose (middle.recall owner) (middle.observe app owner))).recall owner) =
        runtime.readyActivationCount leaks event (middle.recall owner) + 1 := by
      rw [← runtime.ownerActivationQueries_length, runtime.respond_ownerActivationQueries,
        ite_eq_left middleReady, List.length_append, List.length_singleton,
        runtime.ownerActivationQueries_length]
    rw [afterCount]
    constructor
    · apply bindingServiceResponse_emissionWord_step controller remainder seed rest middle
        middleRecall payload result start serial choose middleReady targetCounted targetMatched
      · simpa only [countEq] using started
      · simpa only [inputEq, countEq] using word
      · intro empty
        rw [serialEq]
        exact unused ((congrArg LocalSeedInput.emitted inputEq).symm.trans empty)
    · intro empty
      apply bindingServiceResponse_unused_serial middle payload result serial choose
        middleReady ?_ empty
      intro beforeEmpty
      rw [serialEq]
      exact unused ((congrArg LocalSeedInput.emitted inputEq).symm.trans beforeEmpty)
  · obtain ⟨recallEq, serialEq⟩ := runtime.dispatch_passive_owner leaks players owner execution next
      command active reached
    have invariant : (app).PolicyInvariant players (fun execution => execution.InputRecall app) :=
      { respond := fun execution who action recalled _ =>
          (app).respond_inputRecall execution who action recalled
        environment := fun execution next command recalled moved =>
          (app).environment_inputRecall execution next command recalled moved }
    have afterRecall := invariant.dispatch command execution next recalled reached
    have emissions : (runtime.environmentSeedInput leaks owner event
        (next.observeEnvironment app)).emitted =
        (runtime.environmentSeedInput leaks owner event
          (execution.observeEnvironment app)).emitted := by
      change (next.network.inputs.filter (fun message => message.sender = owner)).filter _ =
        (execution.network.inputs.filter (fun message => message.sender = owner)).filter _
      rw [afterRecall owner, recalled owner, recallEq]
    constructor
    · rw [emissions, recallEq]
      exact word
    · intro empty
      rw [serialEq]
      exact unused (emissions.symm.trans empty)

end Vegas.EventGraphRuntime.LocalSeedController

end


noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- Before actual resolution, the complete physical continuation of a pure
binding service rule has the deterministic original-calendar emission word.
Arbitrary remainder commands and foreign responses remain in the evaluator. -/
theorem runRounds_bindingEmissionWord
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (seed : Seed) (rest : RestSeed) (inputs : graph.Inputs)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (start serial entered : Nat) (choose : List Nat → Option Nat)
    (players : Player → (app).Policy)
    (episode : (app).Execution → Prop)
    (invariant : (app).PolicyInvariant players episode)
    (focal : ∀ execution middle, controller.domain execution → episode execution →
      middle ∈ (execution.environmentStep app (.activate owner)).support →
      players owner (middle.recall owner) (middle.observe app owner) = PMF.pure
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (middle.recall owner) (middle.observe app owner)))
    (preserves : ∀ execution memory next, controller.domain execution →
      execution.application.Invariant inputs →
      execution.application.activatedAt event = some entered →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next)
    (count : Nat) (execution next : (app).Execution)
    (ready : execution.application.publicView.EventReady event)
    (genuine : controller.domain execution) (episodeValid : episode execution)
    (valid : execution.application.Invariant inputs)
    (activated : execution.application.activatedAt event = some entered)
    (recalled : execution.InputRecall app)
    (counted : CountedQueryLog (controller.replay remainder (initialMemory seed rest)
      execution.environmentRecall).log)
    (unresolved : ∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log,
      entry.reply = .activation ∨ entry.reply = .exhausted)
    (matched : positiveQueries (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log =
      runtime.ownerActivationQueries leaks event (execution.recall owner))
    (indexed : (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner))
    (clocks : exhaustedClocks (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log =
      List.range (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed ++
        if (controller.replay remainder (initialMemory seed rest)
            execution.environmentRecall).closedAt = some
            (runtime.environmentSeedInput leaks owner event
              (execution.observeEnvironment app)).elapsed then
          [(runtime.environmentSeedInput leaks owner event
            (execution.observeEnvironment app)).elapsed] else [])
    (started : start ≤ runtime.readyActivationCount leaks event (execution.recall owner))
    (word : (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
          (runtime.readyActivationCount leaks event (execution.recall owner)))
    (unused : (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).emitted = [] →
      execution.network.nextSerial owner = serial)
    (remembered : ∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log, entry.query.input.emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
          entry.query.activationIndex)
    (unfinished : event ∉ next.application.config.cut.completed)
    (reached : next ∈ ((app).runRounds
      (controller.fixedScheduler remainder (initialMemory seed rest)) players count
        execution).support) :
    (runtime.environmentSeedInput leaks owner event (next.observeEnvironment app)).emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
          (runtime.readyActivationCount leaks event (next.recall owner)) ∧
      ((runtime.environmentSeedInput leaks owner event (next.observeEnvironment app)).emitted = [] →
        next.network.nextSerial owner = serial) ∧
      ∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
          next.environmentRecall).log, entry.query.input.emitted =
        bindingEmissionWord (controller.calendar seed) choose start owner event serial
          entry.query.activationIndex := by
  have recallInvariant : (app).PolicyInvariant players
      (fun execution => execution.InputRecall app) :=
    { respond := fun execution who action recalled _ =>
        (app).respond_inputRecall execution who action recalled
      environment := fun execution next command recalled moved =>
        (app).environment_inputRecall execution next command recalled moved }
  induction count generalizing execution with
  | zero =>
      cases (PMF.mem_support_pure_iff _ _).mp reached
      exact ⟨word, unused, remembered⟩
  | succ count ih =>
      obtain ⟨middle, firstRound, later⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ reached)
      let memory := controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall
      have memoryIndex : memory.activationIndex =
          runtime.readyActivationCount leaks event (execution.recall owner) := indexed
      have moved : middle ∈ ((app).dispatch players
          (controller.step remainder memory execution.environmentRecall
            (execution.observeEnvironment app)).1 execution).support := by
        simpa only [ReactiveApplication.round, fixedScheduler, PMF.pure_bind] using firstRound
      have first := runtime.reactive_dispatch_progress leaks inputs players execution middle _
        valid moved
      have joint : (next, controller.replay remainder (initialMemory seed rest)
          next.environmentRecall) ∈
          ((controller.implementation (PMF.pure seed) (PMF.pure rest) remainder).runJoint players
            count middle (controller.replay remainder (initialMemory seed rest)
              middle.environmentRecall)).support := by
        rw [controller.runJoint_replay]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨next, later, rfl⟩
      obtain ⟨ticks, progress⟩ := controller.runJoint_progress (PMF.pure seed) (PMF.pure rest)
        remainder inputs players count middle _ next _ first.invariant joint
      have middleUnfinished : event ∉ middle.application.config.cut.completed :=
        fun completed => unfinished (progress.completed completed)
      have replayEq : controller.replay remainder (initialMemory seed rest)
          middle.environmentRecall = (controller.step remainder memory execution.environmentRecall
            (execution.observeEnvironment app)).2 := by
        rw [(app).dispatch_environmentRecall players _ execution middle moved]
        exact controller.replay_snoc remainder (initialMemory seed rest)
          execution.environmentRecall _
      have middleWord := controller.dispatch_bindingEmissionWord remainder seed rest execution
        middle payload result start serial choose players
          (fun next reached => focal execution next genuine episodeValid reached)
            ready genuine recalled counted
          matched indexed clocks started word unused moved
      have middleRemembered : ∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
          middle.environmentRecall).log, entry.query.input.emitted =
          bindingEmissionWord (controller.calendar seed) choose start owner event serial
          entry.query.activationIndex := by
        rw [replayEq]
        rcases controller.step_log_eq_or_append remainder memory execution.environmentRecall
            (execution.observeEnvironment app) with unchanged | ⟨reply, appended⟩
        · rw [unchanged]
          exact remembered
        · rw [appended]
          intro entry member
          rcases List.mem_append.mp member with prior | last
          · exact remembered entry prior
          · cases List.mem_singleton.mp last
            simpa only [memoryIndex] using word
      have indexedLength : memory.activationIndex = (positiveQueries memory.log).length := by
        rw [matched, runtime.ownerActivationQueries_length]
        exact indexed
      have middleCounted := controller.step_countedLog remainder memory execution.environmentRecall
        (execution.observeEnvironment app) counted indexedLength clocks
      have middleUnresolved := controller.dispatch_log_unresolved remainder inputs players execution
        middle memory valid genuine middleUnfinished unresolved moved
      have middleMatched := controller.dispatch_ownerLog remainder memory execution middle players
        genuine recalled matched indexed moved
      have middleClocks := controller.dispatch_exhaustionRange remainder inputs players execution
        middle memory entered valid activated middleUnfinished genuine clocks moved
      have middleReady : middle.application.publicView.EventReady event := by
        apply (middle.application.publicView_eventReady event).mpr
        rcases first.ready_or_completed event
            ((execution.application.publicView_eventReady event).mp ready) with done | readyNow
        · exact False.elim (middleUnfinished done)
        · exact readyNow
      have middleStarted : start ≤ runtime.readyActivationCount leaks event (middle.recall owner) :=
        by
          have counts := congrArg List.length (runtime.dispatch_ownerActivationQueries leaks players
            execution middle _ owner event moved)
          rw [runtime.ownerActivationQueries_length, List.length_append,
            runtime.ownerActivationQueries_length] at counts
          omega
      rw [← replayEq] at middleCounted middleUnresolved middleMatched middleClocks
      exact ih middle middleReady
        (preserves execution memory middle genuine valid activated moved middleUnfinished)
        (invariant.dispatch _ execution middle episodeValid moved) first.invariant
        (first.activated event entered activated middleUnfinished)
        (recallInvariant.dispatch _ execution middle recalled moved)
        middleCounted middleUnresolved middleMatched.1 middleMatched.2 middleClocks middleStarted
        middleWord.1 middleWord.2 middleRemembered later

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

theorem runRounds_first_binding_resolution
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (seed : Seed) (rest : RestSeed) (inputs : graph.Inputs)
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (start serial entered : Nat) (choose : List Nat → Option Nat)
    (players : Player → (app).Policy)
    (episode : (app).Execution → Prop)
    (invariant : (app).PolicyInvariant players episode)
    (focal : ∀ execution middle, controller.domain execution → episode execution →
      middle ∈ (execution.environmentStep app (.activate owner)).support →
      players owner (middle.recall owner) (middle.observe app owner) = PMF.pure
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (middle.recall owner) (middle.observe app owner)))
    (preserves : ∀ execution memory next, controller.domain execution →
      execution.application.Invariant inputs →
      execution.application.activatedAt event = some entered →
      next ∈ ((app).dispatch players
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next)
    (count : Nat) (execution next : (app).Execution)
    (ready : execution.application.publicView.EventReady event)
    (genuine : controller.domain execution) (episodeValid : episode execution)
    (valid : execution.application.Invariant inputs)
    (activated : execution.application.activatedAt event = some entered)
    (recalled : execution.InputRecall app)
    (counted : CountedQueryLog (controller.replay remainder (initialMemory seed rest)
      execution.environmentRecall).log)
    (unresolved : ∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log,
      entry.reply = .activation ∨ entry.reply = .exhausted)
    (matched : positiveQueries (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log =
      runtime.ownerActivationQueries leaks event (execution.recall owner))
    (indexed : (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).activationIndex =
      runtime.readyActivationCount leaks event (execution.recall owner))
    (clocks : exhaustedClocks (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log =
      List.range (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).elapsed ++
        if (controller.replay remainder (initialMemory seed rest)
            execution.environmentRecall).closedAt = some
            (runtime.environmentSeedInput leaks owner event
              (execution.observeEnvironment app)).elapsed then
          [(runtime.environmentSeedInput leaks owner event
            (execution.observeEnvironment app)).elapsed] else [])
    (started : start ≤ runtime.readyActivationCount leaks event (execution.recall owner))
    (word : (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
          (runtime.readyActivationCount leaks event (execution.recall owner)))
    (unused : (runtime.environmentSeedInput leaks owner event
        (execution.observeEnvironment app)).emitted = [] →
      execution.network.nextSerial owner = serial)
    (remembered : ∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
        execution.environmentRecall).log, entry.query.input.emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
          entry.query.activationIndex)
    (initialUnfinished : event ∉ execution.application.config.cut.completed)
    (completed : event ∈ next.application.config.cut.completed)
    (reached : next ∈ ((app).runRounds
      (controller.fixedScheduler remainder (initialMemory seed rest)) players count
        execution).support) :
    ∃ (used : Nat) (before final : (app).Execution)
      (query : CurrentSeedQuery graph) (command : (app).Command),
      used < count ∧
        before ∈ ((app).runRounds (controller.fixedScheduler remainder (initialMemory seed rest))
          players used execution).support ∧
        event ∉ before.application.config.cut.completed ∧
        event ∈ final.application.config.cut.completed ∧
        final ∈ ((app).dispatch players
          (controller.step remainder (controller.replay remainder (initialMemory seed rest)
            before.environmentRecall) before.environmentRecall
              (before.observeEnvironment app)).1 before).support ∧
        CountedQueryLog ((controller.replay remainder (initialMemory seed rest)
          before.environmentRecall).log ++ [⟨query, .resolution command⟩]) ∧
        (∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
          before.environmentRecall).log, entry.reply = .activation ∨ entry.reply = .exhausted) ∧
        (∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
            before.environmentRecall).log ++ [⟨query, .resolution command⟩],
          controller.reply seed entry.query = entry.reply ∧
          entry.query.input.emitted =
            bindingEmissionWord (controller.calendar seed) choose start owner event serial
          entry.query.activationIndex) ∧
        (controller.replay remainder (initialMemory seed rest) final.environmentRecall).log =
          (controller.replay remainder (initialMemory seed rest) before.environmentRecall).log ++
            [⟨query, .resolution command⟩] ∧
        next ∈ ((app).runRounds (controller.fixedScheduler remainder (initialMemory seed rest))
          players (count - used - 1) final).support := by
  obtain ⟨used, before, final, query, command, within, supported, incomplete, complete, dispatched,
      recorded, priorUnresolved, answer, logged, suffix⟩ :=
    controller.runRounds_first_counted_resolution remainder seed rest inputs players entered
      preserves count execution next initialUnfinished completed reached genuine valid activated
        recalled counted unresolved matched indexed clocks
  have priorWord := controller.runRounds_bindingEmissionWord remainder seed rest inputs payload
    result start serial entered choose players episode invariant focal preserves used execution
      before
      ready
      genuine episodeValid valid activated recalled counted unresolved matched indexed clocks
        started word
        unused
        remembered incomplete supported
  have joint : (before, controller.replay remainder (initialMemory seed rest)
      before.environmentRecall) ∈
      ((controller.implementation (PMF.pure seed) (PMF.pure rest) remainder).runJoint players used
        execution (controller.replay remainder (initialMemory seed rest)
          execution.environmentRecall)).support := by
    rw [controller.runJoint_replay]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨before, supported, rfl⟩
  obtain ⟨_, _, _, priorIndex, _⟩ := controller.runJoint_survivorLog (PMF.pure seed) (PMF.pure rest)
    remainder inputs players entered preserves used execution _ before _ incomplete joint genuine
      valid activated recalled counted unresolved matched indexed clocks
  let memory := controller.replay remainder (initialMemory seed rest) before.environmentRecall
  have finalReplay : controller.replay remainder (initialMemory seed rest) final.environmentRecall =
      (controller.step remainder memory before.environmentRecall
        (before.observeEnvironment app)).2 := by
    rw [(app).dispatch_environmentRecall players _ before final dispatched]
    exact controller.replay_snoc remainder (initialMemory seed rest) before.environmentRecall _
  have finalWords : ∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
      final.environmentRecall).log, entry.query.input.emitted =
      bindingEmissionWord (controller.calendar seed) choose start owner event serial
          entry.query.activationIndex := by
    rw [finalReplay]
    rcases controller.step_log_eq_or_append remainder memory before.environmentRecall
        (before.observeEnvironment app) with unchanged | ⟨reply, appended⟩
    · rw [unchanged]
      exact priorWord.2.2
    · rw [appended]
      intro entry member
      rcases List.mem_append.mp member with earlier | last
      · exact priorWord.2.2 entry earlier
      · cases List.mem_singleton.mp last
        have indexEq : memory.activationIndex =
            runtime.readyActivationCount leaks event (before.recall owner) := priorIndex
        simpa only [indexEq] using priorWord.1
  have answers := controller.replayFrom_answers remainder (initialMemory seed rest) []
    final.environmentRecall (by intro entry member; cases member)
  refine ⟨used, before, final, query, command, within, supported, incomplete, complete, dispatched,
    recorded, priorUnresolved, ?_, logged, suffix⟩
  intro entry member
  have inFinal : entry ∈ (controller.replay remainder (initialMemory seed rest)
      final.environmentRecall).log := by rwa [logged]
  exact ⟨answers entry inFinal, finalWords entry inFinal⟩

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph))

local notation "app" => runtime.reactiveApplication leaks

/-- A prefix of own recall cannot contain an event packet absent from the
complete own emitted history. -/
theorem ownerEmissionsAtActivation_empty (event : graph.EventId)
    (past : List (app).PlayerEntry) (index : Nat)
    (unsent : ((app).outputs past).filter
      (fun message => message.payload.call.event? graph = some event) = []) :
    runtime.ownerEmissionsAtActivation leaks event past index = [] := by
  apply List.eq_nil_of_subset_nil
  intro message member
  rw [← unsent]
  obtain ⟨emitted, named⟩ := List.mem_filter.mp member
  obtain ⟨entry, inPrefix, output⟩ := List.mem_filterMap.mp emitted
  exact List.mem_filter.mpr ⟨List.mem_filterMap.mpr
    ⟨entry, List.mem_of_mem_take inPrefix, output⟩, named⟩

/-- This actual ready response preserves every earlier activation-indexed
emission prefix, even when it transmits the first packet now. -/
theorem respond_ownerEmissionsAtActivation (execution : (app).Execution)
    (owner : Player) (event : graph.EventId) (action : (app).Action) (index : Nat)
    (ready : execution.application.publicView.EventReady event)
    (earlier : index ≤ runtime.readyActivationCount leaks event (execution.recall owner)) :
    runtime.ownerEmissionsAtActivation leaks event
        ((execution.respond app owner action).recall owner) index =
      runtime.ownerEmissionsAtActivation leaks event (execution.recall owner) index := by
  rcases action with ⟨transmission⟩
  cases transmission with
  | none =>
      simpa only [ReactiveApplication.Execution.respond, ↓reduceIte] using
        runtime.ownerEmissionsAtActivation_append_ready leaks event (execution.recall owner)
          [⟨execution.observe app owner, ⟨none⟩, none⟩] index earlier
          (by intro entry member; cases List.mem_singleton.mp member; exact ready)
  | some material =>
      simpa only [ReactiveApplication.Execution.respond, ↓reduceIte] using
        runtime.ownerEmissionsAtActivation_append_ready leaks event (execution.recall owner)
          [⟨execution.observe app owner, ⟨some material⟩,
            some (execution.network.submit owner
              ((app).packet ((app).submit execution.application owner material) owner
                (execution.network.known owner) material)).1⟩] index earlier
          (by intro entry member; cases List.mem_singleton.mp member; exact ready)

end Vegas.EventGraphRuntime

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed RestSeed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- At an unsent site every real replayed query precedes this first response's
new packet. Actual recall therefore initializes the entire generated word. -/
theorem response_unsent_binding_logWord
    (remainder : SeedRemainderController runtime leaks RestSeed owner event)
    (seed : Seed) (rest : RestSeed) (execution : (app).Execution) (response : (app).Action)
    (recalled : execution.InputRecall app)
    (ready : execution.application.publicView.EventReady event)
    (unsent : (runtime.environmentSeedInput leaks owner event
      (execution.observeEnvironment app)).emitted = [])
    (choose : List Nat → Option Nat)
    (remembered : ∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
        (execution.respond app owner response).environmentRecall).log,
      entry.query.activationIndex < runtime.readyActivationCount leaks event
          ((execution.respond app owner response).recall owner) ∧
      entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        ((execution.respond app owner response).recall owner) entry.query.activationIndex) :
    ∀ entry ∈ (controller.replay remainder (initialMemory seed rest)
        (execution.respond app owner response).environmentRecall).log,
      entry.query.input.emitted = bindingEmissionWord (controller.calendar seed) choose
        (runtime.readyActivationCount leaks event (execution.recall owner)) owner event
        (execution.network.nextSerial owner)
        entry.query.activationIndex := by
  have afterCount : runtime.readyActivationCount leaks event
      ((execution.respond app owner response).recall owner) =
      runtime.readyActivationCount leaks event (execution.recall owner) + 1 := by
    rw [← runtime.ownerActivationQueries_length, runtime.respond_ownerActivationQueries,
      ite_eq_left ready, List.length_append, List.length_singleton,
      runtime.ownerActivationQueries_length]
  have ownUnsent : ((app).outputs (execution.recall owner)).filter
      (fun message => message.payload.call.event? graph = some event) = [] := by
    have inputEq := congrArg LocalSeedInput.emitted
      (runtime.seedInput_eq_of_inputRecall leaks execution recalled owner event)
    exact inputEq.symm.trans unsent
  intro entry member
  obtain ⟨bounded, emitted⟩ := remembered entry member
  have earlier : entry.query.activationIndex ≤
      runtime.readyActivationCount leaks event (execution.recall owner) := by
    rw [afterCount] at bounded
    omega
  calc
    entry.query.input.emitted = runtime.ownerEmissionsAtActivation leaks event
        ((execution.respond app owner response).recall owner) entry.query.activationIndex := emitted
    _ = runtime.ownerEmissionsAtActivation leaks event (execution.recall owner)
        entry.query.activationIndex := runtime.respond_ownerEmissionsAtActivation leaks execution
          owner event response entry.query.activationIndex ready earlier
    _ = [] := runtime.ownerEmissionsAtActivation_empty leaks event (execution.recall owner)
      entry.query.activationIndex ownUnsent
    _ = _ := (bindingEmissionWord_before _ _ _ _ _ _ _ earlier).symm

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)
  (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => runtime.reactiveApplication leaks
local notation "family" => fun values : (side : Bool) → A side =>
  controller.fixedScheduler remainder (initialMemory (values false) (values true))
local notation "mixture" => ReactiveApplication.schedulerMixture app
  (independentProduct laws) family
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "model" => ReactiveApplication.ResponseMenu.information menu
  (inputs.map State.initial) horizon (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "players" profile =>
  ReactiveApplication.ResponseMenu.decodeProfile menu
    (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler mixture) profile
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => independentProduct laws
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
    (ReactiveApplication.Execution.environmentRecall
      (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (bounds.onePacketMenu runtime leaks)
    (PMF.map (State.initial (graph := graph)) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture (runtime.reactiveApplication leaks)
        (independentProduct laws) (fun values => controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))))))]

/-- Every actual completed continuation from a clean unsent Bayes site has
its original-seed first resolving transcript generated by the pure local
wait-or-handle rule, with all initial word and domain facts derived. -/
theorem bayesBelief_first_binding_resolution
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (current : (app).Control) (acting : current.actor = some owner)
    (supported : some current ∈ (((model).bayesBelief profile owner site
      ((menu).decisionInformationAntichain (inputs.map State.initial) horizon
        (mixture).scheduler owner site) positive).map (β := (app).ProtocolState)
          (fun history => history.1.state)).support)
    (values : (side : Bool) → A side)
    (valueSupport : values ∈ ((mixture).posterior current.execution.environmentRecall).support)
    (ready : current.execution.application.publicView.EventReady event)
    (unmissed : current.execution.application.publicView.missedBindingBy owner = false)
    (unsent : (runtime.ownerSeedInput leaks event (current.execution.recall owner)
      (current.execution.observe app owner)).emitted = [])
    (payload : L.Ty) (result : PublicationResult (L.Val payload))
    (choose : List Nat → Option Nat)
    (binding : bindingOwnedBy graph owner event = true)
    (bounded : ∀ value, result = .success value → (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (admissible : ∀ clocks slot, choose clocks = some slot → slot < bounds.candidateCount ∧
      slot ∉ runtime.submittedCandidateSlots leaks (current.execution.recall owner))
    (future : Player → (app).Policy)
    (focal : future owner = fun past view => PMF.pure
      (runtime.guardedBindingServiceResponse leaks bounds owner event payload result choose
        past view))
    (coveredFuture : ∀ who past view action, action ∈ (future who past view).support →
      action ∈ (menu).actions who past view)
    (next : (app).Execution)
    (reached : next ∈ ((app).runRounds (family values) future current.remaining
      (current.execution.respond app owner
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (current.execution.recall owner) (current.execution.observe app owner)))).support)
    (completed : event ∈ next.application.config.cut.completed) :
    let start := current.execution.respond app owner (runtime.bindingServiceResponse leaks owner
      event payload result choose (current.execution.recall owner)
        (current.execution.observe app owner))
    let memory := fun execution : (app).Execution => controller.replay remainder
      (initialMemory (values false) (values true)) execution.environmentRecall
    ∃ (used : Nat) (before final : (app).Execution)
      (query : CurrentSeedQuery graph) (command : (app).Command),
      used < current.remaining ∧
        before ∈ ((app).runRounds (family values) future used start).support ∧
        event ∉ before.application.config.cut.completed ∧
        event ∈ final.application.config.cut.completed ∧
        final ∈ ((app).dispatch future
          (controller.step remainder (memory before) before.environmentRecall
            (before.observeEnvironment app)).1 before).support ∧
        CountedQueryLog ((memory before).log ++ [⟨query, .resolution command⟩]) ∧
        (∀ entry ∈ (memory before).log,
          entry.reply = .activation ∨ entry.reply = .exhausted) ∧
        (∀ entry ∈ (memory before).log ++ [⟨query, .resolution command⟩],
          controller.reply (values false) entry.query = entry.reply ∧
          entry.query.input.emitted =
            bindingEmissionWord (controller.calendar (values false)) choose
            (runtime.readyActivationCount leaks event (current.execution.recall owner)) owner event
            (current.execution.network.nextSerial owner)
            entry.query.activationIndex) ∧
        (memory final).log = (memory before).log ++ [⟨query, .resolution command⟩] ∧
        next ∈ ((app).runRounds (family values) future
          (current.remaining - used - 1) final).support := by
  classical
  let response := runtime.bindingServiceResponse leaks owner event payload result choose
    (current.execution.recall owner) (current.execution.observe app owner)
  let after := current.execution.respond app owner response
  obtain ⟨sourceHistory, _, sourceState⟩ := (PMF.mem_support_map_iff _ _ _).mp supported
  have sourceTrace : ((menu).protocol (inputs.map State.initial) horizon
      (mixture).scheduler).Trace (some current) := sourceState ▸ sourceHistory.1.trace
  have rawSourceTrace := (menu).toRawTrace (inputs.map State.initial) horizon
    (mixture).scheduler sourceTrace
  let episode := runtime.BindingServiceEpisode leaks (current.execution.recall owner)
    owner event payload result
  have episodeInvariant : (app).PolicyInvariant future episode :=
    runtime.bindingServiceEpisode_policyInvariant leaks bounds (current.execution.recall owner)
      owner event payload result choose future focal
  have episodeInitial : episode current.execution :=
    runtime.bindingServiceEpisode_initial leaks owner event payload result current.execution
  have responseEq : runtime.guardedBindingServiceResponse leaks bounds owner event payload result
      choose (current.execution.recall owner) (current.execution.observe app owner) = response :=
    runtime.guardedBindingServiceResponse_eq_at_history leaks bounds inputs horizon
      (mixture).scheduler current rawSourceTrace (current.execution.recall owner) owner event
        payload
        result choose binding bounded admissible episodeInitial
          (current.execution.observe app owner)
          rfl
  have permitted : response ∈ (menu).actions owner (current.execution.recall owner)
      (current.execution.observe app owner) := by
    rw [← responseEq]
    exact runtime.guardedBindingServiceResponse_available leaks bounds owner event payload result
      choose (current.execution.recall owner) (current.execution.observe app owner)
  have afterEpisode : episode after := episodeInvariant.respond current.execution owner response
    episodeInitial (by
      rw [focal]
      change response ∈ (PMF.pure (runtime.guardedBindingServiceResponse leaks bounds owner event
        payload result choose (current.execution.recall owner)
          (current.execution.observe app owner))).support
      rw [responseEq]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl)
  have agrees : ∀ execution middle, controller.domain execution → episode execution →
      middle ∈ (execution.environmentStep app (.activate owner)).support →
      future owner (middle.recall owner) (middle.observe app owner) = PMF.pure
        (runtime.bindingServiceResponse leaks owner event payload result choose
          (middle.recall owner) (middle.observe app owner)) := by
    intro execution middle genuine episodeValid moved
    rw [domainEq] at genuine
    obtain ⟨budget, scheduler, remaining, ⟨trace⟩, _⟩ := genuine
    have rawTrace := (menu).toRawTrace (inputs.map State.initial) budget scheduler trace
    have recallEq := (app).environmentStep_recall execution middle (.activate owner) moved
    have applicationEq : middle.application = execution.application := by
      simp only [ReactiveApplication.Execution.environmentStep, PMF.map_comp] at moved
      obtain ⟨selected, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp moved
      rfl
    rw [focal, recallEq]
    change PMF.pure (runtime.guardedBindingServiceResponse leaks bounds owner event payload result
      choose (execution.recall owner) (middle.observe app owner)) = _
    exact congrArg PMF.pure
      (runtime.guardedBindingServiceResponse_eq_at_history leaks bounds inputs budget scheduler
        ⟨remaining, none, execution⟩ rawTrace (current.execution.recall owner) owner event payload
          result choose binding bounded admissible episodeValid (middle.observe app owner)
            (congrArg (fun state => (app).observePlayer state owner) applicationEq))
  obtain ⟨setup, entered, _, valid, recalled, genuine, enteredEq, counted, unresolved,
      positiveMatch, indexMatch, remembered, clocks⟩ :=
    controller.bayesBelief_response_log_signature remainder laws bounds inputs horizon ordered
      domainEq owned profile site positive current acting supported values valueSupport ready
        unmissed response permitted
  obtain ⟨sourceSetup, count, before, _, _, _, runs, chosen, observed⟩ :=
    controller.bayesBelief_fixed_activation remainder laws bounds inputs horizon profile site
      positive current acting supported values valueSupport
  have recallInvariant : (app).PolicyInvariant (players profile)
      (fun execution => execution.InputRecall app) :=
    { respond := fun execution who action recalled _ =>
        (app).respond_inputRecall execution who action recalled
      environment := fun execution next command recalled moved =>
        (app).environment_inputRecall execution next command recalled moved }
  have beforeRecall := recallInvariant.runRounds (family values) count
    (ReactiveApplication.Execution.initial app (State.initial sourceSetup)) before
      ((app).initial_inputRecall _) runs
  have sourceRecall := (app).environment_inputRecall before current.execution (.activate owner)
    beforeRecall observed
  have unsentEnvironment : (runtime.environmentSeedInput leaks owner event
      (current.execution.observeEnvironment app)).emitted = [] :=
    (congrArg LocalSeedInput.emitted (runtime.seedInput_eq_of_inputRecall leaks current.execution
      sourceRecall owner event)).trans unsent
  have initialWord := bindingServiceResponse_initial_emissionWord controller remainder
    (values false) (values true) current.execution sourceRecall payload result choose ready
      unsentEnvironment counted positiveMatch
  have initialUnused := bindingServiceResponse_unused_serial current.execution payload result
    (current.execution.network.nextSerial owner) choose ready (fun _ => rfl)
  have initialRemembered := controller.response_unsent_binding_logWord remainder (values false)
    (values true) current.execution response sourceRecall ready unsentEnvironment choose remembered
  have publicEq :=
    (runtime.reactive_respond_application leaks current.execution owner response).2
  have afterReady : after.application.publicView.EventReady event := by
    change (current.execution.respond app owner response).application.publicView.EventReady event
    rw [publicEq]
    exact ready
  have afterCount : runtime.readyActivationCount leaks event (after.recall owner) =
      runtime.readyActivationCount leaks event (current.execution.recall owner) + 1 := by
    change runtime.readyActivationCount leaks event
      ((current.execution.respond app owner response).recall owner) = _
    rw [← runtime.ownerActivationQueries_length, runtime.respond_ownerActivationQueries,
      ite_eq_left ready, List.length_append, List.length_singleton,
      runtime.ownerActivationQueries_length]
  have started : runtime.readyActivationCount leaks event (current.execution.recall owner) ≤
      runtime.readyActivationCount leaks event (after.recall owner) := by
    rw [afterCount]
    omega
  rw [← afterCount] at initialWord
  have initialUnfinished := ((after.application.publicView_eventReady event).mp afterReady).1
  have preserves : ∀ execution memory next, controller.domain execution →
      execution.application.Invariant setup →
      execution.application.activatedAt event = some entered →
      next ∈ ((app).dispatch future
        (controller.step remainder memory execution.environmentRecall
          (execution.observeEnvironment app)).1 execution).support →
      event ∉ next.application.config.cut.completed → controller.domain next := by
    intro execution memory next genuine valid active moved incomplete
    rw [domainEq] at genuine ⊢
    exact runtime.countedSeedDomain_dispatch_of_activated_survives leaks bounds inputs ordered
      future coveredFuture owner event owned execution next genuine setup valid entered active
        _ moved incomplete
  exact controller.runRounds_first_binding_resolution remainder (values false) (values true) setup
    payload result (runtime.readyActivationCount leaks event (current.execution.recall owner))
      (current.execution.network.nextSerial owner) entered choose future episode episodeInvariant
        agrees preserves
        current.remaining after next afterReady genuine afterEpisode valid enteredEq recalled
          counted
          unresolved
          positiveMatch indexMatch clocks started initialWord initialUnused initialRemembered
            initialUnfinished completed reached

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {Seed : Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks Seed owner event)

local notation "app" => runtime.reactiveApplication leaks

/-- Two correctly counted local logs of equal length agree when both use the
same original seed and the same activation-indexed emitted packet prefixes. -/
theorem CountedQueryLog.eq_of_seed_replies
    (seed : Seed) (emittedAt : Nat → List (Message Player (WitnessedPacket graph)))
    {first second : List (LocalSeedEntry graph (app).Command)}
    (left : CountedQueryLog first) (right : CountedQueryLog second)
    (leftReplies : ∀ entry ∈ first, controller.reply seed entry.query = entry.reply)
    (rightReplies : ∀ entry ∈ second, controller.reply seed entry.query = entry.reply)
    (leftEmitted : ∀ entry ∈ first,
      entry.query.input.emitted = emittedAt entry.query.activationIndex)
    (rightEmitted : ∀ entry ∈ second,
      entry.query.input.emitted = emittedAt entry.query.activationIndex)
    (lengths : first.length = second.length) : first = second := by
  induction left generalizing second with
  | empty =>
      cases second with
      | nil => rfl
      | cons head tail => simp only [List.length_nil, List.length_cons] at lengths; omega
  | @append past recorded entry clock index ih =>
      cases right with
      | empty =>
          simp only [List.length_append, List.length_singleton, List.length_nil] at lengths
          omega
      | @append other recordedOther otherEntry otherClock otherIndex =>
          have earlierLengths : past.length = other.length := by
            simpa only [List.length_append, List.length_singleton, Nat.add_right_cancel_iff]
              using lengths
          have earlierEq := ih recordedOther
            (fun prior member => leftReplies prior (List.mem_append_left _ member))
            (fun prior member => rightReplies prior (List.mem_append_left _ member))
            (fun prior member => leftEmitted prior (List.mem_append_left _ member))
            (fun prior member => rightEmitted prior (List.mem_append_left _ member)) earlierLengths
          subst other
          have elapsedEq := clock.trans otherClock.symm
          have indexEq := index.trans otherIndex.symm
          have leftMember : entry ∈ past ++ [entry] := List.mem_append_right _ (by simp)
          have rightMember : otherEntry ∈ past ++ [otherEntry] :=
            List.mem_append_right _ (by simp)
          have emittedEq : entry.query.input.emitted = otherEntry.query.input.emitted := by
            rw [leftEmitted entry leftMember, rightEmitted otherEntry rightMember, indexEq]
          have inputEq : entry.query.input = otherEntry.query.input :=
            congrArg₂ (fun clock packets => (⟨clock, packets⟩ : LocalSeedInput graph))
              elapsedEq emittedEq
          have queryEq : entry.query = otherEntry.query :=
            congrArg₂ (fun input index => (⟨input, index⟩ : CurrentSeedQuery graph)) inputEq indexEq
          have replyEq : entry.reply = otherEntry.reply := by
            rw [← leftReplies entry leftMember, ← rightReplies otherEntry rightMember, queryEq]
          have entryEq : entry = otherEntry :=
            congrArg₂ (fun query reply => (⟨query, reply⟩ : LocalSeedEntry graph (app).Command))
              queryEq replyEq
          rw [entryEq]

/-- Every initial segment still carries the actual local clock/index counters. -/
theorem CountedQueryLog.take
    {log : List (LocalSeedEntry graph (app).Command)} (recorded : CountedQueryLog log)
    (count : Nat) : CountedQueryLog (log.take count) := by
  induction recorded with
  | empty => simpa only [List.take_nil] using CountedQueryLog.empty
  | @append past recorded entry clock index ih =>
      by_cases earlier : count ≤ past.length
      · rw [List.take_append_of_le_length earlier]
        exact ih
      · rw [List.take_of_length_le (by
          simp only [List.length_append, List.length_singleton]
          omega)]
        exact CountedQueryLog.append recorded entry clock index

/-- Equal original seeds and own-service emitted prefixes force the shorter
actual local query log to be an initial segment of the longer one. -/
theorem CountedQueryLog.prefix_of_seed_replies
    (seed : Seed) (emittedAt : Nat → List (Message Player (WitnessedPacket graph)))
    {first second : List (LocalSeedEntry graph (app).Command)}
    (left : CountedQueryLog first) (right : CountedQueryLog second)
    (leftReplies : ∀ entry ∈ first, controller.reply seed entry.query = entry.reply)
    (rightReplies : ∀ entry ∈ second, controller.reply seed entry.query = entry.reply)
    (leftEmitted : ∀ entry ∈ first,
      entry.query.input.emitted = emittedAt entry.query.activationIndex)
    (rightEmitted : ∀ entry ∈ second,
      entry.query.input.emitted = emittedAt entry.query.activationIndex)
    (lengths : first.length ≤ second.length) : first <+: second := by
  have same : first = second.take first.length :=
    CountedQueryLog.eq_of_seed_replies controller seed emittedAt left (right.take first.length)
      leftReplies
      (fun entry member => rightReplies entry (List.mem_of_mem_take member))
      leftEmitted
      (fun entry member => rightEmitted entry (List.mem_of_mem_take member))
      (by simp only [List.length_take, Nat.min_eq_left lengths])
  refine ⟨second.drop first.length, ?_⟩
  calc
    _ = second.take first.length ++ second.drop first.length :=
      congrArg (fun segment => segment ++ second.drop first.length) same
    _ = second := List.take_append_drop first.length second

private theorem prefix_eq_of_first_resolution
    {before other : List (LocalSeedEntry graph (app).Command)}
    (query otherQuery : CurrentSeedQuery graph) (command otherCommand : (app).Command)
    (isPrefix : before ++ [LocalSeedEntry.mk query (.resolution command)] <+:
      other ++ [LocalSeedEntry.mk otherQuery (.resolution otherCommand)])
    (unresolved : ∀ entry ∈ other, entry.reply = .activation ∨ entry.reply = .exhausted) :
    before ++ [LocalSeedEntry.mk query (.resolution command)] =
      other ++ [LocalSeedEntry.mk otherQuery (.resolution otherCommand)] := by
  have longer : other.length <
      (before ++ [LocalSeedEntry.mk query (.resolution command)]).length := by
    by_contra notLonger
    have within :
        (before ++ [LocalSeedEntry.mk query (.resolution command)]).length ≤ other.length :=
      Nat.le_of_not_gt notLonger
    obtain ⟨rest, restEq⟩ := isPrefix
    have taken := congrArg
      (List.take (before ++ [LocalSeedEntry.mk query (.resolution command)]).length) restEq
    rw [List.take_append_of_le_length (Nat.le_refl _), List.take_length,
      List.take_append_of_le_length within] at taken
    have member :
        (LocalSeedEntry.mk query (.resolution command) : LocalSeedEntry graph (app).Command) ∈
        other.take (before ++ [LocalSeedEntry.mk query (.resolution command)]).length := by
      rw [← taken]
      exact List.mem_append_right _ (by simp)
    rcases unresolved _ (List.mem_of_mem_take member) with impossible | impossible <;>
      cases impossible
  obtain ⟨rest, restEq⟩ := isPrefix
  have lengths := congrArg List.length restEq
  simp only [List.length_append, List.length_singleton] at lengths longer
  have empty : rest = [] := by
    have zero : rest.length = 0 := by omega
    cases rest with
    | nil => rfl
    | cons head tail => simp only [List.length_cons] at zero; omega
  simpa only [empty, List.append_nil] using restEq

/-- Stopping at the first resolving reply removes any dependence of the local
query transcript on the number and placement of remainder commands. -/
theorem CountedQueryLog.eq_at_resolution
    (seed : Seed) (emittedAt : Nat → List (Message Player (WitnessedPacket graph)))
    {first second : List (LocalSeedEntry graph (app).Command)}
    (query otherQuery : CurrentSeedQuery graph) (command otherCommand : (app).Command)
    (left : CountedQueryLog (first ++ [LocalSeedEntry.mk query (.resolution command)]))
    (right : CountedQueryLog (second ++ [LocalSeedEntry.mk otherQuery (.resolution otherCommand)]))
    (leftReplies : ∀ entry ∈ first ++ [LocalSeedEntry.mk query (.resolution command)],
      controller.reply seed entry.query = entry.reply)
    (rightReplies : ∀ entry ∈ second ++ [LocalSeedEntry.mk otherQuery (.resolution otherCommand)],
      controller.reply seed entry.query = entry.reply)
    (leftEmitted : ∀ entry ∈ first ++ [LocalSeedEntry.mk query (.resolution command)],
      entry.query.input.emitted = emittedAt entry.query.activationIndex)
    (rightEmitted : ∀ entry ∈ second ++ [LocalSeedEntry.mk otherQuery (.resolution otherCommand)],
      entry.query.input.emitted = emittedAt entry.query.activationIndex)
    (leftUnresolved : ∀ entry ∈ first,
      entry.reply = .activation ∨ entry.reply = .exhausted)
    (rightUnresolved : ∀ entry ∈ second,
      entry.reply = .activation ∨ entry.reply = .exhausted) :
    first ++ [LocalSeedEntry.mk query (.resolution command)] =
      second ++ [LocalSeedEntry.mk otherQuery (.resolution otherCommand)] := by
  by_cases lengths : (first ++ [LocalSeedEntry.mk query (.resolution command)]).length ≤
      (second ++ [LocalSeedEntry.mk otherQuery (.resolution otherCommand)]).length
  · exact prefix_eq_of_first_resolution query otherQuery command otherCommand
      (CountedQueryLog.prefix_of_seed_replies controller seed emittedAt left right
        leftReplies rightReplies leftEmitted rightEmitted lengths) rightUnresolved
  · exact (prefix_eq_of_first_resolution otherQuery query otherCommand command
      (CountedQueryLog.prefix_of_seed_replies controller seed emittedAt right left
        rightReplies leftReplies rightEmitted leftEmitted (Nat.le_of_not_ge lengths))
          leftUnresolved).symm

end Vegas.EventGraphRuntime.LocalSeedController

end

noncomputable section

namespace Vegas.EventGraphRuntime.LocalSeedController

open Interaction GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}
  {A : Bool → Type} {owner : Player} {event : graph.EventId}
  (controller : LocalSeedController runtime leaks (A false) owner event)
  (remainder : SeedRemainderController runtime leaks (A true) owner event)
  (laws : (side : Bool) → PMF (A side)) (bounds : MessageBounds graph)
  (inputs : PMF graph.Inputs) (horizon : Nat)

local notation "app" => runtime.reactiveApplication leaks
local notation "family" => fun values : (side : Bool) → A side =>
  controller.fixedScheduler remainder (initialMemory (values false) (values true))
local notation "mixture" => ReactiveApplication.schedulerMixture app
  (independentProduct laws) family
local notation "menu" => bounds.onePacketMenu runtime leaks
local notation "model" => ReactiveApplication.ResponseMenu.information menu
  (inputs.map State.initial) horizon (ReactiveApplication.SchedulerImplementation.scheduler mixture)
local notation "players" profile =>
  ReactiveApplication.ResponseMenu.decodeProfile menu
    (inputs.map State.initial) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler mixture) profile
local notation "draws" => fun state : (app).ProtocolState => match state with
  | none => independentProduct laws
  | some current => ReactiveApplication.SchedulerImplementation.posterior mixture
    (ReactiveApplication.Execution.environmentRecall
      (ReactiveApplication.Control.execution current))

variable [Finite (GameTheory.Protocol.ExecutionProtocol.History
  (ReactiveApplication.ResponseMenu.protocol (bounds.onePacketMenu runtime leaks)
    (PMF.map (State.initial (graph := graph)) inputs) horizon
    (ReactiveApplication.SchedulerImplementation.scheduler
      (ReactiveApplication.schedulerMixture (runtime.reactiveApplication leaks)
        (independentProduct laws) (fun values => controller.fixedScheduler remainder
          (initialMemory (values false) (values true)))))))]

/-- At the same actual unsent owner information site, two supported original
seeded executions with the same local seed have the same first resolving
transcript, even with different hidden preparations, remainder seeds and
foreign policies. -/
theorem bayesBelief_first_binding_log_eq
    (ordered : graph.RevealRelaxedOrdered)
    (domainEq : controller.domain = runtime.CountedSeedDomain leaks bounds inputs owner)
    (owned : graph.actor? event = some owner)
    (profile : ∀ who, (model).BehavioralPolicy who)
    (site : (model).InformationSite owner)
    (positive : 0 < (model).informationMass profile owner site)
    (current : Bool → (app).Control)
    (acting : ∀ side, (current side).actor = some owner)
    (supported : ∀ side, some (current side) ∈
      (((model).bayesBelief profile owner site
        ((menu).decisionInformationAntichain (inputs.map State.initial) horizon
          (mixture).scheduler owner site) positive).map (β := (app).ProtocolState)
            (fun history => history.1.state)).support)
    (values : Bool → (side : Bool) → A side)
    (valueSupport : ∀ side, values side ∈
      ((mixture).posterior (current side).execution.environmentRecall).support)
    (sameSeed : values false false = values true false)
    (ready : ∀ side, (current side).execution.application.publicView.EventReady event)
    (unmissed : ∀ side,
      (current side).execution.application.publicView.missedBindingBy owner = false)
    (unsent : ∀ side, (runtime.ownerSeedInput leaks event
      ((current side).execution.recall owner)
      ((current side).execution.observe app owner)).emitted = [])
    (payload : Bool → L.Ty)
    (result : ∀ side, PublicationResult (L.Val (payload side)))
    (choose : List Nat → Option Nat)
    (binding : bindingOwnedBy graph owner event = true)
    (bounded : ∀ side value, result side = .success value →
      (⟨payload side, value⟩ : Raw L) ∈ bounds.values)
    (admissible : ∀ side clocks slot, choose clocks = some slot →
      slot < bounds.candidateCount ∧
        slot ∉ runtime.submittedCandidateSlots leaks ((current side).execution.recall owner))
    (future : Bool → Player → (app).Policy)
    (focal : ∀ side, future side owner = fun past view => PMF.pure
      (runtime.guardedBindingServiceResponse leaks bounds owner event
        (payload side) (result side) choose past view))
    (coveredFuture : ∀ side who past view action,
      action ∈ (future side who past view).support → action ∈ (menu).actions who past view)
    (next : Bool → (app).Execution)
    (reached : ∀ side, next side ∈ ((app).runRounds (family (values side)) (future side)
      (current side).remaining ((current side).execution.respond app owner
        (runtime.bindingServiceResponse leaks owner event (payload side) (result side) choose
          ((current side).execution.recall owner)
          ((current side).execution.observe app owner)))).support)
    (completed : ∀ side, event ∈ (next side).application.config.cut.completed) :
    ∃ log : List (LocalSeedEntry graph (app).Command), CountedQueryLog log ∧
      ∀ side, ∃ (used : Nat) (before final : (app).Execution)
        (query : CurrentSeedQuery graph) (command : (app).Command),
        used < (current side).remaining ∧
        before ∈ ((app).runRounds (family (values side)) (future side) used
          ((current side).execution.respond app owner
            (runtime.bindingServiceResponse leaks owner event (payload side) (result side) choose
              ((current side).execution.recall owner)
              ((current side).execution.observe app owner)))).support ∧
        event ∉ before.application.config.cut.completed ∧
        event ∈ final.application.config.cut.completed ∧
        final ∈ ((app).dispatch (future side)
          (controller.step remainder
            (controller.replay remainder (initialMemory (values side false) (values side true))
              before.environmentRecall) before.environmentRecall
            (before.observeEnvironment app)).1 before).support ∧
        (controller.replay remainder (initialMemory (values side false) (values side true))
          final.environmentRecall).log = log ∧
        log = (controller.replay remainder
          (initialMemory (values side false) (values side true)) before.environmentRecall).log ++
            [⟨query, .resolution command⟩] ∧
        next side ∈ ((app).runRounds (family (values side)) (future side)
          ((current side).remaining - used - 1) final).support := by
  classical
  have genuine : ∀ side,
      (app).observe owner (some (current side)) = site.1 ∧
      (current side).execution.SerialRecall app := by
    intro side
    obtain ⟨history, _, stateEq⟩ := (PMF.mem_support_map_iff _ _ _).mp (supported side)
    have observed := (menu).info (inputs.map State.initial) horizon
      (mixture).scheduler owner history.1.trace
    have infoEq : (app).observe owner history.1.state = site.1 :=
      observed.symm.trans history.2
    have trace := stateEq ▸ history.1.trace
    refine ⟨?_, ?_⟩
    · exact stateEq ▸ infoEq
    · exact (runtime.countRecall_history leaks
        ((menu).toRawTrace (inputs.map State.initial) horizon (mixture).scheduler trace)).2.1
  have inputEq :
      ((current false).execution.recall owner, (current false).execution.observe app owner) =
      ((current true).execution.recall owner, (current true).execution.observe app owner) := by
    have same := (genuine false).1.trans (genuine true).1.symm
    simpa only [ReactiveApplication.observe, acting, ite_eq_left, Option.some.injEq] using same
  have recallEq : (current false).execution.recall owner =
      (current true).execution.recall owner := congrArg Prod.fst inputEq
  have serialEq : (current false).execution.network.nextSerial owner =
      (current true).execution.network.nextSerial owner := by
    rw [(genuine false).2 owner, (genuine true).2 owner, recallEq]
  obtain ⟨leftUsed, leftBefore, leftFinal, leftQuery, leftCommand,
      leftWithin, leftReached, leftIncomplete, leftComplete, leftMoved, leftCounted,
      leftUnresolved, leftWords, leftLog, leftSuffix⟩ :=
    controller.bayesBelief_first_binding_resolution remainder laws bounds inputs horizon
      ordered domainEq owned profile site positive (current false) (acting false)
        (supported false) (values false) (valueSupport false) (ready false) (unmissed false)
          (unsent false) (payload false) (result false) choose
            binding (bounded false) (admissible false) (future false) (focal false)
              (coveredFuture false)
              (next false) (reached false) (completed false)
  obtain ⟨rightUsed, rightBefore, rightFinal, rightQuery, rightCommand,
      rightWithin, rightReached, rightIncomplete, rightComplete, rightMoved, rightCounted,
      rightUnresolved, rightWords, rightLog, rightSuffix⟩ :=
    controller.bayesBelief_first_binding_resolution remainder laws bounds inputs horizon
      ordered domainEq owned profile site positive (current true) (acting true)
        (supported true) (values true) (valueSupport true) (ready true) (unmissed true)
          (unsent true) (payload true) (result true) choose
            binding (bounded true) (admissible true) (future true) (focal true) (coveredFuture true)
              (next true) (reached true) (completed true)
  have sameLog := CountedQueryLog.eq_at_resolution controller (values false false)
    (bindingEmissionWord (controller.calendar (values false false)) choose
      (runtime.readyActivationCount leaks event ((current false).execution.recall owner))
      owner event ((current false).execution.network.nextSerial owner))
    leftQuery rightQuery leftCommand rightCommand leftCounted rightCounted
    (fun entry member => (leftWords entry member).1)
    (fun entry member => by rw [sameSeed]; exact (rightWords entry member).1)
    (fun entry member => (leftWords entry member).2)
    (fun entry member => by
      rw [sameSeed, recallEq, serialEq]
      exact (rightWords entry member).2) leftUnresolved rightUnresolved
  refine ⟨_, leftCounted, ?_⟩
  intro side
  cases side with
  | false =>
      exact ⟨leftUsed, leftBefore, leftFinal, leftQuery, leftCommand, leftWithin, leftReached,
        leftIncomplete, leftComplete, leftMoved, leftLog, rfl, leftSuffix⟩
  | true =>
      exact ⟨rightUsed, rightBefore, rightFinal, rightQuery, rightCommand, rightWithin,
        rightReached, rightIncomplete, rightComplete, rightMoved,
        rightLog.trans sameLog.symm, sameLog, rightSuffix⟩

end Vegas.EventGraphRuntime.LocalSeedController

end
