/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.EventApplication

/-! # Swapping hidden values in event-graph configurations

A *value swap* (`Vegas.EventGraph.ValueSwap`) is an involution on the stored
value of every field and on the original action of every event, which fixes
every public field and every action at a resolution, and sends a failed binding
to a failed binding. Applied pointwise to the inputs, the outputs and the
chronological history of a configuration (`Vegas.EventGraph.Config.swap`), it
keeps the cut, the completion order and the public observation
(`Vegas.EventGraph.publicObserve_swap`), and each player's observation becomes
the swap of that observation on the fields visible to the player
(`Vegas.EventGraph.playerObserve_swap`).

Completing an event commutes with the swap. A graph step whose evaluator reads
only fields the swap fixes, such as a sample or a resolution of a binding the
swap fixes, commutes with it as well (`Vegas.EventGraph.Config.swap_mem_step`).
-/

noncomputable section

namespace Vegas.EventGraph

variable {Player : Type} {L : IExpr} [R : IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}

variable (graph) in
/-- **A value swap.** An involution on the value of every field and on the
action of every event. Public fields and resolution actions are fixed, and a
failed binding stays failed. At a binding event, the action and the stored
result are swapped alike. -/
structure ValueSwap where
  /-- The swap of a field's stored value. -/
  value : (field : graph.Field) → (graph.layout field).Value → (graph.layout field).Value
  /-- The swap of an event's original action. -/
  action : (event : graph.EventId) → graph.Action event → graph.Action event
  value_involutive : ∀ field, Function.Involutive (value field)
  action_involutive : ∀ event, Function.Involutive (action event)
  value_public : ∀ field, graph.fieldPublic field → value field = id
  action_publication : ∀ event payload, graph.outputLayout event = .publication payload →
    action event = id
  output_failure : ∀ event owner payload (outputEq : graph.outputLayout event =
      .binding owner payload),
    value (.inr event) (cast (congrArg EventField.Value outputEq.symm) .failure) =
      cast (congrArg EventField.Value outputEq.symm) .failure
  action_binding : ∀ event owner payload (outputEq : graph.outputLayout event =
      .binding owner payload) (result : PublicationResult (L.Val payload)),
    action event (cast (congrArg EventField.Action outputEq.symm) result) =
      cast (congrArg EventField.Action outputEq.symm)
        (cast (congrArg EventField.Value outputEq)
          (value (.inr event) (cast (congrArg EventField.Value outputEq.symm) result)))

namespace ValueSwap

variable (swap : graph.ValueSwap)

/-- The swap of a partial store, field by field. -/
def store (store : Store graph.layout) : Store graph.layout :=
  fun field => (store field).map (swap.value field)

theorem store_involutive : Function.Involutive swap.store := by
  intro store
  funext field
  simp only [ValueSwap.store, Option.map_map]
  cases store field with
  | none => rfl
  | some value => exact congrArg some (swap.value_involutive field value)

/-- The swap of one completion record. -/
def completion (completion : graph.Completion) : graph.Completion :=
  ⟨completion.event, swap.action completion.event completion.action⟩

@[simp] theorem completion_event (completion : graph.Completion) :
    (swap.completion completion).event = completion.event := rfl

theorem completion_involutive : Function.Involutive swap.completion := by
  rintro ⟨event, action⟩
  simp only [ValueSwap.completion, swap.action_involutive event action]

/-- A swapped store agrees with the original on every public field. -/
theorem store_public (values : Store graph.layout) (field : graph.Field)
    (isPublic : graph.fieldPublic field) : swap.store values field = values field := by
  simp only [ValueSwap.store, swap.value_public field isPublic, Option.map_id, id_eq]

end ValueSwap

namespace Config

/-- Configurations with the same inputs, cut, outputs and history are equal. -/
theorem ext_fields {left right : graph.Config} (inputs : left.inputs = right.inputs)
    (cut : left.cut = right.cut) (outputs : left.outputs = right.outputs)
    (history : left.history = right.history) : left = right := by
  rcases left with ⟨_, _, _, _, _, _, _⟩
  rcases right with ⟨_, _, _, _, _, _, _⟩
  cases inputs
  cases cut
  cases outputs
  cases history
  rfl

/-- **The swap of a configuration**: of its inputs, its outputs and the actions
of its history. -/
def swap (swap : graph.ValueSwap) (config : graph.Config) : graph.Config where
  inputs input := swap.value (.inl input) (config.inputs input)
  cut := config.cut
  outputs event := (config.outputs event).map (swap.value (.inr event))
  output_available event := by
    rw [Option.isSome_map]
    exact config.output_available event
  history := config.history.map swap.completion
  history_nodup := by
    rw [List.map_map]
    exact config.history_nodup
  history_exact event := by
    rw [List.map_map]
    exact config.history_exact event

variable (swap : graph.ValueSwap)

@[simp] theorem swap_cut (config : graph.Config) : (config.swap swap).cut = config.cut := rfl

@[simp] theorem swap_history (config : graph.Config) :
    (config.swap swap).history = config.history.map swap.completion := rfl

theorem swap_history_events (config : graph.Config) :
    (config.swap swap).history.map Completion.event = config.history.map Completion.event := by
  rw [swap_history, List.map_map]
  rfl

@[simp] theorem swap_store (config : graph.Config) :
    (config.swap swap).store = swap.store config.store := by
  funext field
  cases field <;> rfl

theorem swap_involutive : Function.Involutive (Config.swap swap) := by
  intro config
  have inputs : (config.swap swap |>.swap swap).inputs = config.inputs := by
    funext input
    exact swap.value_involutive (.inl input) (config.inputs input)
  have outputs : (config.swap swap |>.swap swap).outputs = config.outputs := by
    funext event
    change ((config.outputs event).map (swap.value (.inr event))).map
      (swap.value (.inr event)) = _
    rw [Option.map_map]
    cases config.outputs event with
    | none => rfl
    | some value => exact congrArg some (swap.value_involutive (.inr event) value)
  have history : (config.swap swap |>.swap swap).history = config.history := by
    change (config.history.map swap.completion).map swap.completion = _
    rw [List.map_map]
    conv_rhs => rw [← List.map_id config.history]
    exact List.map_congr_left fun completion _ => swap.completion_involutive completion
  exact ext_fields inputs rfl outputs history

/-- **Completing an event commutes with the swap.** -/
theorem swap_complete (config : graph.Config) (event : graph.EventId)
    (ready : config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (config.complete event ready action value).swap swap =
      (config.swap swap).complete event ready (swap.action event action)
        (swap.value (.inr event) value) := by
  have outputs : ((config.complete event ready action value).swap swap).outputs =
      ((config.swap swap).complete event ready (swap.action event action)
        (swap.value (.inr event) value)).outputs := by
    funext query
    by_cases same : query = event
    · subst same
      change ((config.complete query ready action value).outputs query).map _ = _
      rw [complete_output_same, complete_output_same]
      rfl
    · change ((config.complete event ready action value).outputs query).map _ = _
      rw [complete_output_of_ne _ _ _ _ _ _ same, complete_output_of_ne _ _ _ _ _ _ same]
      rfl
  have history : ((config.complete event ready action value).swap swap).history =
      ((config.swap swap).complete event ready (swap.action event action)
        (swap.value (.inr event) value)).history := by
    simp [ValueSwap.completion]
  exact ext_fields rfl rfl outputs history

end Config

/-- **The public observation ignores the swap.** -/
theorem publicObserve_swap (swap : graph.ValueSwap) (config : graph.Config) :
    graph.publicObserve (config.swap swap) = graph.publicObserve config := by
  apply PublicObservation.ext graph
  · exact Config.swap_history_events swap config
  · funext field
    simp only [publicObserve, Config.swap_store, publicStore]
    split
    · exact swap.store_public config.store field (by assumption)
    · rfl


/-! ### Public reads -/

/-- Two stores agree on every public field. -/
def PublicAgree (left right : Store graph.layout) : Prop :=
  ∀ field, graph.fieldPublic field → left field = right field

theorem ValueSwap.store_publicAgree (swap : graph.ValueSwap) (values : Store graph.layout) :
    PublicAgree (swap.store values) values :=
  swap.store_public values

theorem fieldPublic_of_ref {kind : EventField Player L} (ref : FieldRef graph.layout kind)
    (isPublic : kind.IsPublic) : graph.fieldPublic ref.field := by
  unfold fieldPublic
  rw [ref.layout_eq]
  exact isPublic

theorem PublicRead.field_public {payload : L.Ty} (read : PublicRead (R := R) graph.layout payload) :
    graph.fieldPublic read.field := by
  cases read with
  | publicData ref => exact fieldPublic_of_ref ref trivial
  | publication ref => exact fieldPublic_of_ref ref trivial

theorem GuardOperand.field?_public {currentPayload payload : L.Ty}
    (operand : GuardOperand graph.layout currentPayload payload) {field : graph.Field}
    (found : operand.field? = some field) : graph.fieldPublic field := by
  cases operand with
  | proposed => cases found
  | publicData ref =>
      cases found
      exact fieldPublic_of_ref ref trivial
  | publication ref =>
      cases found
      exact fieldPublic_of_ref ref trivial

/-- Guards read only public fields. -/
theorem GuardCheck.allAccepted?_publicAgree {payload : L.Ty}
    (checks : List (GuardCheck graph.layout payload)) {left right : Store graph.layout}
    (agree : PublicAgree left right) (proposal : PublicationResult (L.Val payload)) :
    GuardCheck.allAccepted? checks left proposal =
      GuardCheck.allAccepted? checks right proposal := by
  induction checks with
  | nil => rfl
  | cons check rest ih =>
      have checkEq := check.eval?_congr_reads left right proposal
        (fun field found => agree field (check.subjectRead.field?_public found))
        (fun ref read field found => agree field ((check.reads ref read).field?_public found))
      simp only [GuardCheck.allAccepted?]
      rw [checkEq, ih]

/-- A resolution reads its binding and public fields only. -/
theorem EventCode.resolveOutput?_publicAgree {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload)) (disclose : Bool)
    {left right : Store graph.layout} (agree : PublicAgree left right)
    (bound : left binding.field = right binding.field) :
    EventCode.resolveOutput? binding checks disclose left =
      EventCode.resolveOutput? binding checks disclose right := by
  have bindingEq := binding.get?_congr left right bound
  unfold EventCode.resolveOutput?
  rw [bindingEq]
  cases binding.get? right with
  | none => rfl
  | some value =>
      simp only [Option.bind_eq_bind, Option.bind_some]
      rw [GuardCheck.allAccepted?_publicAgree checks agree]

/-- A public sample reads public fields only. -/
theorem PublicDist.eval?_publicAgree {payload : L.Ty}
    (law : PublicDist (R := R) graph.layout payload)
    {left right : Store graph.layout} (agree : PublicAgree left right) :
    law.eval? left = law.eval? right :=
  law.eval?_congr_reads left right fun ref _ =>
    PublicRead.get?_congr (law.reads ref) left right
      (agree _ (PublicRead.field_public (law.reads ref)))


/-! ### Steps -/

open EventGraphRuntime in
/-- The swap fixes the binding a resolution event reads; nothing is asked at
other events. -/
def ResolutionFixed (swap : graph.ValueSwap) (event : graph.EventId) : Prop :=
  match nodeView graph event with
  | .resolve _ _ binding _ _ _ => swap.value binding.field = id
  | .bind .. | .sample .. => True

/-- The code of a ready event can be evaluated in its configuration. -/
private theorem code_eval?_exists (config : graph.Config) {event : graph.EventId}
    (ready : config.cut.Ready event) {output : EventField Player L}
    (outputEq : graph.outputLayout event = output) {code : EventCode graph.layout output}
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) = code)
    (action : output.Action) : ∃ law, code.eval? action config.store = some law := by
  apply Option.isSome_iff_exists.mp
  apply code.eval?_isSome_of_reads action config.store
  intro field member
  apply config.read_available ready
  rw [← EventCode.readFields_cast outputEq (graph.nodes event), codeEq]
  exact member

/-- **A graph step commutes with the swap** at an event whose resolution reads
a binding the swap fixes. -/
theorem Config.step_swap (swap : graph.ValueSwap) (config : graph.Config)
    (event : graph.EventId) (ready : config.cut.Ready event) (action : graph.Action event)
    (fixed : ResolutionFixed swap event) :
    (config.swap swap).step event ready (swap.action event action) =
      (config.step event ready action).map (Config.swap swap) := by
  unfold ResolutionFixed at fixed
  cases view : EventGraphRuntime.nodeView graph event with
  | bind owner payload outputEq codeEq =>
      obtain ⟨result, rfl⟩ : ∃ result : PublicationResult (L.Val payload),
          action = cast (congrArg EventField.Action outputEq.symm) result :=
        ⟨cast (congrArg EventField.Action outputEq) action, by simp⟩
      set swapped : PublicationResult (L.Val payload) :=
        cast (congrArg EventField.Value outputEq)
          (swap.value (.inr event) (cast (congrArg EventField.Value outputEq.symm) result))
      have valueEq : swap.value (.inr event) (cast (congrArg EventField.Value outputEq.symm)
          result) = cast (congrArg EventField.Value outputEq.symm) swapped := by
        simp [swapped]
      rw [swap.action_binding event owner payload outputEq result,
        (config.swap swap).step_eq_map_of_code event ready outputEq (.bind owner payload) codeEq
          swapped (PMF.pure swapped) rfl,
        config.step_eq_map_of_code event ready outputEq (.bind owner payload) codeEq
          result (PMF.pure result) rfl, PMF.pure_map, PMF.pure_map, PMF.pure_map,
        Config.swap_complete, swap.action_binding event owner payload outputEq result, valueEq]
      simp only [cast_cast]
  | resolve owner payload binding checks outputEq codeEq =>
      rw [view] at fixed
      obtain ⟨disclose, rfl⟩ : ∃ disclose : Bool,
          action = cast (congrArg EventField.Action outputEq.symm) disclose :=
        ⟨cast (congrArg EventField.Action outputEq) action, by simp⟩
      obtain ⟨law, evaluates⟩ := code_eval?_exists config ready outputEq codeEq disclose
      obtain ⟨result, resolved, rfl⟩ := Option.map_eq_some_iff.mp evaluates
      have swappedResolved : EventCode.resolveOutput? binding checks disclose
          (config.swap swap).store = some result := by
        rw [Config.swap_store, EventCode.resolveOutput?_publicAgree binding checks disclose
          (swap.store_publicAgree config.store) (by simp [ValueSwap.store, fixed])]
        exact resolved
      have actionFixed := swap.action_publication event payload outputEq
      have valueFixed := swap.value_public (.inr event)
        (show (graph.outputLayout event).IsPublic by rw [outputEq]; trivial)
      rw [actionFixed, id_eq,
        (config.swap swap).step_eq_map_of_code event ready outputEq _ codeEq disclose
          (PMF.pure result) (by rw [EventCode.resolve_eval?, swappedResolved]; rfl),
        config.step_eq_map_of_code event ready outputEq _ codeEq disclose (PMF.pure result)
          evaluates, PMF.pure_map, PMF.pure_map, PMF.pure_map, Config.swap_complete,
        actionFixed, valueFixed, id_eq, id_eq]
  | sample payload law outputEq codeEq =>
      obtain ⟨marker, rfl⟩ : ∃ marker : PUnit,
          action = cast (congrArg EventField.Action outputEq.symm) marker :=
        ⟨cast (congrArg EventField.Action outputEq) action, by simp⟩
      have actionFixed : swap.action event (cast (congrArg EventField.Action outputEq.symm)
          marker) = cast (congrArg EventField.Action outputEq.symm) marker := by
        generalize swap.action event (cast (congrArg EventField.Action outputEq.symm) marker) =
          other
        obtain ⟨otherMarker, rfl⟩ : ∃ otherMarker : PUnit,
            other = cast (congrArg EventField.Action outputEq.symm) otherMarker :=
          ⟨cast (congrArg EventField.Action outputEq) other, by simp⟩
        rfl
      have valueFixed := swap.value_public (.inr event)
        (show (graph.outputLayout event).IsPublic by rw [outputEq]; trivial)
      obtain ⟨drawn, evaluates⟩ := code_eval?_exists config ready outputEq codeEq marker
      have swappedEvaluates : (EventCode.sample payload law).eval? marker
          (config.swap swap).store = some drawn := by
        rw [Config.swap_store]
        change law.eval? _ = _
        rw [PublicDist.eval?_publicAgree law (swap.store_publicAgree config.store)]
        exact evaluates
      rw [actionFixed,
        (config.swap swap).step_eq_map_of_code event ready outputEq _ codeEq marker drawn
          swappedEvaluates,
        config.step_eq_map_of_code event ready outputEq _ codeEq marker drawn evaluates,
        PMF.map_comp]
      congr 1
      funext value
      rw [Function.comp_apply, Config.swap_complete, actionFixed, valueFixed, id_eq]

/-! ### Player observations -/

variable [DecidableEq Player]

/-- The swap of a player observation: of its store and its own actions. -/
def PlayerObservation.swap {who : Player} (swap : graph.ValueSwap)
    (observation : graph.PlayerObservation who) : graph.PlayerObservation who where
  completionOrder := observation.completionOrder
  store := swap.store observation.store
  ownActions := observation.ownActions.map swap.completion

/-- **A player observes the swap of its observation.** -/
theorem playerObserve_swap (swap : graph.ValueSwap) (who : Player) (config : graph.Config) :
    graph.playerObserve who (config.swap swap) =
      (graph.playerObserve who config).swap swap := by
  apply PlayerObservation.ext graph
  · exact Config.swap_history_events swap config
  · funext field
    simp only [playerObserve, PlayerObservation.swap, Config.swap_store, playerStore,
      ValueSwap.store]
    split <;> rfl
  · simp only [playerObserve, PlayerObservation.swap, Config.swap_history, ownCompletions,
      List.filter_map]
    rfl

/-- A swap fixing every field visible to a player and its actions fixes its
observations. -/
theorem PlayerObservation.swap_eq_self {who : Player} (swap : graph.ValueSwap)
    (fixedValues : ∀ field, graph.fieldVisibleTo who field → swap.value field = id)
    (fixedActions : ∀ event, graph.actor? event = some who → swap.action event = id)
    (config : graph.Config) :
    (graph.playerObserve who config).swap swap = graph.playerObserve who config := by
  apply PlayerObservation.ext graph
  · rfl
  · funext field
    simp only [PlayerObservation.swap, playerObserve, ValueSwap.store, playerStore]
    split
    · rename_i visible
      rw [fixedValues field visible, Option.map_id, id_eq]
    · rfl
  · simp only [PlayerObservation.swap, playerObserve, ownCompletions]
    conv_rhs => rw [← List.map_id (List.filter _ config.history)]
    refine List.map_congr_left fun completion member => ?_
    have owned := of_decide_eq_true (List.mem_filter.mp member).2
    simp only [ValueSwap.completion, fixedActions completion.event owned, id_eq]

end Vegas.EventGraph

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} {L : IExpr}

/-- The swap of a candidate meaning by a map of its opened value. -/
def swapCandidate (swap : Raw L → Raw L) :
    CommitmentCandidate (Raw L) → CommitmentCandidate (Raw L)
  | .fresh => .fresh
  | .openable raw => .openable (swap raw)
  | .unopenable => .unopenable

@[simp] theorem swapCandidate_fresh (swap : Raw L → Raw L) :
    swapCandidate swap .fresh = .fresh := rfl

@[simp] theorem swapCandidate_unopenable (swap : Raw L → Raw L) :
    swapCandidate swap .unopenable = .unopenable := rfl

@[simp] theorem swapCandidate_openable (swap : Raw L → Raw L) (raw : Raw L) :
    swapCandidate swap (.openable raw) = .openable (swap raw) := rfl

theorem swapCandidate_eq_fresh_iff (swap : Raw L → Raw L)
    (candidate : CommitmentCandidate (Raw L)) :
    swapCandidate swap candidate = .fresh ↔ candidate = .fresh := by
  cases candidate <;> simp

theorem swapCandidate_involutive {swap : Raw L → Raw L} (involutive : Function.Involutive swap) :
    Function.Involutive (swapCandidate swap) := by
  intro candidate
  cases candidate <;> simp [involutive _]

variable [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- The typed result a candidate gives a binding with this payload. -/
def candidateResult (candidate : CommitmentCandidate (Raw L)) (payload : L.Ty) :
    PublicationResult (L.Val payload) :=
  match candidate with
  | .openable raw => (raw.as? payload).elim .failure .success
  | .fresh | .unopenable => .failure

theorem State.bindingResult_eq (state : State graph) (handle : Handle graph) (payload : L.Ty) :
    state.bindingResult handle payload =
      candidateResult (state.candidates.lookup handle) payload := by
  unfold State.bindingResult candidateResult
  cases state.candidates.lookup handle <;> rfl

variable (graph) in
/-- **A hidden swap**: a value swap with an involution on the value prepared at
each handle. -/
structure HiddenSwap where
  /-- The swap of stored values and actions. -/
  values : graph.ValueSwap
  /-- The swap of the value prepared at a handle. -/
  raw : Handle graph → Raw L → Raw L
  raw_involutive : ∀ handle, Function.Involutive (raw handle)

namespace HiddenSwap

variable (swap : HiddenSwap graph)

/-- The swap of a candidate catalogue, handle by handle. -/
def candidates (catalogue : CommitmentCandidates Player (CandidateSlot graph) (Raw L)) :
    CommitmentCandidates Player (CandidateSlot graph) (Raw L) :=
  ⟨fun owner slot => swapCandidate (swap.raw (owner, slot)) (catalogue.table owner slot)⟩

@[simp] theorem lookup_candidates
    (catalogue : CommitmentCandidates Player (CandidateSlot graph) (Raw L))
    (handle : Handle graph) :
    (swap.candidates catalogue).lookup handle =
      swapCandidate (swap.raw handle) (catalogue.lookup handle) := rfl

theorem candidates_involutive : Function.Involutive swap.candidates := by
  intro catalogue
  change CommitmentCandidates.mk _ = CommitmentCandidates.mk _
  congr 1
  funext owner slot
  exact swapCandidate_involutive (swap.raw_involutive (owner, slot)) _

theorem candidates_prepare [DecidableEq Player]
    (catalogue : CommitmentCandidates Player (CandidateSlot graph) (Raw L))
    (owner : Player) (slot : CandidateSlot graph) (raw : Raw L) :
    swap.candidates (catalogue.prepare owner slot raw) =
      (swap.candidates catalogue).prepare owner slot (swap.raw (owner, slot) raw) := by
  unfold CommitmentCandidates.prepare
  rw [lookup_candidates]
  cases fresh : catalogue.lookup (owner, slot) with
  | openable | unopenable => rfl
  | fresh =>
      change CommitmentCandidates.mk _ = CommitmentCandidates.mk _
      congr 1
      funext other otherSlot
      by_cases same : other = owner ∧ otherSlot = slot
      · obtain ⟨rfl, rfl⟩ := same
        simp
      · simp only [same, ↓reduceIte]
        rfl

theorem candidates_freeze [DecidableEq Player]
    (catalogue : CommitmentCandidates Player (CandidateSlot graph) (Raw L))
    (handle : Handle graph) :
    swap.candidates (catalogue.freeze handle) = (swap.candidates catalogue).freeze handle := by
  unfold CommitmentCandidates.freeze
  rw [lookup_candidates]
  cases fresh : catalogue.lookup handle with
  | openable | unopenable => rfl
  | fresh =>
      change CommitmentCandidates.mk _ = CommitmentCandidates.mk _
      congr 1
      funext owner slot
      by_cases same : (owner, slot) = handle
      · simp [same]
      · simp only [same, ↓reduceIte]
        rfl

theorem verify_candidates
    (catalogue : CommitmentCandidates Player (CandidateSlot graph) (Raw L))
    (handle : Handle graph) (raw : Raw L) :
    (swap.candidates catalogue).verify handle raw =
      catalogue.verify handle (swap.raw handle raw) := by
  rw [Bool.eq_iff_iff, CommitmentCandidates.verify_eq_true_iff,
    CommitmentCandidates.verify_eq_true_iff, lookup_candidates]
  constructor
  · intro opened
    have := congrArg (swapCandidate (swap.raw handle)) opened
    rwa [swapCandidate_involutive (swap.raw_involutive handle), swapCandidate_openable] at this
  · intro opened
    rw [opened, swapCandidate_openable, swap.raw_involutive handle]

end HiddenSwap

/-- **The swap of an application state**: of its configuration and its
candidate catalogue. -/
def State.swap (swap : HiddenSwap graph) (state : State graph) : State graph :=
  { state with
    config := state.config.swap swap.values
    candidates := swap.candidates state.candidates }

section StateSwap

variable (swap : HiddenSwap graph)

@[simp] theorem State.swap_config (state : State graph) :
    (state.swap swap).config = state.config.swap swap.values := rfl

@[simp] theorem State.swap_accepted (state : State graph) :
    (state.swap swap).accepted = state.accepted := rfl

@[simp] theorem State.swap_candidates (state : State graph) :
    (state.swap swap).candidates = swap.candidates state.candidates := rfl

@[simp] theorem State.swap_clock (state : State graph) :
    (state.swap swap).clock = state.clock := rfl

@[simp] theorem State.swap_activatedAt (state : State graph) :
    (state.swap swap).activatedAt = state.activatedAt := rfl

theorem State.swap_involutive : Function.Involutive (State.swap swap) := by
  rintro ⟨config, accepted, candidates, clock, activatedAt⟩
  simp only [State.swap, State.mk.injEq]
  exact ⟨Config.swap_involutive _ config, trivial, swap.candidates_involutive candidates, trivial,
    trivial⟩

@[simp] theorem State.swap_publicView (state : State graph) :
    (state.swap swap).publicView = state.publicView := by
  unfold State.publicView
  rw [State.swap_config, publicObserve_swap]
  rfl

theorem State.swap_withinDeadline (runtime : EventGraphRuntime graph) (state : State graph)
    (event : graph.EventId) :
    (state.swap swap).WithinDeadline runtime event ↔ state.WithinDeadline runtime event :=
  Iff.rfl

theorem State.swap_handleUnused (state : State graph) (handle : Handle graph) :
    (state.swap swap).HandleUnused handle ↔ state.HandleUnused handle := Iff.rfl

theorem State.swap_bindingResult (state : State graph) (handle : Handle graph)
    (payload : L.Ty) :
    (state.swap swap).bindingResult handle payload =
      candidateResult (swapCandidate (swap.raw handle) (state.candidates.lookup handle))
        payload := by
  rw [State.bindingResult_eq]
  rfl

/-- Completing an event commutes with the swap. -/
theorem State.swap_complete (state : State graph) (event : graph.EventId)
    (ready : state.config.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    (state.complete event ready action value).swap swap =
      (state.swap swap).complete event ready (swap.values.action event action)
        (swap.values.value (.inr event) value) := by
  unfold State.complete State.swap
  rw [Config.swap_complete]
  rfl

end StateSwap

/-- The swap of a player view: of its observation and its own candidates. -/
def PlayerView.swap [DecidableEq Player] (swap : HiddenSwap graph) (view : PlayerView graph) :
    PlayerView graph :=
  { view with
    observation := view.observation.swap swap.values
    candidates := fun slot => swapCandidate (swap.raw (view.who, slot)) (view.candidates slot) }

theorem State.swap_playerView [DecidableEq Player] (swap : HiddenSwap graph) (state : State graph)
    (who : Player) :
    (state.swap swap).playerView who = (state.playerView who).swap swap := by
  unfold State.playerView PlayerView.swap
  rw [State.swap_publicView, State.swap_config, playerObserve_swap]
  rfl

theorem PlayerView.swap_involutive [DecidableEq Player] (swap : HiddenSwap graph) :
    Function.Involutive (PlayerView.swap swap) := by
  intro view
  rcases view with ⟨who, publicView, observation, candidates⟩
  unfold PlayerView.swap
  simp only [PlayerView.mk.injEq, true_and]
  refine ⟨heq_of_eq ?_, ?_⟩
  · apply PlayerObservation.ext graph
    · rfl
    · exact swap.values.store_involutive observation.store
    · change (observation.ownActions.map swap.values.completion).map swap.values.completion = _
      rw [List.map_map]
      conv_rhs => rw [← List.map_id observation.ownActions]
      exact List.map_congr_left fun completion _ => swap.values.completion_involutive completion
  · funext slot
    exact swapCandidate_involutive (swap.raw_involutive (who, slot)) _

end Vegas.EventGraphRuntime
