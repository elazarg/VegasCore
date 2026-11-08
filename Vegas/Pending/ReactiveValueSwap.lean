/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.EventValueSwap
import Vegas.Pending.ReactiveRuntime

/-! # Swapping hidden values along reactive executions

A hidden swap (`Vegas.EventGraphRuntime.HiddenSwap`) acts on a reactive
execution of the event application: on its application state, and on every
recalled view and action, where a commitment's prepared value is swapped at its
handle (`Vegas.EventGraphRuntime.HiddenSwap.execution`). The network, the
receipts and the scheduler's recall are unchanged, and so is every view of the
scheduler (`Vegas.EventGraphRuntime.HiddenSwap.observeEnvironment_execution`).

A response commutes with the swap when its evidence request is fixed by the
swap (`Vegas.EventGraphRuntime.HiddenSwap.respond_execution`); an inclusion
commutes with it when the included call satisfies the conditions of
`Vegas.EventGraphRuntime.handle_swap`
(`Vegas.EventGraphRuntime.HiddenSwap.includePending_execution`). Automatic
service commutes with swaps that fix failed binding output; this condition is
discharged by concrete pair swaps. The environment law combines native command
conditions with this automatic-service condition.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  {timeouts : EventTimeouts graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

namespace State

/-- Swapping hidden values preserves the exact automatic-service predicate. -/
theorem automaticReady_swap (swap : HiddenSwap graph) (state : State graph)
    (event : graph.EventId) :
    (state.swap swap).AutomaticReady event ↔ state.AutomaticReady event := by
  simp only [AutomaticReady, swap_config, Config.swap_cut, Config.swap_defaulted]

/-- Automatic failure commutes with a swap that fixes failed binding output. -/
theorem completeFailure_swap (swap : HiddenSwap graph) (state : State graph)
    (event : graph.EventId) (ready : state.config.cut.Ready event)
    (fixed : swap.values.ExpiryFixed event) :
    (state.swap swap).completeFailure event ready =
      (state.completeFailure event ready).swap swap := by
  cases view : nodeView graph event with
  | bind owner payload outputEq codeEq =>
      simp only [completeFailure, view]
      rw [swap_complete, swap.values.action_binding event owner payload outputEq,
        fixed owner payload outputEq]
      rfl
  | resolve owner payload binding checks outputEq codeEq =>
      simp only [completeFailure, view]
      rw [swap_complete, swap.values.action_publication event payload outputEq,
        swap.values.value_public (.inr event)
          (show (graph.outputLayout event).IsPublic by rw [outputEq]; trivial)]
      rfl
  | sample payload law outputEq codeEq => simp only [completeFailure, view]

/-- Bounded automatic service commutes with a failure-fixing hidden swap. -/
theorem drainFuel_swap (swap : HiddenSwap graph)
    (fixed : ∀ event, swap.values.ExpiryFixed event) (fuel : Nat) (state : State graph) :
    drainFuel fuel (state.swap swap) = (drainFuel fuel state).swap swap := by
  classical
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      have readyEq : (state.swap swap).AutomaticReady = state.AutomaticReady :=
        funext fun event => propext (automaticReady_swap swap state event)
      simp only [drainFuel, completeAutomatic]
      simp only [readyEq]
      split
      · rename_i pending
        rw [completeFailure_swap swap state _ _ (fixed _)]
        exact ih _
      · rfl

/-- Native automatic service commutes with a failure-fixing hidden swap. -/
theorem drain_swap (swap : HiddenSwap graph)
    (fixed : ∀ event, swap.values.ExpiryFixed event) (state : State graph) :
    (state.swap swap).drain = state.drain.swap swap := by
  simp only [drain, swap_config, Config.remaining, Config.swap_cut]
  exact drainFuel_swap swap fixed _ state

end State

/-- The conditions under which including a call commutes with the swap: an
accepted commitment's handle is compatible with the swap at its event, and an
opening addresses a ready resolution only if the swap fixes the binding it reads
and every handle accepted for that binding. -/
def InclusionFixed (timeouts : EventTimeouts graph) (swap : HiddenSwap graph)
    (state : State graph) (message : Message Player (Payload graph)) : Prop :=
  (∀ next event candidate, handle timeouts state message = some next →
    message.payload = .commitment event candidate → BindCompatible swap event candidate) ∧
  ∀ event, (∃ candidate raw, message.payload = .opening event candidate raw) →
    state.config.cut.Ready event → RevealFixed swap state event

namespace HiddenSwap

variable (swap : HiddenSwap graph)

/-- The swap of a response: of its transmitted submission. -/
def action (response : ((reactiveApplication timeouts) leaks).Action) :
    ((reactiveApplication timeouts) leaks).Action :=
  ⟨response.transmission.map (WitnessedSubmission.swap swap)⟩

/-- The swap of a player's view of an execution: of its application view. -/
def view (observed : ((reactiveApplication timeouts) leaks).PlayerView) :
    ((reactiveApplication timeouts) leaks).PlayerView :=
  ⟨observed.messages, PlayerView.swap swap observed.application, observed.receipts⟩

/-- The swap of a recall entry: of its view and its action. -/
def entry (recalled : ((reactiveApplication timeouts) leaks).PlayerEntry) :
    ((reactiveApplication timeouts) leaks).PlayerEntry :=
  ⟨swap.view recalled.beforeView, swap.action recalled.action, recalled.emitted⟩

/-- **The swap of an execution**: of its application state and of every
player's recall. -/
def execution (current : ((reactiveApplication timeouts) leaks).Execution) :
    ((reactiveApplication timeouts) leaks).Execution :=
  ⟨current.application.swap swap, current.network, current.receipts,
    fun who => (current.logs who).map swap.entry, current.environmentRecall⟩

@[simp] theorem execution_application (current : ((reactiveApplication timeouts) leaks).Execution) :
    (swap.execution current).application = current.application.swap swap := rfl

@[simp] theorem execution_network (current : ((reactiveApplication timeouts) leaks).Execution) :
    (swap.execution current).network = current.network := rfl

@[simp] theorem execution_receipts (current : ((reactiveApplication timeouts) leaks).Execution) :
    (swap.execution current).receipts = current.receipts := rfl

@[simp] theorem execution_recall (current : ((reactiveApplication timeouts) leaks).Execution)
    (who : Player) : (swap.execution current).logs who = (current.logs who).map swap.entry :=
  rfl

@[simp] theorem execution_environmentRecall
    (current : ((reactiveApplication timeouts) leaks).Execution) :
    (swap.execution current).environmentRecall = current.environmentRecall := rfl

theorem action_involutive :
    Function.Involutive (swap.action (timeouts := timeouts) (leaks := leaks)) := by
  rintro ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      change (⟨some ((submission.swap swap).swap swap)⟩ :
        ((reactiveApplication timeouts) leaks).Action) = _
      rw [WitnessedSubmission.swap_involutive swap submission]

theorem view_involutive :
    Function.Involutive (swap.view (timeouts := timeouts) (leaks := leaks)) := by
  rintro ⟨messages, application, receipts⟩
  change (⟨messages, PlayerView.swap swap (PlayerView.swap swap application), receipts⟩ :
    ((reactiveApplication timeouts) leaks).PlayerView) = _
  rw [PlayerView.swap_involutive swap application]

theorem entry_involutive :
    Function.Involutive (swap.entry (timeouts := timeouts) (leaks := leaks)) := by
  rintro ⟨beforeView, response, emitted⟩
  change (⟨swap.view (swap.view beforeView), swap.action (swap.action response), emitted⟩ :
    ((reactiveApplication timeouts) leaks).PlayerEntry) = _
  rw [swap.view_involutive, swap.action_involutive]

theorem execution_involutive :
    Function.Involutive (swap.execution (timeouts := timeouts) (leaks := leaks)) := by
  rintro ⟨application, network, receipts, logs, environmentRecall⟩
  change (⟨(application.swap swap).swap swap, network, receipts,
    fun who => ((logs who).map swap.entry).map swap.entry, environmentRecall⟩ :
      ((reactiveApplication timeouts) leaks).Execution) = _
  rw [State.swap_involutive swap application]
  congr 1
  funext who
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (logs who)]
  exact List.map_congr_left fun recalled _ => swap.entry_involutive recalled

/-- A player's view of the swapped execution is the swap of its view. -/
theorem observe_execution (current : ((reactiveApplication timeouts) leaks).Execution)
    (who : Player) :
    (swap.execution current).observe ((reactiveApplication timeouts) leaks) who =
      swap.view (current.observe ((reactiveApplication timeouts) leaks) who) := by
  change (⟨current.network.observe who, (current.application.swap swap).playerView who,
    current.receipts⟩ : ((reactiveApplication timeouts) leaks).PlayerView) = _
  rw [State.swap_playerView]
  rfl

/-- **The scheduler sees no swap.** -/
theorem observeEnvironment_execution (current : ((reactiveApplication timeouts) leaks).Execution) :
    (swap.execution current).observeEnvironment ((reactiveApplication timeouts) leaks) =
      current.observeEnvironment ((reactiveApplication timeouts) leaks) := by
  change (⟨current.network.publicView, (current.application.swap swap).publicView,
    current.receipts⟩ : ((reactiveApplication timeouts) leaks).EnvironmentView) = _
  rw [State.swap_publicView]
  rfl

/-- The evidence request of a response is fixed by the swap. -/
def RequestFixed (response : ((reactiveApplication timeouts) leaks).Action) : Prop :=
  ∀ submission, response.transmission = some submission →
    EvidenceRequest.FixedBy swap (WitnessedSubmission.evidence submission)

/-- **A response commutes with the swap** when its evidence request is fixed. -/
theorem respond_execution (current : ((reactiveApplication timeouts) leaks).Execution)
    (who : Player) (response : ((reactiveApplication timeouts) leaks).Action)
    (fixed : swap.RequestFixed response) :
    (swap.execution current).respond ((reactiveApplication timeouts) leaks) who
        (swap.action response) =
      swap.execution (current.respond ((reactiveApplication timeouts) leaks) who response) := by
  let app := (reactiveApplication timeouts) leaks
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      change (⟨current.application.swap swap, current.network, current.receipts,
          fun observer => if observer = who then (current.logs who).map swap.entry ++
            [⟨(swap.execution current).observe app who, ⟨none⟩, none⟩]
          else (current.logs observer).map swap.entry, current.environmentRecall⟩ :
            app.Execution) =
        swap.execution ⟨current.application, current.network, current.receipts,
          fun observer => if observer = who then current.logs who ++
            [⟨current.observe app who, ⟨none⟩, none⟩] else current.logs observer,
          current.environmentRecall⟩
      rw [observe_execution]
      change ReactiveApplication.Execution.mk _ _ _ _ _ = ReactiveApplication.Execution.mk _ _ _ _ _
      congr 1
      funext observer
      by_cases same : observer = who
      · subst same
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        rfl
      · simp only [same, ↓reduceIte]
  | some submission =>
      have emitted := WitnessedSubmission.emit_swap swap submission
        (submitStep (submission.call.register current.application who) who
          submission.call.packet) who (current.network.known who) (fixed submission rfl)
      have submitted := WitnessedSubmission.submit_swap swap submission current.application who
      let after := submitStep (submission.call.register current.application who) who
        submission.call.packet
      let sent := current.network.submit who (submission.emit after who (current.network.known who))
      change (⟨submitStep ((submission.swap swap).call.register (current.application.swap swap) who)
            who (submission.swap swap).call.packet,
          (current.network.submit who ((submission.swap swap).emit
            (submitStep ((submission.swap swap).call.register (current.application.swap swap)
              who) who (submission.swap swap).call.packet) who (current.network.known who))).2,
          current.receipts,
          fun observer => if observer = who then (current.logs who).map swap.entry ++
            [⟨(swap.execution current).observe app who, ⟨some (submission.swap swap)⟩,
              some (current.network.submit who ((submission.swap swap).emit
                (submitStep ((submission.swap swap).call.register
                  (current.application.swap swap) who) who (submission.swap swap).call.packet)
                  who (current.network.known who))).1⟩]
          else (current.logs observer).map swap.entry, current.environmentRecall⟩ :
            app.Execution) =
        swap.execution ⟨after, sent.2, current.receipts,
          fun observer => if observer = who then current.logs who ++
            [⟨current.observe app who, ⟨some submission⟩, some sent.1⟩]
          else current.logs observer,
          current.environmentRecall⟩
      rw [submitted, emitted, observe_execution]
      change ReactiveApplication.Execution.mk _ _ _ _ _ = ReactiveApplication.Execution.mk _ _ _ _ _
      congr 1
      funext observer
      by_cases same : observer = who
      · subst same
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        rfl
      · simp only [same, ↓reduceIte]

/-- Inclusion commutes with a failure-fixing swap when the included call satisfies
its compatibility and resolution conditions. -/
theorem includePending_execution (current : ((reactiveApplication timeouts) leaks).Execution)
    (id : MessageId Player)
    (failures : ∀ event, swap.values.ExpiryFixed event)
    (fixed : ∀ envelope, current.network.lookup id = some envelope →
      envelope.payload.tokenValid = true →
      InclusionFixed timeouts swap current.application ⟨envelope.id, envelope.payload.call⟩) :
    (swap.execution current).includePending ((reactiveApplication timeouts) leaks) id =
      swap.execution (current.includePending ((reactiveApplication timeouts) leaks) id) := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  simp only [execution_network]
  cases found : current.network.lookup id with
  | none => rfl
  | some envelope =>
      have handled : ((reactiveApplication timeouts) leaks).handle
          (current.application.swap swap) envelope =
          (((reactiveApplication timeouts) leaks).handle current.application envelope).map
            (State.swap swap) := by
        rw [reactiveApplication_handle, reactiveApplication_handle]
        split
        · rename_i valid
          obtain ⟨compatible, openingFixed⟩ := fixed envelope found valid
          rw [handle_swap timeouts swap current.application _ compatible openingFixed]
          simp only [Option.map_map, Function.comp_def, State.drain_swap swap failures]
        · rfl
      simp only [execution_application]
      rw [handled]
      cases ((reactiveApplication timeouts) leaks).handle current.application envelope <;> rfl

/-- Environment steps commute with a failure-fixing swap when included calls
satisfy their compatibility and resolution conditions. -/
theorem environmentStep_execution (current : ((reactiveApplication timeouts) leaks).Execution)
    (command : ((reactiveApplication timeouts) leaks).Command)
    (fixed : ∀ id envelope, command = .include id → current.network.lookup id = some envelope →
      envelope.payload.tokenValid = true →
      InclusionFixed timeouts swap current.application ⟨envelope.id, envelope.payload.call⟩)
    (failures : ∀ event, swap.values.ExpiryFixed event) :
    (swap.execution current).environmentStep ((reactiveApplication timeouts) leaks) command =
      (current.environmentStep ((reactiveApplication timeouts) leaks) command).map
        swap.execution := by
  unfold ReactiveApplication.Execution.environmentStep
  rw [observeEnvironment_execution, PMF.map_comp]
  cases command with
  | activate who =>
      simp only [execution_network, PMF.map_comp]
      rfl
  | wait =>
      simp only [PMF.pure_map]
      rfl
  | «include» id =>
      simp only [PMF.pure_map]
      rw [swap.includePending_execution current id failures (fun envelope found =>
        fixed id envelope rfl found)]
      rfl
  | application command =>
      simp only [execution_application]
      change PMF.map _ (PMF.map _ (PMF.map State.drain
        (environmentStep timeouts (current.application.swap swap) command))) =
        PMF.map _ (PMF.map _ (PMF.map State.drain
          (environmentStep timeouts current.application command)))
      rw [environmentStep_swap timeouts swap current.application command
        (fun event _ _ _ _ _ => failures event)]
      simp only [PMF.map_comp, Function.comp_def, State.drain_swap swap failures]
      rfl

end HiddenSwap

end Vegas.EventGraphRuntime
