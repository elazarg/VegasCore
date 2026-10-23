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
(`Vegas.EventGraphRuntime.HiddenSwap.includePending_execution`), and every
other environment step commutes with it unconditionally.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open Interaction Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket graph)}

/-- The conditions under which including a call commutes with the swap: an
accepted commitment's handle is compatible with the swap at its event, and an
opening addresses a ready resolution only if the swap fixes the binding it reads
and every handle accepted for that binding. -/
def InclusionFixed (runtime : EventGraphRuntime graph) (swap : HiddenSwap graph)
    (state : State graph) (message : Message Player (Payload graph)) : Prop :=
  (∀ next event candidate, handle runtime state message = some next →
    message.payload = .commitment event candidate → BindCompatible swap event candidate) ∧
  ∀ event, (∃ candidate raw, message.payload = .opening event candidate raw) →
    state.config.cut.Ready event → RevealFixed swap state event

namespace HiddenSwap

variable (swap : HiddenSwap graph)

/-- The swap of a response: of its transmitted submission. -/
def action (response : (runtime.reactiveApplication leaks).Action) :
    (runtime.reactiveApplication leaks).Action :=
  ⟨response.transmission.map (WitnessedSubmission.swap swap)⟩

/-- The swap of a player's view of an execution: of its application view. -/
def view (observed : (runtime.reactiveApplication leaks).PlayerView) :
    (runtime.reactiveApplication leaks).PlayerView :=
  ⟨observed.messages, PlayerView.swap swap observed.application, observed.receipts⟩

/-- The swap of a recall entry: of its view and its action. -/
def entry (recalled : (runtime.reactiveApplication leaks).PlayerEntry) :
    (runtime.reactiveApplication leaks).PlayerEntry :=
  ⟨swap.view recalled.beforeView, swap.action recalled.action, recalled.emitted⟩

/-- **The swap of an execution**: of its application state and of every
player's recall. -/
def execution (current : (runtime.reactiveApplication leaks).Execution) :
    (runtime.reactiveApplication leaks).Execution :=
  ⟨current.application.swap swap, current.network, current.receipts,
    fun who => (current.recall who).map swap.entry, current.environmentRecall⟩

@[simp] theorem execution_application (current : (runtime.reactiveApplication leaks).Execution) :
    (swap.execution current).application = current.application.swap swap := rfl

@[simp] theorem execution_network (current : (runtime.reactiveApplication leaks).Execution) :
    (swap.execution current).network = current.network := rfl

@[simp] theorem execution_receipts (current : (runtime.reactiveApplication leaks).Execution) :
    (swap.execution current).receipts = current.receipts := rfl

@[simp] theorem execution_recall (current : (runtime.reactiveApplication leaks).Execution)
    (who : Player) : (swap.execution current).recall who = (current.recall who).map swap.entry :=
  rfl

@[simp] theorem execution_environmentRecall
    (current : (runtime.reactiveApplication leaks).Execution) :
    (swap.execution current).environmentRecall = current.environmentRecall := rfl

theorem action_involutive :
    Function.Involutive (swap.action (runtime := runtime) (leaks := leaks)) := by
  rintro ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      change (⟨some ((submission.swap swap).swap swap)⟩ :
        (runtime.reactiveApplication leaks).Action) = _
      rw [WitnessedSubmission.swap_involutive swap submission]

theorem view_involutive :
    Function.Involutive (swap.view (runtime := runtime) (leaks := leaks)) := by
  rintro ⟨messages, application, receipts⟩
  change (⟨messages, PlayerView.swap swap (PlayerView.swap swap application), receipts⟩ :
    (runtime.reactiveApplication leaks).PlayerView) = _
  rw [PlayerView.swap_involutive swap application]

theorem entry_involutive :
    Function.Involutive (swap.entry (runtime := runtime) (leaks := leaks)) := by
  rintro ⟨beforeView, response, emitted⟩
  change (⟨swap.view (swap.view beforeView), swap.action (swap.action response), emitted⟩ :
    (runtime.reactiveApplication leaks).PlayerEntry) = _
  rw [swap.view_involutive, swap.action_involutive]

theorem execution_involutive :
    Function.Involutive (swap.execution (runtime := runtime) (leaks := leaks)) := by
  rintro ⟨application, network, receipts, recall, environmentRecall⟩
  change (⟨(application.swap swap).swap swap, network, receipts,
    fun who => ((recall who).map swap.entry).map swap.entry, environmentRecall⟩ :
      (runtime.reactiveApplication leaks).Execution) = _
  rw [State.swap_involutive swap application]
  congr 1
  funext who
  rw [List.map_map]
  conv_rhs => rw [← List.map_id (recall who)]
  exact List.map_congr_left fun recalled _ => swap.entry_involutive recalled

/-- A player's view of the swapped execution is the swap of its view. -/
theorem observe_execution (current : (runtime.reactiveApplication leaks).Execution)
    (who : Player) :
    (swap.execution current).observe (runtime.reactiveApplication leaks) who =
      swap.view (current.observe (runtime.reactiveApplication leaks) who) := by
  change (⟨current.network.observe who, (current.application.swap swap).playerView who,
    current.receipts⟩ : (runtime.reactiveApplication leaks).PlayerView) = _
  rw [State.swap_playerView]
  rfl

/-- **The scheduler sees no swap.** -/
theorem observeEnvironment_execution (current : (runtime.reactiveApplication leaks).Execution) :
    (swap.execution current).observeEnvironment (runtime.reactiveApplication leaks) =
      current.observeEnvironment (runtime.reactiveApplication leaks) := by
  change (⟨current.network.publicView, (current.application.swap swap).publicView,
    current.receipts⟩ : (runtime.reactiveApplication leaks).EnvironmentView) = _
  rw [State.swap_publicView]
  rfl

/-- The evidence request of a response is fixed by the swap. -/
def RequestFixed (response : (runtime.reactiveApplication leaks).Action) : Prop :=
  ∀ submission, response.transmission = some submission →
    EvidenceRequest.FixedBy swap (WitnessedSubmission.evidence submission)

/-- **A response commutes with the swap** when its evidence request is fixed. -/
theorem respond_execution (current : (runtime.reactiveApplication leaks).Execution)
    (who : Player) (response : (runtime.reactiveApplication leaks).Action)
    (fixed : swap.RequestFixed response) :
    (swap.execution current).respond (runtime.reactiveApplication leaks) who
        (swap.action response) =
      swap.execution (current.respond (runtime.reactiveApplication leaks) who response) := by
  let app := runtime.reactiveApplication leaks
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      change (⟨current.application.swap swap, current.network, current.receipts,
          fun observer => if observer = who then (current.recall who).map swap.entry ++
            [⟨(swap.execution current).observe app who, ⟨none⟩, none⟩]
          else (current.recall observer).map swap.entry, current.environmentRecall⟩ :
            app.Execution) =
        swap.execution ⟨current.application, current.network, current.receipts,
          fun observer => if observer = who then current.recall who ++
            [⟨current.observe app who, ⟨none⟩, none⟩] else current.recall observer,
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
          fun observer => if observer = who then (current.recall who).map swap.entry ++
            [⟨(swap.execution current).observe app who, ⟨some (submission.swap swap)⟩,
              some (current.network.submit who ((submission.swap swap).emit
                (submitStep ((submission.swap swap).call.register
                  (current.application.swap swap) who) who (submission.swap swap).call.packet)
                  who (current.network.known who))).1⟩]
          else (current.recall observer).map swap.entry, current.environmentRecall⟩ :
            app.Execution) =
        swap.execution ⟨after, sent.2, current.receipts,
          fun observer => if observer = who then current.recall who ++
            [⟨current.observe app who, ⟨some submission⟩, some sent.1⟩]
          else current.recall observer,
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

/-- **Inclusion commutes with the swap** when the included call satisfies the
inclusion conditions. -/
theorem includePending_execution (current : (runtime.reactiveApplication leaks).Execution)
    (id : MessageId Player)
    (fixed : ∀ envelope, current.network.lookup id = some envelope →
      envelope.payload.tokenValid = true →
      InclusionFixed runtime swap current.application ⟨envelope.id, envelope.payload.call⟩) :
    (swap.execution current).includePending (runtime.reactiveApplication leaks) id =
      swap.execution (current.includePending (runtime.reactiveApplication leaks) id) := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  simp only [execution_network]
  cases found : current.network.lookup id with
  | none => rfl
  | some envelope =>
      have handled : (runtime.reactiveApplication leaks).handle
          (current.application.swap swap) envelope =
          ((runtime.reactiveApplication leaks).handle current.application envelope).map
            (State.swap swap) := by
        rw [reactiveApplication_handle, reactiveApplication_handle]
        split
        · rename_i valid
          obtain ⟨compatible, openingFixed⟩ := fixed envelope found valid
          exact handle_swap runtime swap current.application _ compatible openingFixed
        · rfl
      simp only [execution_application]
      rw [handled]
      cases (runtime.reactiveApplication leaks).handle current.application envelope <;> rfl

/-- **Environment steps commute with the swap** when every included call
satisfies the inclusion conditions. -/
theorem environmentStep_execution (current : (runtime.reactiveApplication leaks).Execution)
    (command : (runtime.reactiveApplication leaks).Command)
    (fixed : ∀ id envelope, command = .include id → current.network.lookup id = some envelope →
      envelope.payload.tokenValid = true →
      InclusionFixed runtime swap current.application ⟨envelope.id, envelope.payload.call⟩)
    (expiry : ∀ event entered, command = .application (.expire event) →
      current.application.config.cut.Ready event →
      current.application.activatedAt event = some entered →
      runtime.deadline event ≤ current.application.clock - entered →
        swap.values.ExpiryFixed event) :
    (swap.execution current).environmentStep (runtime.reactiveApplication leaks) command =
      (current.environmentStep (runtime.reactiveApplication leaks) command).map
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
      rw [swap.includePending_execution current id (fun envelope found =>
        fixed id envelope rfl found)]
      rfl
  | application command =>
      simp only [execution_application]
      change PMF.map _ (PMF.map _ (environmentStep runtime (current.application.swap swap)
        command)) = _
      rw [environmentStep_swap runtime swap current.application command
        (fun event entered same => expiry event entered (by rw [same])),
        PMF.map_comp, PMF.map_comp, PMF.map_comp]
      rfl

end HiddenSwap

end Vegas.EventGraphRuntime
