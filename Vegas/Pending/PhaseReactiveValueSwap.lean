/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseSwapApplication
import Vegas.Pending.ReactiveValueSwap

/-! # Full physical executions under a phased hidden-value swap -/

noncomputable section

namespace Vegas.EventGraphRuntime

open EventGraph Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L} {runtime : EventGraphRuntime graph}
  {leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph)}

namespace HiddenSwap

variable (swap : HiddenSwap graph)

/-- Only hidden preparation data changes; physical packet fields stay fixed. -/
def phaseAction (response : (phaseApplication runtime leaks).Action) :
    (phaseApplication runtime leaks).Action :=
  ⟨response.transmission.map (WitnessedSubmission.swap swap)⟩

/-- The native private projection changes while the entire phase public view is fixed. -/
def phaseView (observed : (phaseApplication runtime leaks).PlayerView) :
    (phaseApplication runtime leaks).PlayerView :=
  ⟨observed.messages, (PlayerView.swap swap observed.application.1, observed.application.2),
    observed.receipts⟩

def phaseEntry (entry : (phaseApplication runtime leaks).PlayerEntry) :
    (phaseApplication runtime leaks).PlayerEntry :=
  ⟨swap.phaseView entry.beforeView, swap.phaseAction entry.action, entry.emitted⟩

/-- Preserve the full physical network, receipts and scheduler recall, and map
all saved/live/archive values together with each original private response. -/
def phaseExecution (current : (phaseApplication runtime leaks).Execution) :
    (phaseApplication runtime leaks).Execution :=
  ⟨current.application.swap swap, current.network, current.receipts,
    fun who => (current.recall who).map swap.phaseEntry, current.environmentRecall⟩

@[simp] theorem phaseExecution_application (current : (phaseApplication runtime leaks).Execution) :
    (swap.phaseExecution current).application = current.application.swap swap := rfl

@[simp] theorem phaseExecution_network (current : (phaseApplication runtime leaks).Execution) :
    (swap.phaseExecution current).network = current.network := rfl

theorem phaseAction_involutive :
    Function.Involutive (swap.phaseAction (runtime := runtime) (leaks := leaks)) := by
  rintro ⟨transmission⟩
  cases transmission with
  | none => rfl
  | some submission =>
      change (⟨some ((submission.swap swap).swap swap)⟩ :
        (phaseApplication runtime leaks).Action) = _
      rw [WitnessedSubmission.swap_involutive swap submission]

theorem phaseView_involutive :
    Function.Involutive (swap.phaseView (runtime := runtime) (leaks := leaks)) := by
  rintro ⟨messages, ⟨native, phase⟩, receipts⟩
  change (⟨messages, (PlayerView.swap swap (PlayerView.swap swap native), phase), receipts⟩ :
    (phaseApplication runtime leaks).PlayerView) = _
  rw [PlayerView.swap_involutive swap native]

theorem phaseEntry_involutive :
    Function.Involutive (swap.phaseEntry (runtime := runtime) (leaks := leaks)) := by
  rintro ⟨view, action, emitted⟩
  change (⟨swap.phaseView (swap.phaseView view), swap.phaseAction (swap.phaseAction action),
    emitted⟩ : (phaseApplication runtime leaks).PlayerEntry) = _
  rw [swap.phaseView_involutive, swap.phaseAction_involutive]

theorem phaseExecution_involutive :
    Function.Involutive (swap.phaseExecution (runtime := runtime) (leaks := leaks)) := by
  rintro ⟨application, network, receipts, recall, environmentRecall⟩
  change (⟨(application.swap swap).swap swap, network, receipts,
    fun who => ((recall who).map swap.phaseEntry).map swap.phaseEntry, environmentRecall⟩ :
      (phaseApplication runtime leaks).Execution) = _
  rw [PhaseRuntimeState.swap_involutive swap application]
  congr 1
  funext who
  rw [List.map_map]
  exact List.map_id'' (fun entry => swap.phaseEntry_involutive entry) _

/-- Current own observations transform with the same saved physical frame. -/
theorem observe_phaseExecution (current : (phaseApplication runtime leaks).Execution)
    (who : Player) :
    (swap.phaseExecution current).observe (phaseApplication runtime leaks) who =
      swap.phaseView (current.observe (phaseApplication runtime leaks) who) := by
  change (⟨current.network.observe who, (current.application.swap swap).playerView who,
    current.receipts⟩ : (phaseApplication runtime leaks).PlayerView) = _
  change (⟨current.network.observe who,
    ((current.application.current.native.swap swap).playerView who,
      (current.application.swap swap).publicView), current.receipts⟩ :
      (phaseApplication runtime leaks).PlayerView) = _
  rw [State.swap_playerView, PhaseRuntimeState.swap_publicView]
  rfl

/-- Even archived public outcomes are identical to the scheduler. -/
theorem observeEnvironment_phaseExecution (current : (phaseApplication runtime leaks).Execution) :
    (swap.phaseExecution current).observeEnvironment (phaseApplication runtime leaks) =
      current.observeEnvironment (phaseApplication runtime leaks) := by
  change (⟨current.network.publicView, (current.application.swap swap).publicView,
    current.receipts⟩ : (phaseApplication runtime leaks).EnvironmentView) = _
  rw [PhaseRuntimeState.swap_publicView]
  rfl

/-- A complete actual response commutes with the phased swap when its requested
certificate value is fixed, retaining silence and every authentic emitted packet. -/
theorem respond_phaseExecution (current : (phaseApplication runtime leaks).Execution)
    (who : Player) (response : (phaseApplication runtime leaks).Action)
    (fixed : ∀ submission, response.transmission = some submission →
      submission.evidence.FixedBy swap) :
    (swap.phaseExecution current).respond (phaseApplication runtime leaks) who
      (swap.phaseAction response) =
      swap.phaseExecution (current.respond (phaseApplication runtime leaks) who response) := by
  let app := phaseApplication runtime leaks
  rcases response with ⟨transmission⟩
  cases transmission with
  | none =>
      change (⟨current.application.swap swap, current.network, current.receipts,
          fun observer => if observer = who then (current.recall who).map swap.phaseEntry ++
            [⟨(swap.phaseExecution current).observe app who, ⟨none⟩, none⟩]
          else (current.recall observer).map swap.phaseEntry, current.environmentRecall⟩ :
            app.Execution) =
        swap.phaseExecution ⟨current.application, current.network, current.receipts,
          fun observer => if observer = who then current.recall who ++
            [⟨current.observe app who, ⟨none⟩, none⟩] else current.recall observer,
          current.environmentRecall⟩
      rw [observe_phaseExecution]
      change ReactiveApplication.Execution.mk _ _ _ _ _ = ReactiveApplication.Execution.mk _ _ _ _ _
      congr 1
      funext observer
      by_cases same : observer = who
      · subst observer
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        rfl
      · simp only [same, ↓reduceIte]
  | some submission =>
      have submitted := PhaseRuntimeState.submit_swap swap current.application who submission
      have emitted := PhaseRuntimeState.emit_swap swap (current.application.submit who submission)
        who (current.network.known who) submission (fixed submission rfl)
      let after := current.application.submit who submission
      let sent := current.network.submit who (after.emit who (current.network.known who) submission)
      change (⟨(current.application.swap swap).submit who (submission.swap swap),
          (current.network.submit who (((current.application.swap swap).submit who
            (submission.swap swap)).emit who (current.network.known who)
              (submission.swap swap))).2,
          current.receipts,
          fun observer => if observer = who then (current.recall who).map swap.phaseEntry ++
            [⟨(swap.phaseExecution current).observe app who, ⟨some (submission.swap swap)⟩,
              some (current.network.submit who (((current.application.swap swap).submit who
                (submission.swap swap)).emit who (current.network.known who)
                  (submission.swap swap))).1⟩]
          else (current.recall observer).map swap.phaseEntry, current.environmentRecall⟩ :
            app.Execution) =
        swap.phaseExecution ⟨after, sent.2, current.receipts,
          fun observer => if observer = who then current.recall who ++
            [⟨current.observe app who, ⟨some submission⟩, some sent.1⟩]
          else current.recall observer,
          current.environmentRecall⟩
      rw [submitted, emitted, observe_phaseExecution]
      change ReactiveApplication.Execution.mk _ _ _ _ _ = ReactiveApplication.Execution.mk _ _ _ _ _
      congr 1
      funext observer
      by_cases same : observer = who
      · subst observer
        simp only [↓reduceIte, List.map_append, List.map_cons, List.map_nil]
        rfl
      · simp only [same, ↓reduceIte]

/-- Current inclusions replay under the native compatibility guard. Stale
namespaces require no binding or disclosure guard because both sides reject them. -/
theorem includePending_phaseExecution (current : (phaseApplication runtime leaks).Execution)
    (id : MessageId Player) (expiry : ∀ event, swap.values.ExpiryFixed event)
    (fixed : ∀ envelope, current.network.lookup id = some envelope →
      envelope.payload.tokenValid current.application.attempt = true →
      InclusionFixed runtime swap current.application.current.native
        ⟨envelope.id, envelope.payload.packet.call⟩) :
    (swap.phaseExecution current).includePending (phaseApplication runtime leaks) id =
      swap.phaseExecution (current.includePending (phaseApplication runtime leaks) id) := by
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  simp only [phaseExecution_network]
  cases found : current.network.lookup id with
  | none => rfl
  | some envelope =>
      have handled : (phaseApplication runtime leaks).handle
          (current.application.swap swap) envelope =
          ((phaseApplication runtime leaks).handle current.application envelope).map
            (PhaseRuntimeState.swap swap) :=
        PhaseRuntimeState.handle_swap runtime swap current.application envelope expiry
        (fun valid => (fixed envelope found valid).1)
        (fun valid => (fixed envelope found valid).2)
      simp only [phaseExecution_application]
      rw [handled]
      cases (phaseApplication runtime leaks).handle current.application envelope <;> rfl

/-- The actual physical environment law replays with identical scheduler
observation, packet network, receipts and full remembered command history. -/
theorem environmentStep_phaseExecution (current : (phaseApplication runtime leaks).Execution)
    (command : (phaseApplication runtime leaks).Command)
    (expiry : ∀ event, swap.values.ExpiryFixed event)
    (fixed : ∀ id envelope, command = .include id → current.network.lookup id = some envelope →
      envelope.payload.tokenValid current.application.attempt = true →
      InclusionFixed runtime swap current.application.current.native
        ⟨envelope.id, envelope.payload.packet.call⟩) :
    (swap.phaseExecution current).environmentStep (phaseApplication runtime leaks) command =
      (current.environmentStep (phaseApplication runtime leaks) command).map
        swap.phaseExecution := by
  unfold ReactiveApplication.Execution.environmentStep
  rw [observeEnvironment_phaseExecution, PMF.map_comp]
  cases command with
  | activate who =>
      simp only [phaseExecution_network, PMF.map_comp]
      rfl
  | wait => simp only [PMF.pure_map]; rfl
  | «include» id =>
      simp only [PMF.pure_map]
      rw [swap.includePending_phaseExecution current id expiry
        (fun envelope found => fixed id envelope rfl found)]
      rfl
  | application command =>
      change PMF.map _ (PMF.map _ ((current.application.swap swap).environment runtime command)) = _
      rw [PhaseRuntimeState.environment_swap runtime swap current.application command expiry,
        PMF.map_comp, PMF.map_comp, PMF.map_comp]
      rfl

end HiddenSwap
end Vegas.EventGraphRuntime
