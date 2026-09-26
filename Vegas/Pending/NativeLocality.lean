/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.NativeRecall
import GameTheoryExtensions.Protocol.Coalescing

/-! # A native player's next input is locally computable

The update uses only own recall, the current native view, and the selected
action. The sender counter is reconstructed from recall. Its equality with
the runtime counter is the sole invariant required by this local simulation.
-/

noncomputable section

namespace Vegas.EventGraphRuntime

open GameTheory.Protocol GameTheory.Math.Probability Interaction

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

def NativeView.afterTransmission (view : NativeView graph) (nonce : Nat) :
    Option (Transmission graph) → NativeView graph
  | none => view
  | some (.replay id) =>
      match view.messages.known? id with
      | none => view
      | some message =>
          { view with messages := { view.messages with sent := view.messages.sent ++ [message] } }
  | some (.submit submission) =>
      { view with
        messages := { view.messages with
          sent := view.messages.sent ++ [⟨(view.who, nonce), submission.packet⟩] }
        candidates := submission.candidateAfter view.who view.candidates }

theorem nativeView_transmit (runtime : EventGraphRuntime graph) (who : Player)
    (state : runtime.application.State) (transmission : Option (Transmission graph)) :
    runtime.nativeView (runtime.transmit who state transmission) who =
      (runtime.nativeView state who).afterTransmission
        (state.pool.nextSerial who) transmission := by
  cases transmission with
  | none => rfl
  | some transmission =>
      cases transmission with
      | replay id =>
          simp only [transmit, MessagePool.replay]
          split <;> simp_all [nativeView, NativeView.ofApplication,
            MessageApplication.State.observe, NativeView.afterTransmission,
            MessagePool.observe, MessagePool.Result.invalid]
      | submit submission =>
          have candidates : (fun slot =>
              (submitStep (submission.register state.application who) who
                submission.packet).candidates.lookup (who, slot)) =
              submission.candidateAfter who
                (fun slot => state.application.candidates.lookup (who, slot)) := by
            funext slot
            exact submission.candidateAfter_eq who state.application slot
          have facts := submission.register_facts who state.application
          simp only [transmit, nativeView, NativeView.ofApplication,
            MessageApplication.State.observe, application, State.playerView,
            submitStep_config, submitStep_publicView, facts.1, facts.2.2,
            NativeView.afterTransmission, MessagePool.submit, MessagePool.observe,
            ↓reduceIte, candidates]

abbrev NativeInput (graph : Vegas.EventGraph Player L) :=
  List (NativeEntry graph) × NativeView graph

def nativeInput (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) : NativeInput graph :=
  (execution.principalHistory who, runtime.nativeView execution.native who)

def NativeInput.afterAction (input : NativeInput graph) (action : PlayerAction graph) :
    NativeInput graph :=
  (input.1 ++ [⟨input.2, action⟩],
    input.2.afterTransmission (authoredCount input.1) action.transmission)

theorem nativeInput_takeAction (runtime : EventGraphRuntime graph) (who : Player)
    (execution : NativeExecution runtime) (action : PlayerAction graph)
    (counters : execution.Counters runtime) :
    runtime.nativeInput who (runtime.takeAction who execution action) =
      (runtime.nativeInput who execution).afterAction action := by
  apply Prod.ext
  · exact runtime.takeAction_history_self who execution action
  · exact (runtime.nativeView_transmit who execution.native action.transmission).trans
      (by rw [counters who]; rfl)

/-- The invariant subtype changes no observation and exposes no proof to the
policy. Every legal native history supplies its required counter invariant. -/
def nativeLocalResponse (runtime : EventGraphRuntime graph) (who : Player) :
    LocalResponse {execution : NativeExecution runtime // execution.Counters runtime}
      (NativeInput graph) (PlayerAction graph) where
  observe execution := runtime.nativeInput who execution.1
  step execution action := ⟨runtime.takeAction who execution.1 action,
    runtime.takeAction_counters who execution.1 action execution.2⟩
  update := NativeInput.afterAction
  observe_step execution action :=
    runtime.nativeInput_takeAction who execution.1 action execution.2

end Vegas.EventGraphRuntime
