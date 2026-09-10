/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedProjection
import Vegas.Compile.ApplicationDeadlineIndependence

/-! # Deadline-independent execution through public activation tracking

Erasing public activation metadata commutes with native execution as long as
included messages do not invoke deadline-sensitive handlers. This compares
ordinary traffic in the actual two interpreters, without a clock-rate bound.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {P : Type} [DecidableEq P] {L : IExpr}

private theorem ordered_handle_no_active (image : ApplicationImage P L)
    (state : ApplicationImage.State P L) (message : Message P (ApplicationImage.Payload P L))
    (hactive : image.activeAddress? state.memory = none) :
    image.orderedApplication.handle state message = none := by
  change (if image.admitsMessage state.memory message then image.handle state message else none) =
    none
  rcases message with ⟨id, payload⟩
  cases payload <;>
    simp [ApplicationImage.admitsMessage, ApplicationImage.Payload.address?,
      ApplicationImage.admitsAddress, hactive]

/-- The full handler result, including rejection, agrees after attaching the
successor's activation metadata. -/
theorem handle_deadlineIndependent (runtime : WindowedApplication P L) (state : State P L)
    (message : Message P (ApplicationImage.Payload P L))
    (hstate : runtime.Consistent state) (hmessage : message.payload.DeadlineIndependent) :
    runtime.handle state message =
      (runtime.image.orderedApplication.handle state.base message).map
        (runtime.advanceTo state) := by
  cases hactive : state.active with
  | none =>
      have hnone : runtime.image.activeAddress? state.base.memory = none := by
        simpa only [hactive, Option.map_none] using hstate.1.symm
      rw [ordered_handle_no_active runtime.image state.base message hnone]
      simp [handle, hactive]
  | some activation =>
      have hcurrent : runtime.image.activeAddress? state.base.memory = some activation.key := by
        simpa only [hactive, Option.map_some] using hstate.1.symm
      simp only [handle, hactive, Option.bind_eq_bind, Option.bind_some, hcurrent, ↓reduceIte]
      rw [atOrigin, ApplicationImage.ordered_handle_withDeadlines_eq _ _ _ _ hmessage]
      cases runtime.image.orderedApplication.handle state.base message <;> rfl

private theorem erase_includePending (runtime : WindowedApplication P L)
    (state : runtime.application.State) (id : MessageId P)
    (hstate : runtime.Consistent state.application)
    (hsafe : state.pool.Satisfies (fun message => message.payload.DeadlineIndependent)) :
    runtime.eraseState (runtime.application.includePending state id) =
      runtime.image.orderedApplication.includePending (runtime.eraseState state) id := by
  cases hlookup : state.pool.lookup id with
  | none =>
      rw [runtime.application.includePending_missing state id hlookup,
        runtime.image.orderedApplication.includePending_missing (runtime.eraseState state) id
          hlookup]
  | some message =>
      have hmessage := hsafe.1 message (List.mem_of_find?_eq_some hlookup)
      have hhandler := runtime.handle_deadlineIndependent state.application message hstate hmessage
      cases hbase : runtime.image.orderedApplication.handle state.application.base message with
      | none =>
          have hconcrete : runtime.application.handle state.application message = none := by
            rw [hbase] at hhandler
            exact hhandler
          rw [runtime.application.includePending_reject state id message hlookup hconcrete,
            runtime.image.orderedApplication.includePending_reject (runtime.eraseState state)
              id message hlookup hbase]
          rfl
      | some base =>
          have hconcrete : runtime.application.handle state.application message =
              some (runtime.advanceTo state.application base) := by
            rw [hbase] at hhandler
            exact hhandler
          rw [runtime.application.includePending_accept state id message
              (runtime.advanceTo state.application base) hlookup hconcrete,
            runtime.image.orderedApplication.includePending_accept (runtime.eraseState state)
              id message base hlookup hbase]
          rfl

/-- Every native command projects exactly when retained messages are
deadline-independent. The command itself may be an arbitrary clock advance. -/
theorem step_erase (runtime : WindowedApplication P L)
    (state : runtime.application.State) (action : runtime.application.Action)
    (hstate : runtime.Consistent state.application)
    (hsafe : state.pool.Satisfies (fun message => message.payload.DeadlineIndependent)) :
    (runtime.application.step state action).map runtime.eraseState =
      runtime.image.orderedApplication.step
        (runtime.eraseState state) (runtime.eraseAction action) := by
  cases action with
  | privateCommand who command | submit who payload | replay who id | deliver who id =>
      simp only [MessageApplication.step, FinDist.map_pure]
      rfl
  | «include» id =>
      simp only [MessageApplication.step, eraseAction, FinDist.map_pure]
      rw [erase_includePending runtime state id hstate hsafe]
  | environment command =>
      cases command with
      | advance clock =>
          simp only [MessageApplication.step, eraseAction, application_advance,
            ApplicationImage.ordered_advance, FinDist.map_pure]
          rfl
      | sample address =>
          simp only [MessageApplication.step, eraseAction]
          change (((runtime.image.orderedApplication.environmentStep state.application.base
            (.sample address)).map (runtime.advanceTo state.application)).map
              (fun application => { state with application })).map runtime.eraseState = _
          simp only [FinDist.map_comp, Function.comp_def]
          rfl

end Vegas.WindowedApplication
