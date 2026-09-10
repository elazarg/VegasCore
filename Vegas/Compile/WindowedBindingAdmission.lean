/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import Vegas.Compile.WindowedBlockIsolation
import Vegas.Compile.ApplicationDeadlineIndependence
import Vegas.Compile.ApplicationImageBindings

/-! # Native admission of a canonical windowed binding

This isolates the ordinary binding service step.  A canonical owner envelope
accepted at the active binding address installs the binding state and makes
that address inactive.  Private preparation is deliberately not required:
the binding handler freezes an optional prepared value.
-/

noncomputable section

namespace Vegas.WindowedApplication

open EventGraph Interaction Interaction.MessageApplication

variable {P : Type} [DecidableEq P] {L : IExpr}

/-- Exact native handling and settlement of a canonical opaque binding. -/
theorem handle_canonical_binding_and_include_inactive
    (runtime : WindowedApplication P L) (state : State P L)
    (activation : Activation Nat) (code : BindingCode P L) (serial : Nat)
    (hactivation : state.active = some activation)
    (hactive : runtime.image.activeAddress? state.base.memory = some code.node)
    (hkey : activation.key = code.node)
    (hcode : runtime.image.lookup code.node = some (.bind code))
    (haccepted : state.base.memory.accepted code.sourceField = none)
    (hnotDone : state.base.memory.done code.node = false)
    (hrequires : code.requires.all state.base.memory.done = true)
    (pool : MessagePool P (ApplicationImage.Payload P L))
    (receipts : List (MessageId P × Bool))
    (hlookup : pool.lookup (code.owner, serial) = some
      ⟨(code.owner, serial), .binding code.node (code.owner, code.sourceSlot)⟩) :
    let message : Message P (ApplicationImage.Payload P L) :=
      ⟨(code.owner, serial), .binding code.node (code.owner, code.sourceSlot)⟩
    let nextBase := state.base.bind code (code.owner, code.sourceSlot)
    runtime.handle state message = some (runtime.advanceTo state nextBase) ∧
      runtime.image.activeAddress?
        (runtime.application.includePending ⟨state, pool, receipts⟩
          (code.owner, serial)).application.base.memory ≠ some code.node := by
  dsimp only
  let message : Message P (ApplicationImage.Payload P L) :=
    ⟨(code.owner, serial), .binding code.node (code.owner, code.sourceSlot)⟩
  have hindependent : message.payload.DeadlineIndependent := by
    simp [message, ApplicationImage.Payload.DeadlineIndependent]
  have hplain : runtime.image.handle state.base message =
      some (state.base.bind code (code.owner, code.sourceSlot)) := by
    rw [runtime.image.handle_binding state.base code.node code hcode
      (code.owner, serial) (code.owner, code.sourceSlot)]
    simp [haccepted, hnotDone, hrequires]
  have hordered : runtime.image.orderedApplication.handle state.base message =
      some (state.base.bind code (code.owner, code.sourceSlot)) := by
    rw [runtime.image.ordered_handle_eq state.base message code.node]
    · exact hplain
    · rfl
    · exact hactive
  have htimed : (runtime.atOrigin activation.since).orderedApplication.handle
      state.base message = some (state.base.bind code (code.owner, code.sourceSlot)) := by
    change (runtime.image.withDeadlines
      (fun address => activation.since + runtime.windowOf address)).orderedApplication.handle
        state.base message = _
    rw [runtime.image.ordered_handle_withDeadlines_eq _ state.base message hindependent]
    exact hordered
  have hhandle : runtime.handle state message =
      some (runtime.advanceTo state (state.base.bind code (code.owner, code.sourceSlot))) := by
    simp only [WindowedApplication.handle, hactivation, Option.bind_eq_bind,
      Option.bind_some, hkey, hactive, if_pos, htimed, Option.pure_def]
  refine ⟨hhandle, ?_⟩
  have hincluded := runtime.application.includePending_accept
    (⟨state, pool, receipts⟩ : runtime.application.State) (code.owner, serial)
    message (runtime.advanceTo state (state.base.bind code (code.owner, code.sourceSlot)))
    hlookup hhandle
  rw [hincluded]
  have hresolved := runtime.handle_resolves_active state
    (runtime.advanceTo state (state.base.bind code (code.owner, code.sourceSlot))) message hhandle
  obtain ⟨address, hbefore, _, hafter⟩ := hresolved
  have : address = code.node := Option.some.inj (hbefore.symm.trans hactive)
  simpa [this] using hafter

end Vegas.WindowedApplication

/-- info: 'Vegas.WindowedApplication.handle_canonical_binding_and_include_inactive'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.WindowedApplication.handle_canonical_binding_and_include_inactive
