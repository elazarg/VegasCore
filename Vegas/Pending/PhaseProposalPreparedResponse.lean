/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.PhaseProposalSubmittedBindings

/-! # Submitted typed preparations through unchanged responses -/

noncomputable section

namespace Vegas.EventGraphRuntime.BindingShadow

open Interaction EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))

local notation "app" => phaseApplication runtime leaks

/-- Other owners, silence and truthful openings cannot introduce another
owned binding record. Their actual raw syntax and evidence remain literal;
old physical results persist even if logical records have been masked. -/
theorem PreparedBindings.respond {owner : Player}
    {original repaired : (app).Execution}
    (prepared : PreparedBindings runtime leaks owner original repaired)
    (actor : Player) (left right : (app).Action)
    (nonbinding : actor ≠ owner ∨ ∀ material, left.transmission = some material →
      ∀ event candidate, material.call.packet ≠ .commitment event candidate) :
    PreparedBindings runtime leaks owner (original.respond app actor left)
      (repaired.respond app actor right) := by
  intro message member sender event candidate call payload outputEq codeEq node
  have old : message ∈ original.network.inputs := by
    rcases left with ⟨transmission⟩
    cases transmission with
    | none => exact member
    | some material =>
        simp only [ReactiveApplication.Execution.respond, MessageNetwork.submit,
          List.mem_append, List.mem_singleton] at member
        rcases member with retained | rfl
        · exact retained
        · rcases nonbinding with foreign | harmless
          · exact (foreign sender).elim
          · apply False.elim
            apply harmless material rfl event candidate
            exact (phase_emit_call (original.application.submit actor material) actor
              (original.network.known actor) material).symm.trans call
  exact (prepared message old sender event candidate call payload outputEq codeEq node).rebase
    ((phaseApplication_preservesFixedCandidates runtime leaks).respond original actor left)
    ((phaseApplication_preservesFixedCandidates runtime leaks).respond repaired actor right)

end Vegas.EventGraphRuntime.BindingShadow
