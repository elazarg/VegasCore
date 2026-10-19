/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalOrdinaryCoverage
import Vegas.Pending.PhaseProposalPreparedUsability

/-! # Actual repaired own-response records are ordinary-supported -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

local notation "app" => phaseApplication runtime leaks

/-- The repair's persistent physical record discharges the usable-response
condition for every literal remembered action, including canceled namespaces.
No old alias, receipt, or privately recalled preparation is discarded. -/
theorem phaseProposalRepaired_recorded_prepared
    (bounds : MessageBounds (serviceGraph setup mode))
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (app).Scheduler) (original : (app).Execution) (control : (app).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (owner : Player)
    (prepared : BindingShadow.PreparedBindings runtime leaks owner original control.execution)
    (network : original.network = control.execution.network)
    (entry : (app).PlayerEntry) (recorded : entry ∈ control.execution.recall owner) :
    phaseProposalResponsePrepared setup mode runtime leaks entry.action := by
  classical
  intro material event candidate transmitted callEq
  have declared : entry.action = ⟨some material⟩ :=
    congrArg (fun value => (⟨value⟩ : (app).Action)) transmitted
  let menu := PhaseCount.onePacketMenu runtime leaks bounds
  obtain ⟨before, prior, _prefix, _acting, viewed, offered, _recalled⟩ :=
    menu.recorded_response_prefix _ horizon scheduler control trace owner entry recorded
  rw [declared] at offered
  have permitted : PhaseCount.permits ((app).outputs (before.execution.recall owner))
      (PhaseCount.localEnvelope runtime leaks owner (before.execution.recall owner)
        (before.execution.observe app owner) material) = true := by
    rcases ((PhaseCount.mem_onePacketActions runtime leaks bounds owner _ _ _).mp offered).2 with
      impossible | ⟨other, same, valid⟩
    · cases impossible
    · cases Option.some.inj same
      exact valid
  have correct := ((PhaseCount.permits_eq_true_iff _ _).mp permitted).2.1
  have named : (PhaseCount.nativeMessage (PhaseCount.localEnvelope runtime leaks owner
      (before.execution.recall owner) (before.execution.observe app owner) material)).payload.call =
        material.call.packet := PhaseCount.maskPacket_call _ _
  unfold CountCallCorrect at correct
  rw [named, callEq] at correct
  obtain ⟨owned, _evidence, candidateOwner, ⟨serial, slot⟩, _unused⟩ := correct
  change candidate.1 = owner at candidateOwner
  have candidateEq : candidate = (owner, .prepared serial) := Prod.ext candidateOwner slot
  subst candidate
  cases node : nodeView (serviceGraph setup mode) event with
  | bind actor payload binding code =>
      simp only [bindingOwnedBy, binding, decide_eq_true_eq] at owned
      subst actor
      rcases material with ⟨⟨packet, opening⟩, evidence⟩
      dsimp only at callEq
      subst packet
      obtain ⟨value, usable⟩ := BindingShadow.PreparedBindings.recorded_preparation_usable
        runtime leaks bounds plan inputs horizon scheduler original control trace owner prepared
          network event payload binding code node serial opening evidence entry recorded declared
      simp only [PhaseProposal.bindingPreparation, binding, usable, Option.map_some, ne_eq,
        reduceCtorEq, not_false_eq_true]
  | resolve actor payload binding checks output code =>
      simp only [bindingOwnedBy, output, Bool.false_eq_true] at owned
  | sample payload law output code =>
      simp only [bindingOwnedBy, output, Bool.false_eq_true] at owned

end Vegas
