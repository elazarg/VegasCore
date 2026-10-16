/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.EventSourceBindingChoice
import Vegas.Game.PhaseRecoveryBindingComponent
import Vegas.Game.PhaseBindingCounterpart

/-! # Actual auxiliary source support for every typed native binding result -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))

/-- Every typed result has a nonmissing auxiliary source choice at the exact
decoded binding input. Guard rejection does not remove its source action. -/
theorem exists_phaseRecoveryBindingChoice (wellFormed : setup.WellFormed)
    (execution : (phaseApplication runtime leaks).Execution) (who : Player)
    (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (view : SourceProgram.ProtocolView who setup.program)
    (decoded : phaseSourceView? setup mode runtime leaks who event
      (execution.observe (phaseApplication runtime leaks) who) = some view)
    (acting : (serviceGraph setup mode).actor? event = some who)
    (result : PublicationResult (L.Val payload)) :
    ∃ choice : setup.commitRecoveryModel.Choice who
        (setup.commitRecoveryClearInformation wellFormed who (some view)),
      phaseRecoveryBindingData setup mode event who payload binding choice.1 = (result, false) := by
  have decodedCore := decoded
  rw [phaseSourceView?_observed] at decodedCore
  obtain ⟨action, actionEq, offered⟩ := decodeEventView?_binding_choice setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program))
    (outputEmbedding setup.program).ref who event _ _ view decodedCore who payload binding result
  have actor := (phaseSourceView?_actor setup mode runtime leaks execution who event view
    decoded).trans acting
  have active : setup.commitRecoveryActive who
      (setup.commitRecoveryClearInformation wellFormed who (some view)).1.1 := by
    unfold Setup.commitRecoveryActive
    rw [setup.commitRecoveryClearInformation_current, setup.commitRecoveryClearInformation_excluded]
    exact ⟨actor, Finset.notMem_empty _⟩
  let move : CommitRecoveryMove Player L := ⟨action, false⟩
  have legal : some move ∈ setup.commitRecoveryModel.menu who
      (setup.commitRecoveryClearInformation wellFormed who (some view)) := by
    refine ⟨active, ?_⟩
    rw [setup.commitRecoveryClearInformation_current]
    exact ⟨offered, by simp only [move, Bool.false_eq_true, false_implies, ite_self]⟩
  let choice : setup.commitRecoveryModel.Choice who
      (setup.commitRecoveryClearInformation wellFormed who (some view)) := ⟨some move, legal⟩
  have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program event
    (cast (congrArg EventField.Action binding.symm) result) action actionEq
  refine ⟨choice, ?_⟩
  simp only [choice, move, phaseRecoveryBindingData, Option.elim_some, Bool.false_eq_true,
    ↓reduceIte, Option.bind_some, encoded, Option.map_some, Option.getD_some, cast_cast, cast_eq]

/-- Full mixing at the actual auxiliary decision gives positive original
typed-result mass for every result, including accepted unusable bindings. -/
theorem phaseRecoveryBindingChoice_supported_of_history [Finite Player]
    (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (mixed : assessment.IsFullyMixed)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (horizon : Nat) (scheduler : (phaseApplication runtime leaks).Scheduler) {control}
    (trace : ((phaseApplication runtime leaks).protocol
      (setup.initialLaw.map fun draw => PhaseRuntimeState.initial plan (encodeInputs draw))
      horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (clear : control.execution.application.current.excluded = ∅)
    (result : PublicationResult (L.Val payload)) :
    (result, false) ∈ ((assessment.strategy who
      (setup.commitRecoveryClearInformation wellFormed who
        (phaseSourceView? setup mode runtime leaks who event
          (control.execution.observe (phaseApplication runtime leaks) who)))).map
            (fun choice => phaseRecoveryBindingData setup mode event who payload binding
              choice.1)).support := by
  have played := phase_ready_binding_information setup mode runtime leaks plan maximal horizon
    scheduler trace who event payload binding request.2.2.1 clear wellFormed
  obtain ⟨source, _sourceTrace, _excluded, _generation, _actor, decoded⟩ :=
    phase_ready_binding_sourceView setup mode runtime leaks plan maximal horizon scheduler trace
      who event payload binding request.2.2.1 clear
  rw [decoded] at played ⊢
  obtain ⟨choice, same⟩ := exists_phaseRecoveryBindingChoice setup mode runtime leaks wellFormed
    control.execution who event payload binding _ decoded request.2.2.2.1 result
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨choice, mixed who ⟨_, played⟩ choice, same⟩

end Vegas
