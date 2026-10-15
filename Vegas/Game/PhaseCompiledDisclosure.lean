/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCompiledOpeningResponse
import Vegas.Compile.EventGraphDisclosureAction
import Vegas.Game.IntendedOpeningExtension

/-! # Compiled disclosing response kernels at successful actual publications -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)

local notation "copied" => EventGraph.toModeProfile (toEventGraph setup.program) mode
  (compileEventProfile setup.program (Setup.decodeBehavioralProfile setup
    (CommitmentInterface.values setup.program) (Setup.openingExtension setup source)))

omit [Fintype Player] in
/-- The source compiler supplies TRUE at every owned publication, including
rank-normalized observations and every dependency mode. -/
theorem compiled_opening_normalized_discloses
    (who : Player) (event : (serviceGraph setup mode).EventId)
    (actor : (serviceGraph setup mode).actor? event = some who)
    (observation : (serviceGraph setup mode).PlayerObservation who)
    (payload : L.Ty)
    (publication : (serviceGraph setup mode).outputLayout event = .publication payload)
    (action : (serviceGraph setup mode).Action event)
    (positive : action ∈ ((serviceGraph setup mode).normalizePolicy who (copied who)
      event actor observation).support) :
    cast (congrArg EventField.Action publication) action = true := by
  have law := compileEventPolicy_disclosing_publication_true setup.program who
    (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      (setup.openingExtension source) who)
    (setup.openingExtension_disclosing source who) event actor
    ((toEventGraph setup.program).fromModeObservation mode who
      ((serviceGraph setup mode).normalizeObservation event who observation)) payload publication
  change (((serviceGraph setup mode).normalizePolicy who (copied who) event actor
    observation).map (cast (congrArg EventField.Action publication))) = PMF.pure true at law
  have projected : cast (congrArg EventField.Action publication) action ∈
      (((serviceGraph setup mode).normalizePolicy who (copied who) event actor observation).map
        (cast (congrArg EventField.Action publication))).support :=
    (PMF.mem_support_map_iff _ _ _).mpr ⟨action, positive, rfl⟩
  rw [law] at projected
  exact (PMF.mem_support_pure_iff _ _).mp projected

/-- A successful actual publication makes the canonical phase response equal
to its complete compiled disclosing action kernel. Guard success is retained
explicitly, rather than inferred from successful binding storage. -/
theorem phaseSourcePolicy_compiled_opening_of_success
    (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
    (assessment : setup.commitRecoveryModel.BehavioralAssessment)
    (plan : RuntimePhasePlan (serviceGraph setup mode))
    (inputs : PMF (serviceGraph setup mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    {control : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : FieldRef (serviceGraph setup mode).layout (.binding who payload))
    (checks : List (GuardCheck (serviceGraph setup mode).layout payload))
    (outputEq : (serviceGraph setup mode).outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode (serviceGraph setup mode).layout) outputEq)
      ((serviceGraph setup mode).nodes event) = .resolve who payload binding checks)
    (node : nodeView (serviceGraph setup mode) event =
      .resolve who payload binding checks outputEq codeEq)
    (request : control.execution.application.SeedRequest who
      ⟨control.execution.application.attempt, event⟩)
    (unsent : ∀ message ∈ (phaseApplication runtime leaks).outputs
      (control.execution.recall who), PhaseCount.event? message.payload ≠
        some ⟨control.execution.application.attempt, event⟩)
    (value : L.Val payload)
    (stored : binding.get? control.execution.application.current.native.config.store =
      some (.success value))
    (values : (⟨payload, value⟩ : Raw L) ∈ bounds.values)
    (resolved : EventCode.resolveOutput? binding checks true
      control.execution.application.current.native.config.store = some (.success value))
    (observation : (serviceGraph setup mode).PlayerObservation who) :
    (phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment who
      (control.execution.recall who)
      (control.execution.observe (phaseApplication runtime leaks) who)).map
        (PhaseNativeProjection.action runtime leaks plan) =
      ((serviceGraph setup mode).normalizePolicy who (copied who) event request.2.2.2.1
        observation).map (fun action => runtime.reactiveDecision
          (PhaseNativeProjection.nativeLeaks leaks plan) who event action
          (control.execution.application.current.native.playerView who)) := by
  apply phaseSourcePolicy_opening_erasure_of_history setup mode runtime leaks bounds wellFormed
    assessment plan inputs horizon scheduler trace who event payload binding checks outputEq codeEq
      node request unsent value stored values resolved
  exact compiled_opening_normalized_discloses setup mode source who event request.2.2.2.1
    observation payload outputEq

end Vegas
