/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCompiledResponse
import Vegas.Pending.PhaseNativePolicyRun
import Vegas.Compile.EventGraphDisclosurePolicy

/-! # Original compiled-native laws for canonical phase executions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

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
/-- The globally disclosing source extension supplies the ready-event
commutation hypothesis in every existing dependency mode. -/
theorem compiled_openingExtension_readyIndependent :
    (serviceGraph setup mode).ReadyIndependent copied :=
  compileEventProfile_mode_disclosing_readyIndependent setup.program
    (setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
      (setup.openingExtension source)) (setup.openingExtension_disclosing source) mode

variable (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (assessment.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat) (phaseScheduler : (phaseApplication runtime leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)
  (values : ∀ event who payload,
    ((serviceGraph setup mode).outputLayout event = .binding who payload ∨
      (serviceGraph setup mode).outputLayout event = .publication payload) →
    ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

local notation "inputs" => setup.initialLaw.map encodeInputs
local notation "players" => phaseSourcePolicy setup mode runtime leaks bounds wellFormed assessment
local notation "prescribed" => fun who => runtime.prescribedReactivePolicy
  (PhaseNativeProjection.nativeLeaks leaks plan) who (copied who)

include copies continuing maximal capacity values phaseScheduler

/-- The concrete canonical dispatcher identifies the entire native policy law
at an actual clear actor callback. No local agreement is assumed. -/
private theorem compiled_policy_at_clear {current : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (phaseConsistent : ∀ who, (players who).Consistent (current.execution.recall who))
    (nativeConsistent : ∀ who, (prescribed who).Consistent
      ((PhaseNativeProjection.execution runtime leaks plan current.execution).recall who))
    (who : Player) (active : current.actor = some who) :
    prescribed who
        ((PhaseNativeProjection.execution runtime leaks plan current.execution).recall who)
        ((PhaseNativeProjection.execution runtime leaks plan current.execution).observe
          (runtime.reactiveApplication (PhaseNativeProjection.nativeLeaks leaks plan)) who) =
      PhaseNativeProjection.nativePolicy runtime leaks plan (players who)
        ((PhaseNativeProjection.execution runtime leaks plan current.execution).recall who)
        ((PhaseNativeProjection.execution runtime leaks plan current.execution).observe
          (runtime.reactiveApplication (PhaseNativeProjection.nativeLeaks leaks plan)) who) := by
  exact (phaseSourcePolicy_prescribed_of_clear_history setup mode runtime leaks source bounds
    wellFormed assessment copies continuing plan maximal horizon phaseScheduler capacity trace clear
      phaseConsistent nativeConsistent values who active).symm.trans
    (PhaseNativeProjection.nativePolicy_at_clear runtime leaks plan bounds inputs horizon
      phaseScheduler
      trace clear who (players who)).symm

/-- Every actual clear canonical history has consistent full prescribed-native
recalls. The native consistency condition is derived by the owning history
induction from the concrete dispatcher. -/
theorem phaseSourcePolicy_compiled_consistent {current : (phaseApplication runtime leaks).Control}
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (consistent : ∀ who, (players who).Consistent (current.execution.recall who)) :
    ∀ who, (prescribed who).Consistent
      ((PhaseNativeProjection.execution runtime leaks plan current.execution).recall who) := by
  apply PhaseNativeProjection.nativePolicies_consistent_of_local_agreement runtime leaks plan
    bounds inputs horizon phaseScheduler players prescribed ?_ trace clear consistent
  intro before prior earlierClear phaseFaithful nativeFaithful who active
  exact compiled_policy_at_clear setup mode runtime leaks source bounds wellFormed assessment
    copies continuing plan maximal horizon phaseScheduler capacity values prior earlierClear
      phaseFaithful nativeFaithful who active

/-- At every fuel, the actual original prescribed-native control law equals
that of the original canonical phase policies after projection. Physical
safety is the only execution-level premise. -/
theorem phaseSourcePolicy_compiled_controlLaw
    (safe : ∀ (current : (phaseApplication runtime leaks).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace (some current)),
    (∀ who, (players who).Consistent (current.execution.recall who)) →
      current.execution.application.current.excluded = ∅)
    (fuel : Nat) :
    (fun law => law.bind ((runtime.reactiveApplication
      (PhaseNativeProjection.nativeLeaks leaks plan)).controlStep ((inputs).map State.initial)
        horizon (PhaseNativeProjection.nativeScheduler runtime leaks plan phaseScheduler)
          prescribed))^[fuel] (PMF.pure none) =
    (fun law => law.bind ((runtime.reactiveApplication
      (PhaseNativeProjection.nativeLeaks leaks plan)).controlStep ((inputs).map State.initial)
        horizon (PhaseNativeProjection.nativeScheduler runtime leaks plan phaseScheduler)
          (fun who => PhaseNativeProjection.nativePolicy runtime leaks plan (players who))))^[fuel]
            (PMF.pure none) := by
  exact PhaseNativeProjection.native_controlLaw_eq_of_local_agreement runtime leaks plan bounds
    (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon phaseScheduler players
      prescribed (phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment)
        safe (fun before prior clear phaseFaithful nativeFaithful who active =>
          compiled_policy_at_clear setup mode runtime leaks source bounds wellFormed assessment
            copies continuing plan maximal horizon phaseScheduler capacity values prior clear
              phaseFaithful nativeFaithful who active) fuel

/-- The original canonical counted run and the original prescribed-native
behavioral run have both exact marginals at every fuel. The joint support
retains full projected controls and the physical public record. -/
theorem phaseSourcePolicy_exists_paired_compiled_run
    (safe : ∀ (current : (phaseApplication runtime leaks).Control)
    (_trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      ((inputs).map (PhaseRuntimeState.initial plan)) horizon phaseScheduler).Trace (some current)),
    (∀ who, (players who).Consistent (current.execution.recall who)) →
      current.execution.application.current.excluded = ∅)
    (fuel : Nat) :
    let menu := PhaseCount.onePacketMenu runtime leaks bounds
    let physicalInitial := (inputs).map (PhaseRuntimeState.initial plan)
    let nativeInitial := (inputs).map State.initial
    let imageScheduler := PhaseNativeProjection.nativeScheduler runtime leaks plan phaseScheduler
    let nativeApp := runtime.reactiveApplication (PhaseNativeProjection.nativeLeaks leaks plan)
    ∃ paired : PMF (nativeApp.ProtocolState × (phaseApplication runtime leaks).ProtocolState),
      paired.map Prod.fst = ((nativeApp.information nativeInitial horizon
        imageScheduler).runSingleMoverBehavioralFrom
          (nativeApp.singleMover nativeInitial horizon imageScheduler)
          (fun who => nativeApp.encodePolicy (prescribed who)) fuel
            (nativeApp.protocol nativeInitial horizon imageScheduler).initHistory).map
              History.state ∧
      paired.map Prod.snd = ((menu.information physicalInitial horizon
        phaseScheduler).runBehavioralFrom
        (fun who => menu.restrictPolicy physicalInitial horizon phaseScheduler who
          (players who)) fuel
          (menu.protocol physicalInitial horizon phaseScheduler).initHistory).map History.state ∧
      ∀ pair ∈ paired.support,
        pair.1 = PhaseNativeProjection.protocolState runtime leaks plan pair.2 ∧
        PhaseNativeProjection.PairedPublicRecord runtime leaks plan pair.1 pair.2 := by
  exact PhaseNativeProjection.exists_paired_behavioral_run_of_local_agreement runtime leaks plan
    bounds (serviceGraph_revealRelaxedOrdered setup mode) maximal inputs horizon phaseScheduler
      players prescribed
      (phaseSourcePolicy_covered setup mode runtime leaks bounds wellFormed assessment) safe
        (fun before prior clear phaseFaithful nativeFaithful who active =>
          compiled_policy_at_clear setup mode runtime leaks source bounds wellFormed assessment
            copies continuing plan maximal horizon phaseScheduler capacity values prior clear
              phaseFaithful nativeFaithful who active) fuel

end Vegas
