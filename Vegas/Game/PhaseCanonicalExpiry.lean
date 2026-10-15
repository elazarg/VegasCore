/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCanonicalOperations

/-! # Original physical service rules out canonical expiry exclusions -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (deadline : (serviceGraph setup mode).EventId → Nat)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (source : ∀ who, setup.intendedModel.BehavioralPolicy who)
  (bounds : MessageBounds (serviceGraph setup mode)) (wellFormed : setup.WellFormed)
  (assessment : setup.commitRecoveryModel.BehavioralAssessment)
  (copies : (setup.commitRecoveryRestriction wellFormed).ExtendsProfile source assessment.strategy)
  (continuing : ∀ who (site : setup.commitRecoveryModel.InformationSite who),
    ∀ choice ∈ (assessment.strategy who site.1).support,
      setup.CommitRecoveryContinues who site.1 choice.1)
  (plan : RuntimePhasePlan (serviceGraph setup mode))
  (ordered : (serviceGraph setup mode).RevealRelaxedOrdered)
  (maximal : plan.phases.IsChain fun before after =>
    before.kind ≠ after.kind ∨ before.kind = .sample)
  (horizon : Nat)
  (scheduler : (phaseApplication (serviceRuntime setup mode deadline) leaks).Scheduler)
  (capacity : horizon ≤ bounds.candidateCount)

local notation "R" => serviceRuntime setup mode deadline
local notation "P" => phaseApplication R leaks
local notation "I" => setup.initialLaw.map encodeInputs
local notation "start" =>
  PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs)

variable (delay bound : (serviceGraph setup mode).EventId → Nat)
  (opportunity : PhaseService.Opportunity (serviceRuntime setup mode deadline) leaks
    (PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs))
      horizon scheduler delay)
  (inclusion : PhaseService.ProtectedInclusion (serviceRuntime setup mode deadline) leaks
    (PMF.map (PhaseRuntimeState.initial plan) (setup.initialLaw.map encodeInputs))
      horizon scheduler bound)
  (timely : (serviceRuntime setup mode deadline).AsyncTimely delay bound)
  (values : ∀ event owner payload,
    ((serviceGraph setup mode).outputLayout event = .binding owner payload ∨
      (serviceGraph setup mode).outputLayout event = .publication payload) →
      ∀ value : L.Val payload, (⟨payload, value⟩ : Raw L) ∈ bounds.values)

include copies continuing ordered maximal capacity opportunity inclusion timely values

/-- Every supported native environment effect at a clear canonical idle prefix
retains empty permanent exclusion under the original physical service contract. -/
theorem phaseSourcePolicy_environmentResult_clear_of_history
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol start horizon scheduler).Trace
      (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (idle : current.actor = none)
    (consistent : ∀ owner, (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      owner).Consistent (current.execution.recall owner))
    (command : EnvironmentCommand (serviceGraph setup mode))
    (native : EventGraphRuntime.State (serviceGraph setup mode))
    (supported : native ∈ (environmentStep R current.execution.application.current.native
      command).support) :
    (current.execution.application.current.environmentResult command native).excluded = ∅ := by
  classical
  cases command with
  | advanceClock => exact clear
  | executeSample event => exact clear
  | expire event =>
      cases owned : (serviceGraph setup mode).actor? event with
      | none => simp only [RecoveryState.environmentResult, RecoveryState.excludeEvent, owned,
          ite_self]; exact clear
      | some owner =>
          have unchanged : native = current.execution.application.current.native := by
            by_cases ready : current.execution.application.current.native.config.cut.Ready event
            · obtain ⟨_draw, valid⟩ := phaseNativeInvariant_history R leaks plan I horizon scheduler
                ((PhaseCount.onePacketMenu R leaks bounds).toRawTrace start horizon scheduler trace)
              obtain ⟨entered, stamp⟩ := valid.active.activatedAt_eq_some_of_ready_actor event ready
                (by simp only [owned, Option.isSome_some])
              by_cases due : deadline event ≤
                  current.execution.application.current.native.clock - entered
              · cases node : nodeView (serviceGraph setup mode) event with
                | bind actor payload outputEq codeEq =>
                    have same := (nodeView_bind_actor outputEq codeEq).symm.trans owned
                    cases Option.some.inj same
                    have initialEq : setup.initialLaw.map (fun draw =>
                        PhaseRuntimeState.initial plan (encodeInputs draw)) = start := by
                      simp only [PMF.map_comp, Function.comp_def]
                    exact (phase_due_binding_impossible setup mode deadline leaks plan bounds
                      wellFormed assessment continuing ordered maximal horizon scheduler capacity
                        delay bound (initialEq.symm ▸ opportunity) (initialEq.symm ▸ inclusion)
                          timely current (initialEq.symm ▸ trace) clear idle owner
                            (consistent owner)
                            event payload outputEq (values event owner payload (Or.inl outputEq))
                              ready entered stamp due).elim
                | resolve actor payload binding checks outputEq codeEq =>
                    have same := (nodeView_resolve_actor outputEq codeEq).symm.trans owned
                    cases Option.some.inj same
                    exact (phase_due_opening_impossible setup mode deadline leaks plan source
                      bounds wellFormed assessment copies ordered maximal horizon scheduler delay
                        bound opportunity inclusion timely current trace clear idle consistent owner
                          event (by rw [outputEq]; trivial) owned
                            (fun payload outputEq value =>
                              values event owner payload (Or.inr outputEq) value)
                            ready entered stamp due).elim
                | sample payload law outputEq codeEq =>
                    rw [nodeView_sample_actor outputEq codeEq] at owned
                    cases owned
              · rw [environmentStep_expire_of_not_due R _ event ready entered stamp due,
                  PMF.mem_support_pure_iff] at supported
                exact supported
            · rw [environmentStep_expire_of_not_ready R _ event ready,
                PMF.mem_support_pure_iff] at supported
              exact supported
          subst native
          simpa only [RecoveryState.environmentResult, not_and_self, ↓reduceIte] using clear

end Vegas
