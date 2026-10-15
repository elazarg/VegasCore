/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseCanonicalExpiry
import Vegas.Pending.PhaseNativeFailureExit

/-! # Canonical physical histories have no first exclusion -/

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

private theorem environment_clear
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol start horizon scheduler).Trace
      (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (idle : current.actor = none)
    (consistent : ∀ owner, (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      owner).Consistent (current.execution.recall owner))
    (command : (P).Command) (next : (P).Execution)
    (supported : next ∈ (current.execution.environmentStep P command).support) :
    next.application.current.excluded = ∅ := by
  classical
  unfold ReactiveApplication.Execution.environmentStep at supported
  obtain ⟨effect, effectSupport, rfl⟩ := PMF.mem_support_map_iff .. |>.mp supported
  cases command with
  | wait =>
      rw [PMF.mem_support_pure_iff] at effectSupport
      subst effect
      exact clear
  | activate owner =>
      obtain ⟨known, _observed, rfl⟩ := PMF.mem_support_map_iff .. |>.mp effectSupport
      exact clear
  | «include» identifier =>
      rw [PMF.mem_support_pure_iff] at effectSupport
      subst effect
      unfold ReactiveApplication.Execution.includePending
      cases lookup : current.execution.network.includePending identifier with
      | mk envelope network =>
          cases envelope with
          | none => exact clear
          | some message =>
              change ((current.execution.application.handle R message).getD
                current.execution.application).current.excluded = ∅
              cases handled : current.execution.application.handle R message with
              | none => exact clear
              | some image =>
                  exact phaseSourcePolicy_handle_clear_of_history setup mode deadline leaks source
                    bounds wellFormed assessment copies plan maximal horizon scheduler current trace
                      clear consistent message image handled
  | application command =>
      obtain ⟨image, applicationSupport, rfl⟩ := PMF.mem_support_map_iff .. |>.mp effectSupport
      change image ∈ (current.execution.application.environment R command).support
        at applicationSupport
      unfold PhaseRuntimeState.environment at applicationSupport
      split at applicationSupport
      · obtain ⟨native, nativeSupport, rfl⟩ := PMF.mem_support_map_iff .. |>.mp applicationSupport
        apply (PhaseRuntimeState.settle_physical _ _ _ _ _).1.trans
        exact phaseSourcePolicy_environmentResult_clear_of_history setup mode deadline leaks source
          bounds wellFormed assessment copies continuing plan ordered maximal horizon scheduler
            capacity delay bound opportunity inclusion timely values current trace clear idle
              consistent command native nativeSupport
      · rw [PMF.mem_support_pure_iff] at applicationSupport
        subst image
        exact clear

/-- One actual transition cannot introduce the first exclusion under canonical
copied play and the original all-legal-history physical service bounds. -/
theorem phaseSourcePolicy_transition_clear_of_history
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol start horizon scheduler).Trace
      (some current))
    (clear : current.execution.application.current.excluded = ∅)
    (consistent : ∀ owner, (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      owner).Consistent (current.execution.recall owner))
    (joint : Player → Option (P).Action) (next : (P).Control)
    (supported : some next ∈ ((P).transition start horizon scheduler
      (some current) joint).support) :
    next.execution.application.current.excluded = ∅ := by
  classical
  cases actor : current.actor with
  | some owner =>
      simp only [ReactiveApplication.transition, actor, PMF.mem_support_pure_iff,
        Option.some.injEq] at supported
      subst next
      rcases (joint owner).getD ⟨none⟩ with ⟨transmission⟩
      cases transmission <;> exact clear
  | none =>
      cases remaining : current.remaining with
      | zero =>
          simp only [ReactiveApplication.transition, actor, remaining,
            PMF.mem_support_pure_iff, Option.some.injEq] at supported
          subst next
          exact clear
      | succ fuel =>
          simp only [ReactiveApplication.transition, actor, remaining,
            PMF.mem_support_bind_iff, PMF.mem_support_map_iff] at supported
          obtain ⟨command, _command, effect, moved, same⟩ := supported
          cases Option.some.inj same
          exact environment_clear setup mode deadline leaks source bounds wellFormed assessment
            copies continuing plan ordered maximal horizon scheduler capacity delay bound
              opportunity
              inclusion timely values current trace clear actor consistent command effect moved

/-- Every actual canonical counted history is clear. The service premises
range over all legal raw physical histories, and are restricted only inside
the proof; no reconstructed global native service contract is assumed. -/
theorem phaseSourcePolicy_clear_history
    (current : (P).Control)
    (trace : ((PhaseCount.onePacketMenu R leaks bounds).protocol start horizon scheduler).Trace
      (some current))
    (consistent : ∀ owner, (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      owner).Consistent (current.execution.recall owner)) :
    current.execution.application.current.excluded = ∅ := by
  classical
  by_contra failed
  obtain ⟨before, after, prior, joint, legal, moved, clear, excluded, retained⟩ :=
    PhaseNativeProjection.exists_first_exclusion_transition R leaks plan bounds I horizon scheduler
      trace ⟨current, rfl, Finset.nonempty_iff_ne_empty.mpr failed⟩
  have earlier : TracePrefix prior trace :=
    (TracePrefix.extend (.refl : TracePrefix prior prior) joint legal moved).trans retained
  have rawPath := (PhaseCount.onePacketMenu R leaks bounds).reaches_raw start horizon scheduler
    earlier.reachesWithin
  have priorConsistent : ∀ owner, (phaseSourcePolicy setup mode R leaks bounds wellFormed assessment
      owner).Consistent (before.execution.recall owner) := by
    intro owner
    obtain ⟨later, word⟩ := (P).reaches_recall_prefix start horizon scheduler rawPath
      before current rfl rfl owner
    exact ReactiveApplication.Policy.Consistent.of_append (word ▸ consistent owner)
  have nextClear := phaseSourcePolicy_transition_clear_of_history setup mode deadline leaks source
    bounds wellFormed assessment copies continuing plan ordered maximal horizon scheduler capacity
      delay bound opportunity inclusion timely values before prior clear priorConsistent joint after
        moved
  rw [nextClear] at excluded
  exact Finset.not_nonempty_empty excluded

end Vegas
