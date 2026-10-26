/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Pending.ExclusionStoppedBoundary
import Vegas.Pending.ExclusionFailureOwners
import Vegas.Game.RecoveryNativeComparison
import Vegas.Game.OnePacketForeignFailureBound
import Vegas.Game.OnePacketRareMainMass
import Vegas.Game.RecoveryForeignFailure
import Vegas.Game.OnePacketDebtRouting
import GameTheoryExtensions.Analysis.Protocol.StoppedExitBound

/-! # Rare first responses of the common native comparison profile -/

noncomputable section

namespace Vegas

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)}

/-- At a clear regular prefix before focal debt, previous source-main foreign
first callbacks prevent the current foreign callback from being a late delivery.
The comparison begins at an actual focal source turn. -/
theorem recovery_nonlate_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (start control : (application setup runtime leaks).Control)
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some start))
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (main : MainActivationTraceAfter setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
      startTrace.length trace) :
    ¬ LateDelivery setup runtime leaks owner (some (control.execution.recall owner,
      control.execution.observe (application setup runtime leaks) owner)) := by
  have nativeOpportunity (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks control.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity
      control actual clear
  exact nonlate_of_mainActivationTraceAfter (runtime := runtime) wellFormed covers capacity source
    focal owner
    different nativeOpportunity timely start control startTrace trace startPrefix current turn
    clear regular notOwed main

theorem recovery_response_main_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (start control : (application setup runtime leaks).Control)
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some start))
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (main : MainActivationTraceAfter setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
      startTrace.length trace)
    (active : control.actor = some owner)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Legal
        (some control) joint)
    (stepMain : MainActivationStep setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
      (some control) joint) :
    responseChoice setup runtime leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) owner
      (some (control.execution.recall owner,
        control.execution.observe (application setup runtime leaks) owner)) ((joint owner).getD
          ⟨none⟩) ∈
      (honestChoice setup runtime leaks bounds (initialLaw setup) horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler) source owner
        (some (control.execution.recall owner,
          control.execution.observe (application setup runtime leaks) owner))).support := by
  have nativeOpportunity (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks control.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity
      control actual clear
  exact response_main_of_mainActivationTraceAfter (runtime := runtime) wellFormed covers capacity
    source focal owner
    different nativeOpportunity timely start control startTrace trace startPrefix current turn
    clear regular notOwed main active joint legal stepMain

theorem regularStep_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal owner : Player)
    (different : owner ≠ focal)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (start control : (application setup runtime leaks).Control)
    (startTrace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some start))
    (trace : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
    (startPrefix : TracePrefix startTrace trace)
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (main : MainActivationTraceAfter setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
      startTrace.length trace)
    (active : control.actor = some owner)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Legal
        (some control) joint)
    (stepMain : MainActivationStep setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
      (some control) joint)
    (next : (application setup runtime leaks).Control)
    (realized : some next ∈ ((onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).step
        (some control) ⟨joint, legal⟩).support) :
    RegularStep setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
      (some control) joint (some next) := by
  have nativeOpportunity (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks control.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity
      control actual clear
  exact regularStep_of_native_mainActivationTraceAfter (runtime := runtime) wellFormed covers
    capacity source focal
    owner different nativeOpportunity timely start control startTrace trace startPrefix current
    turn clear regular notOwed main active joint legal stepMain next realized

theorem recovery_stopped_regular_of_mainActivationTraceAfter
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {initial : PMF (RecoveryState (graph setup))}
    (initialized : ∀ state ∈ initial.support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)))
    (nativeLaw : initial.map RecoveryState.native = initialLaw setup)
    {horizon : Nat} {scheduler : (runtime.recoveryApplication leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (certificate : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).WellFoundedHistories)
    (profile : ∀ who, (onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).BehavioralPolicy who)
    (extraStop : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).History → Prop)
    (start : (onePacketProtocol setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).History)
    (control : (application setup runtime leaks).Control) (state : start.state = some control)
    (current : (graph setup).EventId)
    (turn : control.execution.application.publicView.ownTurn? focal = some current)
    (regular : RegularTrace setup runtime leaks bounds horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
      start.trace) :
    ∀ final ∈ ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
      (RecoveryProjection.nativeScheduler runtime leaks scheduler)).runBehavioralUntil
        certificate profile (fun history =>
          ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
            (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
              history.state ∨
          DecodedState setup runtime leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
        start).support,
      (∃ reached, final.state = some reached) ∧ TracePrefix start.trace final.trace ∧
        (MainActivationTraceAfter setup runtime leaks bounds horizon
          (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
          start.trace.length final.trace →
          RegularTrace setup runtime leaks bounds horizon
            (RecoveryProjection.nativeScheduler runtime leaks scheduler) source focal
            final.trace) := by
  have nativeOpportunity (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks control.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity
      control actual clear
  exact stopped_regular_of_mainActivationTraceAfter (runtime := runtime) wellFormed covers
    capacity source focal
    nativeOpportunity timely certificate profile extraStop start control state current turn
    regular


end Vegas

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication runtime leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler runtime leaks scheduler
local notation "R" => model setup runtime leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
  (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu runtime leaks bounds) Initial horizon scheduler

theorem nativeComparisonStrategy_event_le_of_disjoint_main [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ)
    (who : Player) (info : (application setup runtime leaks).Info)
    (nonlate : ¬ LateDelivery setup runtime leaks who info)
    (occurs : ∃ history : (ReactiveApplication.ResponseMenu.protocol
      (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon
        (NativeScheduler)).History, (N).infoOf who history.trace = info)
    (forced : Vegas.forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks)
      (initialLaw setup)
      horizon (NativeScheduler) who info)
    (event : Set ((N).Choice who info))
    (disjoint : Disjoint
      (honestChoice setup runtime leaks bounds (initialLaw setup) horizon (NativeScheduler)
        (sequence n)
        who info).support event) :
    (((nativeComparisonStrategy setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one
      weights n who info).toOuterMeasure event).toReal) ≤ (scale n) ^ 2 + scale n := by
  exact OnePacketComparison.assembled_event_le_of_disjoint_main setup runtime leaks bounds horizon
    (NativeScheduler) sequence scale positive le_one (fun n => nativeComparisonWeights setup
      runtime leaks
    bounds horizon scheduler (weights n)) (nativeComparisonSequence setup runtime leaks bounds
      horizon
    scheduler sequence scale positive le_one weights) (nativeComparisonSequence_assembled setup
      runtime
    leaks bounds horizon scheduler sequence scale positive le_one weights) n who info nonlate
    occurs forced event disjoint

theorem nativeComparison_joint_mainActivation_failure_le [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    (control : (application setup runtime leaks).Control)
    (trace : (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some
      control))
    (clear : ExclusionEvidence 0 ∅
      (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n)
      focal trace)
    (notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
      ¬ ProtocolState.OwesFailure focal setup.program point)
    (running : ¬ (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).terminal
      (some control)) :
    ((((N).behavioralJoint
      (Function.update (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler
        sequence scale
        positive le_one weights n) focal focalPolicy) trace running).toOuterMeasure
      {draw | ¬ MainActivationStep setup runtime leaks bounds horizon (NativeScheduler) (sequence
        n) focal
        (some control) draw.1}).toReal) ≤ (scale n) ^ 2 + scale n := by
  exact OnePacketComparison.assembled_joint_mainActivation_failure_le setup runtime leaks bounds
    horizon
    (NativeScheduler) wellFormed sequence scale positive le_one (fun n => nativeComparisonWeights
      (runtime := runtime)
    setup leaks bounds horizon scheduler (weights n)) (nativeComparisonSequence setup runtime
      leaks bounds
    horizon scheduler sequence scale positive le_one weights) (nativeComparisonSequence_assembled
      (runtime := runtime)
    setup leaks bounds horizon scheduler sequence scale positive le_one weights) n focal
    focalPolicy control trace clear regular notOwed running

theorem nativeComparison_marker_mass_le_rank [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks Initial horizon scheduler delay)
    (timely : runtime.AsyncTimely delay bound)
    (certificate :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).WellFoundedHistories)
    (extraStop : (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History
      → Prop)
    (start : (application setup runtime leaks).Control)
    (startTrace :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (regular : RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) focal
      startTrace) :
    (((N).runBehavioralUntil certificate
      (Function.update (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler
        sequence scale
        positive le_one weights n) focal focalPolicy)
      (fun history => ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
        DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).toOuterMeasure
      {final | ¬ MainActivationTraceAfter setup runtime leaks bounds horizon (NativeScheduler)
        (sequence n)
        focal startTrace.length final.trace}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application setup runtime leaks).rank horizon (some start) := by
  have initialized : ∀ state ∈ (Initial).support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)) := by
    intro state member
    obtain ⟨native, nativeMember, rfl⟩ := PMF.support_map .. ▸ member
    obtain ⟨inputs, rfl⟩ := serviceInitialLaw_initialized setup native nativeMember
    exact ⟨inputs, rfl⟩
  have nativeLaw : (Initial).map RecoveryState.native = initialLaw setup := initialLaw_native setup
  have nativeOpportunity (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks control.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity
      control actual clear
  exact OnePacketComparison.assembled_marker_mass_le_rank setup runtime leaks bounds horizon
    (NativeScheduler) wellFormed covers capacity sequence scale positive le_one (fun n =>
    nativeComparisonWeights setup runtime leaks bounds horizon scheduler (weights n))
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
    weights) (nativeComparisonSequence_assembled setup runtime leaks bounds horizon scheduler
      sequence
    scale positive le_one weights) n focal focalPolicy nativeOpportunity timely certificate
    extraStop start startTrace current turn regular

theorem recovery_stopped_foreignFailure_marked
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks (Initial) horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks (Initial) horizon scheduler
      bound)
    (timely : runtime.AsyncTimely delay bound)
    (certificate : (onePacketProtocol setup runtime leaks bounds horizon
      (NativeScheduler)).WellFoundedHistories)
    (profile : ∀ who, (N).BehavioralPolicy who)
    (extraStop : (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History
      → Prop)
    (start : (application setup runtime leaks).Control)
    (startTrace :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨start.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon (NativeScheduler) source focal
      startTrace)
    (final : (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History)
    (supported : final ∈ ((N).runBehavioralUntil certificate profile (fun history =>
      ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).support)
    (finalControl : (application setup runtime leaks).Control) (state : final.state = some
      finalControl)
    (owner : Player) (different : owner ≠ focal) (event : (graph setup).EventId)
    (owned : (graph setup).actor? event = some owner)
    (failed : finalControl.execution.application.PublicFailure event) :
    ¬ MainActivationTraceAfter setup runtime leaks bounds horizon (NativeScheduler) source focal
      startTrace.length final.trace := by
  have initialized : ∀ state ∈ (Initial).support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)) := by
    intro state member
    obtain ⟨native, nativeMember, rfl⟩ := PMF.support_map .. ▸ member
    obtain ⟨inputs, rfl⟩ := serviceInitialLaw_initialized setup native nativeMember
    exact ⟨inputs, rfl⟩
  have nativeLaw : (Initial).map RecoveryState.native = initialLaw setup := initialLaw_native setup
  have nativeOpportunity (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks control.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity
      control actual clear
  have nativeInclusion (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      ProtectedInclusionAt runtime leaks control.execution bound := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.ProtectedInclusion.clear_native runtime leaks initialized inclusion
      control actual clear
  exact OnePacketComparison.stopped_foreignFailure_marked setup runtime leaks bounds horizon
    (NativeScheduler) wellFormed covers capacity source focal nativeOpportunity nativeInclusion
    timely certificate profile extraStop start startTrace current turn clear regular final
    supported finalControl state owner different event owned failed

theorem nativeComparison_foreign_failure_mass_le_rank [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (certificate :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).WellFoundedHistories)
    (extraStop : (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History
      → Prop)
    (start : (application setup runtime leaks).Control)
    (startTrace :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨start.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) focal
      startTrace) :
    (((N).runBehavioralUntil certificate
      (Function.update (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler
        sequence scale
        positive le_one weights n) focal focalPolicy)
      (fun history => ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
        DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).toOuterMeasure
      {final | ∃ (control : (application setup runtime leaks).Control) (owner : Player)
        (event : (graph setup).EventId), final.state = some control ∧ owner ≠ focal ∧
        (graph setup).actor? event = some owner ∧
          control.execution.application.PublicFailure event}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application setup runtime leaks).rank horizon (some start) := by
  have initialized : ∀ state ∈ (Initial).support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)) := by
    intro state member
    obtain ⟨native, nativeMember, rfl⟩ := PMF.support_map .. ▸ member
    obtain ⟨inputs, rfl⟩ := serviceInitialLaw_initialized setup native nativeMember
    exact ⟨inputs, rfl⟩
  have nativeLaw : (Initial).map RecoveryState.native = initialLaw setup := initialLaw_native setup
  have nativeOpportunity (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks control.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity
      control actual clear
  have nativeInclusion (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      ProtectedInclusionAt runtime leaks control.execution bound := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.ProtectedInclusion.clear_native runtime leaks initialized inclusion
      control actual clear
  exact OnePacketComparison.assembled_foreign_failure_mass_le_rank setup runtime leaks bounds
    horizon
    (NativeScheduler) wellFormed covers capacity sequence scale positive le_one (fun n =>
    nativeComparisonWeights setup runtime leaks bounds horizon scheduler (weights n))
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
    weights) (nativeComparisonSequence_assembled setup runtime leaks bounds horizon scheduler
      sequence
    scale positive le_one weights) n focal focalPolicy nativeOpportunity nativeInclusion timely
    certificate extraStop start startTrace current turn clear regular

theorem nativeComparison_foreign_exit_mass_le_rank [Fintype (RP).History]
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((R).InfoState who)] [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup runtime leaks bounds Initial horizon scheduler slots p))
      (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity runtime leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion runtime leaks Initial horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (certificate :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).WellFoundedHistories)
    (extraStop : (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History
      → Prop)
    (start : (application setup runtime leaks).Control)
    (startTrace :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Trace (some start))
    (current : (graph setup).EventId)
    (turn : start.execution.application.publicView.ownTurn? focal = some current)
    (clear : ExclusionEvidence 0 ∅
      (⟨start.execution.application, ∅⟩ : RecoveryState (graph setup)))
    (regular : RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) focal
      startTrace) :
    (((N).runBehavioralUntil certificate
      (Function.update (nativeComparisonStrategy setup runtime leaks bounds horizon scheduler
        sequence scale
        positive le_one weights n) focal focalPolicy)
      (fun history => ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state ∨
        DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
      ⟨some start, startTrace⟩).toOuterMeasure
      {final | ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          final.state ∧
        focal ∉ nativeFailureOwners runtime leaks final.state}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application setup runtime leaks).rank horizon (some start) := by
  have initialized : ∀ state ∈ (Initial).support, ∃ inputs,
      state = (⟨State.initial inputs, ∅⟩ : RecoveryState (graph setup)) := by
    intro state member
    obtain ⟨native, nativeMember, rfl⟩ := PMF.support_map .. ▸ member
    obtain ⟨inputs, rfl⟩ := serviceInitialLaw_initialized setup native nativeMember
    exact ⟨inputs, rfl⟩
  have nativeLaw : (Initial).map RecoveryState.native = initialLaw setup := initialLaw_native setup
  have nativeOpportunity (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      OpportunityAt runtime leaks control.execution delay := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.Opportunity.clear_native runtime leaks initialized opportunity
      control actual clear
  have nativeInclusion (control : (application setup runtime leaks).Control)
      (prior : (onePacketProtocol setup runtime leaks bounds horizon
        (RecoveryProjection.nativeScheduler runtime leaks scheduler)).Trace (some control))
      (clear : ExclusionEvidence 0 ∅
        (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup))) :
      ProtectedInclusionAt runtime leaks control.execution bound := by
    have actual := (bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup)
      horizon (RecoveryProjection.nativeScheduler runtime leaks scheduler) prior
    rw [← nativeLaw] at actual
    exact Recovery.ProtectedInclusion.clear_native runtime leaks initialized inclusion
      control actual clear
  exact OnePacketComparison.assembled_foreign_exit_mass_le_rank setup runtime leaks bounds horizon
    (NativeScheduler) wellFormed covers capacity sequence scale positive le_one (fun n =>
    nativeComparisonWeights setup runtime leaks bounds horizon scheduler (weights n))
    (nativeComparisonSequence setup runtime leaks bounds horizon scheduler sequence scale positive
      le_one
    weights) (nativeComparisonSequence_assembled setup runtime leaks bounds horizon scheduler
      sequence
    scale positive le_one weights) n focal focalPolicy nativeOpportunity nativeInclusion timely
    certificate extraStop start startTrace current turn clear regular

end Vegas.RecoveryOnePacket
