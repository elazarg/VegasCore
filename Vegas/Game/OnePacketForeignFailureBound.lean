/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketMainActivationRegularity
import Vegas.Game.OnePacketForeignFailure
import Vegas.Game.OnePacketRareMainMass
import Vegas.Game.OnePacketCertificateDischarge
import Vegas.Pending.ExclusionStoppedBoundary
import Vegas.Pending.ExclusionFailureOwners
import GameTheoryExtensions.Analysis.Protocol.StoppedExitBound

/-! # Rare foreign first failures under actual assembled native counted play

The original source component weights and every focal policy are retained.
Service enters only through genuine clear counted OpportunityAt and
ProtectedInclusionAt predicates. The error is square plus scale times the
actual remaining protocol rank.
-/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

local notation "NativeScheduler" => scheduler
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler

/-- At a represented forced nonlate input, the globally assembled comparison
profile gives a total mass at most square plus scale to every response event
disjoint from source-main support. The original common weights are retained. -/
theorem assembled_event_le_of_disjoint_main
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((N).InfoState who)]
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one weights targetSequence) (n : ℕ)
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
    ((((targetSequence n).strategy who info).toOuterMeasure event).toReal) ≤ (scale n) ^ 2 +
      scale n := by
  let main := honestChoice setup runtime leaks bounds (initialLaw setup) horizon (NativeScheduler)
    (sequence n) who info
  let law := (targetSequence n).strategy who info
  have dominates : ∀ choice, slotRetention (scale n) * (main choice).toReal ≤
      (law choice).toReal := by
    intro choice
    change slotRetention (scale n) * (main choice).toReal ≤
      (((targetSequence n).strategy who info) choice).toReal
    rw [assembled n]
    exact onePacketMixture_ge_honest_of_not_late setup runtime leaks bounds horizon
      (NativeScheduler)
      sequence scale positive le_one n
      ((weights n)) nonlate occurs
      forced choice
  have close := PMF.WithinTV.of_domination main law (slotRetention (scale n))
    (slotRetention_le_one (positive n).le (le_one n)) dominates
  have zero : main.toOuterMeasure event = 0 :=
    (PMF.toOuterMeasure_apply_eq_zero_iff main event).mpr disjoint
  have comparison := close event
  rw [zero, ENNReal.toReal_zero, zero_sub, abs_neg,
    abs_of_nonneg ENNReal.toReal_nonneg] at comparison
  exact comparison.trans (by
    have lower := slotMainRetention_ge (positive n).le (le_one n)
    change 1 - slotRetention (scale n) ≤ (scale n) ^ 2 + scale n
    have retained : 1 - ((scale n) ^ 2 + scale n) ≤ slotRetention (scale n) := by
      simpa only [slotRetention, mul_assoc] using lower
    linarith)

private theorem responseChoice_getD_eq
    (who : Player) (past : List (application setup runtime leaks).PlayerEntry)
    (view : (application setup runtime leaks).PlayerView)
    (choice : (N).Choice who (some (past, view))) :
    responseChoice setup runtime leaks bounds (initialLaw setup) horizon (NativeScheduler) who
      (some (past, view)) (choice.1.getD ⟨none⟩) = choice := by
  classical
  rcases choice with ⟨value, allowed⟩
  change ∃ response ∈ bounds.onePacketActions runtime leaks who past view,
    value = some response at allowed
  obtain ⟨response, offered, rfl⟩ := allowed
  apply Subtype.ext
  simp only [Option.getD_some, responseChoice, dite_eq_left offered]

/-- An actual behavioral step of the same comparison profile, with arbitrary
focal policy, puts at most square plus scale on violating the foreign fresh-main
condition. Idle, focal, and nonfirst callbacks have no such violation. -/
theorem assembled_joint_mainActivation_failure_le
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one weights targetSequence) (n : ℕ)
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
      (Function.update ((targetSequence n).strategy) focal focalPolicy) trace
        running).toOuterMeasure
      {draw | ¬ MainActivationStep setup runtime leaks bounds horizon (NativeScheduler) (sequence
        n) focal
        (some control) draw.1}).toReal) ≤ (scale n) ^ 2 + scale n := by
  classical
  let profile := Function.update ((targetSequence n).strategy) focal focalPolicy
  let jointLaw := (N).behavioralJoint profile trace running
  let bad : Set {joint : Player → Option (application setup runtime leaks).Action //
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Legal
        (some control) joint} :=
    {draw | ¬ MainActivationStep setup runtime leaks bounds horizon (NativeScheduler) (sequence n)
      focal (some control) draw.1}
  change (jointLaw.toOuterMeasure bad).toReal ≤ _
  by_cases eligible : ∃ owner, control.actor = some owner ∧ owner ≠ focal ∧
      FirstActivation setup runtime leaks owner (some (control.execution.recall owner,
        control.execution.observe (application setup runtime leaks) owner))
  · obtain ⟨owner, active, different, first⟩ := eligible
    let info := some (control.execution.recall owner,
      control.execution.observe (application setup runtime leaks) owner)
    let main := honestChoice setup runtime leaks bounds (initialLaw setup) horizon (NativeScheduler)
      (sequence n) owner info
    let optionBad := {selected : Option (application setup runtime leaks).Action |
      responseChoice setup runtime leaks bounds (initialLaw setup) horizon (NativeScheduler) owner
        info
        (selected.getD ⟨none⟩) ∉ main.support}
    have infoEq : (N).infoOf owner trace = info := by
      rw [onePacket_infoOf]
      simp only [ReactiveApplication.observe, active, ↓reduceIte, info]
    have marginal : jointLaw.map (fun draw => draw.1 owner) =
        ((targetSequence n).strategy owner info).map Subtype.val := by
      calc
        jointLaw.map (fun draw => draw.1 owner) =
            (jointLaw.map Subtype.val).map (fun actions => actions owner) :=
          by simp only [PMF.map_comp, Function.comp_def]
        _ = (profile owner ((N).infoOf owner trace)).map Subtype.val := by
          rw [(N).behavioralJoint_map_val, independentProduct_map_eval]
        _ = _ := by
          simpa only [profile, Function.update_of_ne different] using
            congrArg (fun input => ((targetSequence n).strategy owner input).map Subtype.val) infoEq
    have eventEq : bad = (fun draw => draw.1 owner) ⁻¹' optionBad := by
      ext draw
      constructor
      · intro outside supported
        apply outside
        intro actor acts actorDifferent actorFirst
        cases Option.some.inj (active.symm.trans acts)
        exact supported
      · intro outside supported
        exact outside (supported owner active different first)
    have choiceEvent : Subtype.val ⁻¹' optionBad = main.supportᶜ := by
      ext choice
      change (responseChoice setup runtime leaks bounds (initialLaw setup) horizon
        (NativeScheduler) owner
        info (choice.1.getD ⟨none⟩) ∉ main.support) ↔ choice ∉ main.support
      rw [responseChoice_getD_eq]
    have forced := forcedAgent_of_history (runtime := runtime) (⟨some control, trace⟩)
      (forcedState_of_clear_regular_notOwes (runtime := runtime) wellFormed (sequence n) focal
        trace clear regular
        notOwed owner)
    rw [infoEq] at forced
    have massEq : (jointLaw.toOuterMeasure bad).toReal =
        (((targetSequence n).strategy owner info).toOuterMeasure main.supportᶜ).toReal := by
      calc
        (jointLaw.toOuterMeasure bad).toReal =
            ((jointLaw.map (fun draw => draw.1 owner)).toOuterMeasure optionBad).toReal := by
          rw [PMF.toOuterMeasure_map_apply, eventEq]
          rfl
        _ = ((((targetSequence n).strategy owner info).map Subtype.val).toOuterMeasure
          optionBad).toReal :=
          congrArg (fun law : PMF (Option (application setup runtime leaks).Action) =>
            (law.toOuterMeasure optionBad).toReal) marginal
        _ = _ := by rw [PMF.toOuterMeasure_map_apply, choiceEvent]
    calc
      (jointLaw.toOuterMeasure bad).toReal = _ := massEq
      _ ≤ _ := assembled_event_le_of_disjoint_main setup runtime leaks bounds horizon
        scheduler sequence scale positive le_one weights targetSequence assembled n owner info
        (not_lateDelivery_of_firstActivation (runtime := runtime) first) ⟨⟨some control, trace⟩,
          infoEq⟩ forced
        main.supportᶜ disjoint_compl_right
  · have zero : jointLaw.toOuterMeasure bad = 0 :=
      (PMF.toOuterMeasure_apply_eq_zero_iff jointLaw bad).mpr
        (Set.disjoint_left.mpr fun draw _ outside => outside fun owner active different first =>
          (eligible ⟨owner, active, different, first⟩).elim)
    rw [zero, ENNReal.toReal_zero]
    exact add_nonneg (sq_nonneg _) (positive n).le

private theorem oneStep_marker_mass_eq_joint
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player) (cutoff : Nat)
    (profile : ∀ who, (N).BehavioralPolicy who)
    (history : (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History)
    (running : ¬ (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).terminal
      history.state)
    (main : MainActivationTraceAfter setup runtime leaks bounds horizon (NativeScheduler) source
      focal
      cutoff history.trace) (later : cutoff ≤ history.trace.length) :
    (((N).runBehavioralFrom profile 1 history).toOuterMeasure
      {next | ¬ MainActivationTraceAfter setup runtime leaks bounds horizon (NativeScheduler)
        source focal
        cutoff next.trace}).toReal =
      (((N).behavioralJoint profile history.trace running).toOuterMeasure
        {draw | ¬ MainActivationStep setup runtime leaks bounds horizon (NativeScheduler) source
          focal
          history.state draw.1}).toReal := by
  classical
  let mark := fun next : (onePacketProtocol setup runtime leaks bounds horizon
    (NativeScheduler)).History =>
    decide (¬ MainActivationTraceAfter setup runtime leaks bounds horizon (NativeScheduler) source
      focal
      cutoff next.trace)
  let markStep := fun draw : {joint : Player → Option (application setup runtime leaks).Action //
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).Legal history.state
        joint} =>
    decide (¬ MainActivationStep setup runtime leaks bounds horizon (NativeScheduler) source focal
      history.state draw.1)
  have mapped : ((N).runBehavioralFrom profile 1 history).map mark =
      ((N).behavioralJoint profile history.trace running).map markStep := by
    rw [(N).runBehavioralFrom_succ_of_not_terminal profile 0 running, PMF.map_bind]
    calc
      _ = ((N).behavioralJoint profile history.trace running).bind
          (fun draw => PMF.pure (markStep draw)) := by
        apply bind_congr_on_support
        intro draw _
        apply map_bindOnSupport_const
        intro target realized
        change (PMF.pure (history.extend draw.2 realized)).map mark = _
        rw [PMF.pure_map]
        apply congrArg PMF.pure
        simp only [mark, markStep, History.extend, MainActivationTraceAfter, main, later,
          true_implies, true_and]
      _ = _ := PMF.bind_pure_comp _ _
  have mass := congrArg (fun law : PMF Bool => (law.toOuterMeasure {true}).toReal) mapped
  have markEvent : mark ⁻¹' {true} = {next | ¬ MainActivationTraceAfter setup runtime leaks bounds
      horizon (NativeScheduler) source focal cutoff next.trace} := by
    ext next
    simp only [Set.mem_preimage, Set.mem_singleton_iff, mark, decide_eq_true_eq, Set.mem_ofPred_eq]
  have stepEvent : markStep ⁻¹' {true} = {draw | ¬ MainActivationStep setup runtime leaks bounds
    horizon
      (NativeScheduler) source focal history.state draw.1} := by
    ext draw
    simp only [Set.mem_preimage, Set.mem_singleton_iff, markStep, decide_eq_true_eq,
      Set.mem_ofPred_eq]
  calc
    _ = ((((N).runBehavioralFrom profile 1 history).map mark).toOuterMeasure {true}).toReal := by
      rw [PMF.toOuterMeasure_map_apply, markEvent]
    _ = ((((N).behavioralJoint profile history.trace running).map markStep).toOuterMeasure
        {true}).toReal := mass
    _ = _ := by
      rw [PMF.toOuterMeasure_map_apply, stepEvent]
      rfl

/-- Before public exclusion or focal debt, the probability that a foreign first
callback leaves source-main support is bounded by square plus scale times the
actual remaining protocol rank. The focal policy is arbitrary. -/
theorem assembled_marker_mass_le_rank
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one weights targetSequence) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt runtime leaks control.execution delay)
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
      (Function.update ((targetSequence n).strategy) focal focalPolicy)
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
  classical
  let profile := Function.update ((targetSequence n).strategy) focal focalPolicy
  let stopped := fun history :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History =>
    ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history
  let marked := {history :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History |
    ¬ MainActivationTraceAfter setup runtime leaks bounds horizon (NativeScheduler) (sequence n)
      focal
      startTrace.length history.trace}
  let payoff := fun history => @ite ℝ (history ∈ marked) (Classical.propDecidable _) 1 0
  let inside := fun history :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History =>
    (∃ reached, history.state = some reached) ∧ TracePrefix startTrace history.trace ∧
      RegularTrace setup runtime leaks bounds horizon (NativeScheduler) (sequence n) focal
        history.trace ∧
      MainActivationTraceAfter setup runtime leaks bounds horizon (NativeScheduler) (sequence n)
        focal
        startTrace.length history.trace
  have payoffBounded : ∀ history, |payoff history| ≤ 1 := by
    intro history
    dsimp only [payoff]
    split <;> norm_num
  have nonnegative : 0 ≤ (scale n) ^ 2 + scale n := add_nonneg (sq_nonneg _) (positive n).le
  have preserve : ∀ history, inside history → ¬ stopped history →
      ¬ (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).terminal
        history.state →
      ∀ next ∈ ((N).runBehavioralFrom profile 1 history).support,
      next ∉ marked → inside next := by
    intro history valid going running next supported unmarked
    have clear : ReactiveApplication.stateInvariant (app := application setup runtime leaks)
        (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
          history.state := not_not.mp (fun failed => going (Or.inl failed))
    rw [(N).runBehavioralFrom_succ_of_not_terminal profile 0 running,
      PMF.mem_support_bind_iff] at supported
    obtain ⟨draw, _chosen, stepped⟩ := supported
    rw [PMF.mem_support_bindOnSupport_iff] at stepped
    obtain ⟨target, realized, reached⟩ := stepped
    change next ∈ (PMF.pure _).support at reached
    rw [PMF.mem_support_pure_iff] at reached
    subst reached
    obtain ⟨before, beforeState⟩ := valid.1
    rcases history with ⟨previous, trace⟩
    change previous = some before at beforeState
    cases beforeState
    obtain ⟨after, afterState, _recall⟩ := (application setup runtime
      leaks).transition_recall_prefix
      (initialLaw setup) horizon (NativeScheduler) before target draw.1 realized
    cases afterState
    have main : MainActivationTraceAfter setup runtime leaks bounds horizon (NativeScheduler)
      (sequence n)
        focal startTrace.length (trace.extend draw.1 draw.2 realized) := not_not.mp unmarked
    refine ⟨⟨after, rfl⟩, .extend valid.2.1 draw.1 draw.2 realized, ?_, main⟩
    refine ⟨valid.2.2.1, ?_⟩
    cases active : before.actor with
    | none =>
        intro actor acts different
        rw [active] at acts
        cases acts
    | some owner =>
        by_cases same : owner = focal
        · intro actor acts different
          have which := Option.some.inj (active.symm.trans acts)
          exact (different (which.symm.trans same)).elim
        have notOwed : ∀ point,
            decodedPoint setup before.execution.application.config = some point →
            ¬ ProtocolState.OwesFailure focal setup.program point := by
          intro point decoded owed
          exact going (Or.inr (Or.inl (decodedState_of_nativeDecodedState (runtime := runtime)
            (failureProfile setup.program) ⟨some before, trace⟩ decoded owed)))
        exact regularStep_of_native_mainActivationTraceAfter (runtime := runtime) wellFormed
          covers capacity
          (sequence n) focal
          owner same opportunity timely start before startTrace trace
          valid.2.1
          current turn clear valid.2.2.1 notOwed main.1 active draw.1 draw.2
          (main.2 valid.2.1.length_le) after realized
  have futureBound : ∀ history,
      |expect ((N).runBehavioralUntil certificate profile stopped history) payoff| ≤ 1 :=
    fun _ => expect_abs_le_of_bounded zero_le_one payoffBounded
  have estimate := (N).abs_expect_runBehavioralUntil_le_of_exits certificate profile stopped inside
    payoff payoffBounded nonnegative
    (fun history => (application setup runtime leaks).rank horizon history.state)
    (fun history valid _ => by
      have unmarked : history ∉ marked := not_not_intro valid.2.2.2
      simp only [payoff, unmarked, ↓reduceIte])
    (by
      intro history next valid going running member
      obtain ⟨⟨joint, legal, realized⟩, _⟩ :=
        (N).mem_support_runBehavioralFrom_one profile running member
      exact (application setup runtime leaks).rank_step (initialLaw setup) horizon (NativeScheduler)
        history.state next.state joint running realized)
    (by
      intro history valid going running
      obtain ⟨control, controlState⟩ := valid.1
      rcases history with ⟨before, trace⟩
      change before = some control at controlState
      cases controlState
      let history : (onePacketProtocol setup runtime leaks bounds horizon
        (NativeScheduler)).History :=
        ⟨some control, trace⟩
      let step := (N).runBehavioralFrom profile 1 history
      let outside := fun next => if inside next then 0
        else expect ((N).runBehavioralUntil certificate profile stopped next) payoff
      have outsideBound : ∀ next, |outside next| ≤ 1 := by
        intro next
        dsimp only [outside]
        split
        · norm_num
        · exact futureBound next
      have outsideNonnegative : ∀ next, 0 ≤ outside next := by
        intro next
        dsimp only [outside]
        split
        · exact le_rfl
        · apply expect_nonneg
          intro final _
          dsimp only [payoff]
          split <;> norm_num
      have comparison : expect step outside ≤ expect step payoff := by
        apply expect_mono ?_
          (payoffIntegrable_of_bounded step outside outsideBound)
          (payoffIntegrable_of_bounded step payoff payoffBounded)
        intro next member
        dsimp only [outside]
        split
        · dsimp only [payoff]
          split <;> norm_num
        · rename_i outsideNext
          by_cases markedNext : next ∈ marked
          · simpa only [payoff, markedNext, ↓reduceIte] using
              (le_abs_self _).trans (futureBound next)
          · exact (outsideNext (preserve history valid going running next member markedNext)).elim
      have clear : ExclusionEvidence 0 ∅
          (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) :=
        not_not.mp (fun failed => going (Or.inl failed))
      have notOwed : ∀ point, decodedPoint setup control.execution.application.config = some point →
          ¬ ProtocolState.OwesFailure focal setup.program point := by
        intro point decoded owed
        exact going (Or.inr (Or.inl (decodedState_of_nativeDecodedState (runtime := runtime)
          (failureProfile setup.program) history decoded owed)))
      rw [abs_of_nonneg (expect_nonneg step outside (fun next _ => outsideNonnegative next))]
      calc
        expect step outside ≤ expect step payoff := comparison
        _ = (step.toOuterMeasure marked).toReal := by
          simpa only [payoff] using expect_indicator step marked
        _ = _ := oneStep_marker_mass_eq_joint setup runtime leaks bounds horizon scheduler
          (sequence n)
          focal startTrace.length profile history running valid.2.2.2 valid.2.1.length_le
        _ ≤ _ := assembled_joint_mainActivation_failure_le setup runtime leaks bounds horizon
          scheduler
          wellFormed sequence scale positive le_one weights targetSequence assembled n focal
            focalPolicy control trace clear
          valid.2.2.1 notOwed running)
    ⟨some start, startTrace⟩
    ⟨⟨start, rfl⟩, .refl, regular,
      mainActivationTraceAfter_of_length_le (runtime := runtime) (sequence n) focal startTrace
        startTrace.length le_rfl⟩
  have indicator := expect_indicator
    ((N).runBehavioralUntil certificate profile stopped ⟨some start, startTrace⟩) marked
  have indicatorAbs := congrArg abs indicator
  rw [abs_of_nonneg ENNReal.toReal_nonneg] at indicatorAbs
  calc
    _ = |expect ((N).runBehavioralUntil certificate profile stopped ⟨some start, startTrace⟩)
        payoff| := by simpa only [payoff] using indicatorAbs.symm
    _ ≤ _ := estimate

/-- A first foreign public failure remembers a future first
activation outside main support. The environment boundary and all prefix
regularity facts come from the actual stopped continuation. -/
theorem stopped_foreignFailure_marked
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (source : setup.intendedModel.BehavioralAssessment) (focal : Player)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      ProtectedInclusionAt runtime leaks control.execution bound)
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
  classical
  have boundary := responseMenu_stopped_exclusion_boundary runtime leaks (initialLaw setup)
    horizon (NativeScheduler) (bounds.onePacketMenu runtime leaks) certificate profile
    (fun history => DecodedState setup runtime leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history)
    ⟨some start, startTrace⟩ start rfl clear final supported
  intro main
  have regularFinal := (stopped_regular_of_mainActivationTraceAfter (runtime := runtime)
    wellFormed covers
    capacity source focal opportunity timely certificate
    profile extraStop ⟨some start, startTrace⟩ start rfl current turn regular final supported).2.2
    main
  rcases final with ⟨finalState, target⟩
  change finalState = some finalControl at state
  subst finalState
  rcases boundary with finalClear | ⟨remaining, execution, prior, command, next, priorClear,
    priorGoing, _chosen, reached, endpoint, startPrefix, targetPrefix⟩
  · have impossible : owner ∈ (∅ : Finset Player) :=
      (finalClear.excluded_zero owner).mpr ⟨event, owned, failed⟩
    exact Finset.notMem_empty owner impossible
  · cases Option.some.inj endpoint
    have beforeRegular := regularTrace_of_tracePrefix (runtime := runtime) source focal
      targetPrefix regularFinal
    have beforeNotOwed : ∀ point, decodedPoint setup execution.application.config = some point →
        ¬ ProtocolState.OwesFailure focal setup.program point := by
      intro point decoded owed
      apply priorGoing
      left
      exact decodedState_of_nativeDecodedState (runtime := runtime) (failureProfile setup.program)
        ⟨some ⟨remaining + 1, none, execution⟩, prior⟩ decoded owed
    exact firstForeignFailure_not_mainActivationTraceAfter (runtime := runtime) wellFormed covers
      capacity
      source focal owner different opportunity inclusion
      timely
      start startTrace remaining execution prior startPrefix current event turn priorClear
      beforeRegular beforeNotOwed owned command next reached target targetPrefix failed main

/-- From a clear source turn, actual foreign first failures under the common comparison
profile have probability at most square plus scale times remaining protocol rank.
The focal policy is arbitrary, and the runner stops at focal source debt. -/
theorem assembled_foreign_failure_mass_le_rank
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one weights targetSequence) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      ProtectedInclusionAt runtime leaks control.execution bound)
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
      (Function.update ((targetSequence n).strategy) focal focalPolicy)
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
  classical
  let profile := Function.update ((targetSequence n).strategy) focal focalPolicy
  let stopped := fun history :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History =>
    ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history
  let law := (N).runBehavioralUntil certificate profile stopped ⟨some start, startTrace⟩
  let failures := {final :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History |
    ∃ (control : (application setup runtime leaks).Control) (owner : Player)
      (event : (graph setup).EventId), final.state = some control ∧ owner ≠ focal ∧
      (graph setup).actor? event = some owner ∧ control.execution.application.PublicFailure event}
  let marked := {final :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History |
    ¬ MainActivationTraceAfter setup runtime leaks bounds horizon (NativeScheduler) (sequence n)
      focal
      startTrace.length final.trace}
  have subset : failures ∩ law.support ⊆ marked := by
    rintro final ⟨⟨control, owner, event, state, different, owned, failed⟩, supported⟩
    exact stopped_foreignFailure_marked setup runtime leaks bounds horizon scheduler wellFormed
      covers capacity (sequence n) focal opportunity inclusion timely certificate profile extraStop
      start startTrace current turn clear regular final supported control state owner different
      event
      owned failed
  have mass : law.toOuterMeasure failures ≤ law.toOuterMeasure marked := by
    calc
      _ = law.toOuterMeasure (failures ∩ law.support) := by
        rw [← PMF.toOuterMeasure_apply_inter_support]
      _ ≤ _ := MeasureTheory.measure_mono subset
  calc
    _ = (law.toOuterMeasure failures).toReal := rfl
    _ ≤ (law.toOuterMeasure marked).toReal := ENNReal.toReal_mono (outerMeasure_ne_top _ _) mass
    _ ≤ _ := assembled_marker_mass_le_rank setup runtime leaks bounds horizon scheduler wellFormed
      covers capacity sequence scale positive le_one weights targetSequence assembled n focal
        focalPolicy opportunity timely
      certificate extraStop start startTrace current turn regular


private theorem foreign_failure_of_unclear_survival (focal : Player)
    (history : (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History)
    (unclear : ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state)
    (survives : focal ∉ nativeFailureOwners runtime leaks history.state) :
    ∃ (control : (application setup runtime leaks).Control) (owner : Player)
      (event : (graph setup).EventId), history.state = some control ∧ owner ≠ focal ∧
      (graph setup).actor? event = some owner ∧ control.execution.application.PublicFailure event
        := by
  classical
  rcases history with ⟨state, trace⟩
  cases state with
  | none => exact (unclear trivial).elim
  | some control =>
    have receipts := native_receiptsComplete_history runtime leaks (initialLaw setup)
      (serviceInitialLaw_initialized setup) horizon (NativeScheduler)
      ((bounds.onePacketMenu runtime leaks).toRawTrace (initialLaw setup) horizon
        (NativeScheduler) trace)
    have witness : ∃ (owner : Player) (event : (graph setup).EventId),
        (graph setup).actor? event = some owner ∧
          control.execution.application.PublicFailure event := by
      by_contra missing
      apply unclear
      refine ⟨receipts, fun event lower => by omega, fun owner => ⟨?_, ?_⟩⟩
      · intro member
        exact (Finset.notMem_empty owner member).elim
      · rintro (inherited | ⟨event, _lower, owned, failed⟩)
        · exact inherited
        · exact (missing ⟨owner, event, owned, failed⟩).elim
    obtain ⟨owner, event, owned, failed⟩ := witness
    refine ⟨control, owner, event, rfl, ?_, owned, failed⟩
    intro same
    subst owner
    apply survives
    change focal ∈ control.execution.application.failureOwners
    simp only [EventGraphRuntime.State.failureOwners, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨event, owned, failed⟩

/-- The actual foreign first-exit event of the debt-stopped common comparison
profile is bounded by square plus scale times remaining protocol rank. -/
theorem assembled_foreign_exit_mass_le_rank
    [(application setup runtime leaks).FiniteNature (initialLaw setup) (NativeScheduler)]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one weights targetSequence) (n : ℕ)
    (focal : Player) (focalPolicy : (N).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace (some control) →
      ExclusionEvidence 0 ∅ (⟨control.execution.application, ∅⟩ : RecoveryState (graph setup)) →
      ProtectedInclusionAt runtime leaks control.execution bound)
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
      (Function.update ((targetSequence n).strategy) focal focalPolicy)
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
  classical
  let profile := Function.update ((targetSequence n).strategy) focal focalPolicy
  let stopped := fun history :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History =>
    ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        history.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure focal setup.program) history.state ∨ extraStop history
  let law := (N).runBehavioralUntil certificate profile stopped ⟨some start, startTrace⟩
  let exits := {final :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History |
    ¬ ReactiveApplication.stateInvariant (app := application setup runtime leaks)
      (fun native => ExclusionEvidence 0 ∅ (⟨native, ∅⟩ : RecoveryState (graph setup)))
        final.state ∧
      focal ∉ nativeFailureOwners runtime leaks final.state}
  let failures := {final :
      (onePacketProtocol setup runtime leaks bounds horizon (NativeScheduler)).History |
    ∃ (control : (application setup runtime leaks).Control) (owner : Player)
      (event : (graph setup).EventId), final.state = some control ∧ owner ≠ focal ∧
      (graph setup).actor? event = some owner ∧ control.execution.application.PublicFailure event}
  have subset : exits ⊆ failures := by
    intro final eligible
    exact foreign_failure_of_unclear_survival setup runtime leaks bounds horizon scheduler focal
      final
      eligible.1 eligible.2
  have mass : law.toOuterMeasure exits ≤ law.toOuterMeasure failures :=
    MeasureTheory.measure_mono subset
  calc
    _ = (law.toOuterMeasure exits).toReal := rfl
    _ ≤ (law.toOuterMeasure failures).toReal := ENNReal.toReal_mono (outerMeasure_ne_top _ _) mass
    _ ≤ _ := assembled_foreign_failure_mass_le_rank setup runtime leaks bounds horizon scheduler
      wellFormed covers capacity sequence scale positive le_one weights targetSequence
        assembled n focal focalPolicy
      opportunity inclusion timely certificate extraStop start startTrace current turn clear regular

end Vegas.OnePacketComparison
