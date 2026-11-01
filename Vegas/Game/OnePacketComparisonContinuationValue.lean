/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketComparisonRetention
import Vegas.Game.OnePacketStoppedContinuationValue
import Vegas.Game.OnePacketSiteLinearity

/-! # Source continuation values of the common native comparison profile -/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "NP" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

omit [Fintype Player] in
private theorem sourceContinuation_value_of_prefix
    (profile : BehavioralProfile setup.program)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player)
    {rank : Nat} {config : (graph setup).Config} {point : ProtocolState setup.program}
    (decoded : sourceServicePrefix? setup rank config = some point) :
    expect (sourceContinuation setup profile rank config)
      (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout who) =
      sourcePointValue setup parameter utility excludedPayoff profile who point := by
  have lawEq : sourceContinuation setup profile rank config =
      (setup.continuationLaw profile (some point)).map some :=
    congrArg (fun decoded => (setup.continuationLaw profile decoded).map some) decoded
  exact congrArg (fun law => expect law
    (fun readout => exclusionReadoutUtility setup parameter utility excludedPayoff readout who))
    lawEq

open Classical in
/-- The same common native weights approximate the source value at every
intended boundary, under counted native service and completion. -/
theorem assembled_stopped_boundary_value_sub_le
    [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ player, bindingEventCount (graph setup) player < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler slots p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive
      le_one weights targetSequence) (n : ℕ)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : ∀ control : (application setup runtime leaks).Control,
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      OpportunityAt runtime leaks control.execution delay)
    (inclusion : ∀ control : (application setup runtime leaks).Control,
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      ProtectedInclusionAt runtime leaks control.execution bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : ∀ control : (application setup runtime leaks).Control,
      ((bounds.onePacketMenu runtime leaks).protocol (initialLaw setup) horizon
        scheduler).Trace (some control) →
      control.execution.application.config.defaulted = ∅ →
      (application setup runtime leaks).terminal (some control) →
      control.execution.application.config.cut.Terminal)
    (certificate : (NP).WellFoundedHistories)
    (rank : Nat) (start : (NP).History) (anchor : (application setup runtime leaks).Execution)
    (state : start.state = some ⟨horizon - anchor.environmentRecall.length, none, anchor⟩)
    (boundary : ReachedBoundary setup runtime leaks horizon scheduler rank anchor)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank anchor.application.config = some point)
    (intended : ProtocolState.Intended setup.program point)
    {Parameter : Type} (parameter : State L setup.context → Parameter)
    (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
    (excludedPayoff : Player → ℝ) (who : Player) {payoffBound : ℝ}
    (boundNonneg : 0 ≤ payoffBound)
    (payoffBounded : ∀ history : (NP).History,
      |exclusionBase setup runtime parameter utility excludedPayoff leaks history.state who| ≤
        payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) :
    let stopped := fun history : (NP).History => ¬ Clear history.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) history.state
    |expect ((N).runBehavioralUntil certificate
        ((targetSequence n).strategy) stopped start)
        (fun final => if stopped final then excludedPayoff who else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who) -
      sourcePointValue setup parameter utility excludedPayoff
        (setup.intendedOpeningProfile (sequence n).strategy) who point| ≤
      (2 * payoffBound * (1 - slotRetention (scale n))) *
        (application setup runtime leaks).rank horizon start.state := by
  intro stopped
  have retained := assembled_dominatesHonestFrom_boundary setup runtime leaks bounds horizon
    scheduler
    wellFormed covers capacity sequence scale positive le_one weights targetSequence
      assembled n opportunity inclusion timely
    completes certificate rank start anchor state boundary point decoded intended
  have estimate := counted_stopped_boundary_value_sub_le (runtime := runtime) opportunity
    inclusion timely
    completes wellFormed covers capacity
    (sequence n) certificate rank start anchor state boundary point decoded intended
    ((targetSequence n).strategy) (slotRetention_nonneg (positive n).le (le_one n))
    (slotRetention_le_one (positive n).le (le_one n)) retained parameter utility excludedPayoff who
    boundNonneg payoffBounded excludedBounded
  have sourceValue := sourceContinuation_value_of_prefix setup
    (setup.intendedOpeningProfile (sequence n).strategy) parameter utility excludedPayoff who
    decoded
  rw [sourceValue] at estimate
  exact estimate

variable {setup runtime leaks bounds horizon scheduler}

/-- Before the next source event completes, the configuration remains fixed.
Consequently an intended start has no earlier public-exclusion or own-debt stop. -/
theorem debtStopped_eq_bind_eventPhase
    (certificate : (NP).WellFoundedHistories)
    (players : ∀ who, (N).BehavioralPolicy who) (who : Player)
    (start : (NP).History) (control : (application setup runtime leaks).Control)
    (current : start.state = some control) {rank : Nat}
    (ordered : control.execution.application.config.cut.IsPrefix rank)
    (point : ProtocolState setup.program)
    (decoded : sourceServicePrefix? setup rank control.execution.application.config = some point)
    (intended : ProtocolState.Intended setup.program point) :
    let phase := fun history : (NP).History =>
      LateStopped setup runtime leaks bounds horizon scheduler rank history ∨ ¬ Clear history.state
    let stopped := fun history : (NP).History => ¬ Clear history.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) history.state
    (N).runBehavioralUntil certificate players stopped start =
      ((N).runBehavioralUntil certificate players phase start).bind
        ((N).runBehavioralUntil certificate players stopped) := by
  classical
  intro phase stopped
  let inside := fun history : (NP).History => phase history ∨
    ∃ before : (application setup runtime leaks).Control, history.state = some before ∧
      before.execution.application.config = control.execution.application.config
  have safe : ∀ history, inside history → ¬ phase history → ¬ stopped history := by
    intro history holds going
    obtain ⟨before, state, configEq⟩ := holds.resolve_left going
    have pointDecoded : decodedPoint setup before.execution.application.config = some point := by
      rw [configEq]
      exact (decodedPoint_eq_of_isPrefix ordered).trans decoded
    have clear : Clear history.state := by
      rw [state]
      exact defaulted_eq_empty_of_decodedIntended pointDecoded intended
    rintro (unclear | owed)
    · exact unclear clear
    · rw [state] at owed
      obtain ⟨found, ⟨residual⟩, holds⟩ := owed
      exact ProtocolState.Intended.not_owesFailure who setup.program point intended
        (holds point
          ((decodedPoint_eq_of_isPrefix residual.checkpoint.ordered).symm.trans pointDecoded))
  have preserve : ∀ history next, inside history → ¬ phase history →
      ¬ (NP).terminal history.state →
      next ∈ ((N).runBehavioralFrom players 1 history).support → inside next := by
    intro history next holds going running member
    obtain ⟨before, state, configEq⟩ := holds.resolve_left going
    obtain ⟨⟨joint, _, realized⟩, _⟩ :=
      (N).mem_support_runBehavioralFrom_one players running member
    change next.state ∈ ((application setup runtime leaks).transition (initialLaw setup)
      horizon scheduler history.state joint).support at realized
    rw [state] at realized
    obtain ⟨after, afterState, _⟩ := (application setup runtime leaks).transition_recall_prefix
      (initialLaw setup) horizon scheduler before next.state joint realized
    have beforeOrdered : before.execution.application.config.cut.IsPrefix rank := by
      rw [configEq]
      exact ordered
    by_cases clearNext : Clear next.state
    · have empty : after.execution.application.config.defaulted = ∅ :=
        by simpa only [afterState, ReactiveApplication.stateInvariant] using clearNext
      rcases reactive_protocol_config_eq_or_step_of_clear runtime leaks (initialLaw setup)
          horizon scheduler before after joint (afterState ▸ realized) empty with
        same | ⟨event, ready, action, supported⟩
      · exact Or.inr ⟨after, afterState, same.trans configEq⟩
      · have lower : rank ≤ event.val := Nat.le_of_not_gt fun earlier =>
          ready.1 ((beforeOrdered.2 event).mpr earlier)
        have bound : rank < (graph setup).order.eventCount := lt_of_le_of_lt lower event.isLt
        have same := setup.eventGraph.sequentialize_ready_unique _ ready (beforeOrdered.ready bound)
        have rankEq : event.val = rank := congrArg Fin.val same
        refine Or.inl (Or.inl ⟨after, afterState, event, ?_, rankEq⟩)
        rw [EventGraph.Config.step, PMF.support_map] at supported
        obtain ⟨value, _chosen, actual⟩ := supported
        rw [← actual]
        exact (EventOrder.Cut.mem_complete _ event ready event).mpr (Or.inl rfl)
    · exact Or.inl (Or.inr clearNext)
  suffices splitting : ∀ history, inside history →
      (N).runBehavioralUntil certificate players stopped history =
        ((N).runBehavioralUntil certificate players phase history).bind
          ((N).runBehavioralUntil certificate players stopped) from
    splitting start (Or.inr ⟨control, current, rfl⟩)
  intro history
  induction history using certificate.induction with
  | _ history ih =>
  intro holds
  by_cases halted : phase history
  · rw [(N).runBehavioralUntil_of_stopped certificate players halted, PMF.pure_bind]
  by_cases ended : (NP).terminal history.state
  · rw [(N).runBehavioralUntil_of_terminal certificate players ended,
      (N).runBehavioralUntil_of_terminal certificate players ended, PMF.pure_bind,
      (N).runBehavioralUntil_of_terminal certificate players ended]
  rw [(N).runBehavioralUntil_of_running certificate players (safe history holds halted) ended,
    (N).runBehavioralUntil_of_running certificate players halted ended, PMF.bind_bind]
  apply bind_congr_on_support
  intro next member
  exact ih next ((N).mem_support_runBehavioralFrom_one players ended member).1
    (preserve history next holds halted ended member)

theorem runUntil_after_localLaw_eq
    (certificate : (NP).WellFoundedHistories) (actsOnce : (N).ActsOnceWhereItMatters)
    (players : ∀ who, (N).BehavioralPolicy who) (who : Player)
    [DecidableEq ((N).InfoState who)] (info : (N).InfoState who)
    (law : PMF ((N).Choice who info)) (phase stopped : (NP).History → Prop)
    (history : (NP).History) (observed : (N).infoOf who history.trace = info)
    (active : (NP).active history.state who) (running : ¬ (NP).terminal history.state)
    (going : ¬ phase history)
    (final : (NP).History)
    (member : final ∈ ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) players who
        ((players who).withLaw info law)) phase history).support) :
    (N).runBehavioralUntil certificate
        (Profile.update (sig := (N).behavioralSignature) players who
          ((players who).withLaw info law)) stopped final =
      (N).runBehavioralUntil certificate players stopped final := by
  classical
  rw [(N).runBehavioralUntil_of_running certificate _ going running,
    PMF.mem_support_bind_iff] at member
  obtain ⟨next, nextMember, reached⟩ := member
  have reachesFinal := historyReaches_of_mem_runBehavioralUntil (N) certificate _ phase next
    final reached
  rw [(N).runBehavioralFrom_succ_of_not_terminal _ 0 running,
    PMF.mem_support_bind_iff] at nextMember
  obtain ⟨draw, _, stepped⟩ := nextMember
  rw [PMF.mem_support_bindOnSupport_iff] at stepped
  obtain ⟨target, realized, nextEq⟩ := stepped
  change next ∈ (PMF.pure _).support at nextEq
  rw [PMF.mem_support_pure_iff] at nextEq
  subst nextEq
  refine (N).runBehavioralUntil_congr certificate stopped final fun later reaches nonterminal
    player => ?_
  by_cases same : player = who
  · subst player
    rw [Profile.update_same]
    obtain ⟨choice, _⟩ := law.support_nonempty
    obtain ⟨_firstFuel, firstReach⟩ := reachesFinal
    obtain ⟨_secondFuel, secondReach⟩ := reaches
    have within := firstReach.trans secondReach
    have first := (N).withLaw_eq_commit_after_actsOnce actsOnce (players who) info law choice
      observed active draw.2 realized later within nonterminal
    have second := (N).withLaw_eq_commit_after_actsOnce actsOnce (players who) info
      (players who info) choice observed active draw.2 realized later within nonterminal
    rw [BehavioralPolicy.withLaw_eq_self] at second
    exact first.trans second.symm
  · rw [Profile.update_of_ne _ _ same]

end Vegas.OnePacketComparison
