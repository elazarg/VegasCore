/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SourceDebtContinuation
import Vegas.Game.NativeExitContinuation
import Vegas.Game.OnePacketComponents
import Vegas.Game.OnePacketLateCertificate
import Vegas.Game.OnePacketForeignFailureBound
import Vegas.Game.RecoveryIrregularBeliefBounds
import GameTheoryExtensions.Analysis.Protocol.StoppedTerminalBound
import GameTheoryExtensions.Math.Probability.ExpectationContraction
import GameTheory.Math.Probability.Bounds

/-! # Native terminal values and stopping before own source debt

Stopping at the first public default or latent own failure changes the focal
payoff only when another player defaults before the focal player owes a failure.
The continuation uses the supplied native runtime's all-history completion.
-/

noncomputable section

namespace Vegas.OnePacketComparison

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (runtime : EventGraphRuntime (graph setup))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (application setup runtime leaks).Scheduler)

local notation "Menu" => bounds.onePacketMenu runtime leaks
local notation "N" => onePacketModel setup runtime leaks bounds (initialLaw setup) horizon scheduler
local notation "E" => ReactiveApplication.ResponseMenu.protocol
  (bounds.onePacketMenu runtime leaks) (initialLaw setup) horizon scheduler
local notation "Clear" => ReactiveApplication.stateInvariant
  (app := application setup runtime leaks)
    (fun native : EventGraphRuntime.State (graph setup) =>
      EventGraph.Config.defaulted (EventGraphRuntime.State.config native) = ∅)

variable {Parameter : Type} (parameter : State L setup.context → Parameter)
  (utility : Parameter × PublicOutcome setup.program → Player → ℝ)
  (excludedPayoff : Player → ℝ)

open Classical in
/-- Replacing the continuation at public default or own latent debt by the
declared exit value charges only foreign defaults before own debt. -/
theorem terminal_value_sub_stopped_le_foreign_default
    (completes : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    (certificate : (E).WellFoundedHistories)
    (players : ∀ who, (N).BehavioralPolicy who) (who : Player)
    {payoffBound : ℝ} (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ final : (E).History,
      |exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who| ≤
        payoffBound)
    (excludedBounded : |excludedPayoff who| ≤ payoffBound) (start : (E).History) :
    let stopped := fun final : (E).History => ¬ Clear final.state ∨
      DecodedState setup runtime leaks (failureProfile setup.program)
        (ProtocolState.OwesFailure who setup.program) final.state
    let law := (N).runBehavioralUntil certificate players stopped start
    |expect ((N).runBehavioralTerminalFrom certificate players start)
        (fun final => exclusionBase setup runtime parameter utility excludedPayoff leaks
          final.state who) -
      expect law (fun final => if stopped final then excludedPayoff who else
        exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who)| ≤
      (2 * payoffBound) * (law.toOuterMeasure {final |
        ¬ Clear final.state ∧
        (∀ current, final.state = some current →
          who ∉ current.execution.application.config.defaulted) ∧
        ¬ DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state}).toReal := by
  intro stopped law
  let payoff := fun final : (E).History =>
    exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
  let continued := fun final : (E).History =>
    expect ((N).runBehavioralTerminalFrom certificate players final) payoff
  let value := fun final => if stopped final then excludedPayoff who else payoff final
  let foreign := {final : (E).History |
    ¬ Clear final.state ∧
    (∀ current, final.state = some current →
      who ∉ current.execution.application.config.defaulted) ∧
    ¬ DecodedState setup runtime leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure who setup.program) final.state}
  have continuedBounded (final) : |continued final| ≤ payoffBound :=
    expect_abs_le_of_bounded nonnegative payoffBounded
  have valueBounded (final) : |value final| ≤ payoffBound := by
    dsimp only [value]
    split
    · exact excludedBounded
    · exact payoffBounded final
  have continuedIntegrable : PayoffIntegrable law continued :=
    payoffIntegrable_of_bounded _ _ continuedBounded
  have valueIntegrable : PayoffIntegrable law value :=
    payoffIntegrable_of_bounded _ _ valueBounded
  have outside : ∀ final ∈ law.support, final ∉ foreign →
      continued final = value final := by
    intro final supported notForeign
    by_cases halted : stopped final
    · change continued final = if stopped final then excludedPayoff who else payoff final
      rw [ite_eq_left halted]
      by_cases owed : DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state
      · exact (exclusionBase_expect_of_owesFailure parameter utility excludedPayoff (Menu)
          horizon scheduler completes certificate players who final owed).2
      have unclear : ¬ Clear final.state := halted.resolve_right owed
      have own : ∃ current, final.state = some current ∧
          who ∈ current.execution.application.config.defaulted := by
        by_contra missing
        apply notForeign
        refine ⟨unclear, ?_, owed⟩
        intro current same member
        exact missing ⟨current, same, member⟩
      obtain ⟨current, same, member⟩ := own
      exact (exclusionBase_expect_of_defaulted parameter utility excludedPayoff (Menu)
        (initialLaw setup) horizon scheduler certificate players final current same who member).2
    · have ended := ((N).mem_support_runBehavioralUntil certificate players stopped start final
        supported).resolve_left halted
      change continued final = if stopped final then excludedPayoff who else payoff final
      rw [ite_eq_right halted]
      dsimp only [continued]
      rw [InformationModel.runBehavioralTerminalFrom,
        (E).randomizedBackwardLaw_of_terminal (history := final) ended, expect_pure]
  have upper := expect_le_add_event_gap law foreign value continued (2 * payoffBound)
    valueIntegrable continuedIntegrable
    (fun final supported outsideEvent => (outside final supported outsideEvent).le)
    (fun final _ _ => by
      linarith [(abs_le.mp (continuedBounded final)).2, (abs_le.mp (valueBounded final)).1])
  have lower := expect_le_add_event_gap law foreign continued value (2 * payoffBound)
    continuedIntegrable valueIntegrable
    (fun final supported outsideEvent => (outside final supported outsideEvent).symm.le)
    (fun final _ _ => by
      linarith [(abs_le.mp (valueBounded final)).2, (abs_le.mp (continuedBounded final)).1])
  have decomposition :
      expect ((N).runBehavioralTerminalFrom certificate players start) payoff =
        expect law continued := by
    rw [(N).runBehavioralTerminalFrom_eq_bind_runBehavioralUntil certificate players stopped start]
    exact expect_bind_tower law ((N).runBehavioralTerminalFrom certificate players) payoff
      (payoffIntegrable_of_bounded _ payoff payoffBounded)
  change |expect ((N).runBehavioralTerminalFrom certificate players start) payoff -
    expect law value| ≤ (2 * payoffBound) * (law.toOuterMeasure foreign).toReal
  rw [decomposition]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

section Assembled

variable [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [Finite setup.intendedProtocol.History]
  {Public : Type*} {signal : State L setup.context → Public}

local instance stoppedComparisonHistoryFintype : Fintype (E).History :=
  (Menu).historyFintype (initialLaw setup) horizon scheduler

open Classical in
/-- On the supplied native assessments, every local law has the same uniform
vanishing terminal-versus-stopped value error. The gain error is twice this
value error. All continuations retain the supplied assembled weights. -/
theorem assembled_terminal_stopped_comparison_bounds
    [∀ who, DecidableEq ((N).InfoState who)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependentGiven signal)
    (observable : setup.PublicInitialSignal signal)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup runtime leaks bounds horizon scheduler (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds (initialLaw setup)
      horizon scheduler bounds.candidateCount p))
    (targetSequence : ℕ → (N).BehavioralAssessment)
    (assembled : OnePacketAssembled setup runtime leaks bounds horizon scheduler sequence scale
      positive le_one weights targetSequence)
    (mixed : ∀ n, (targetSequence n).IsFullyMixed)
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (N) (targetSequence n)
      ((Menu).decisionRecall (initialLaw setup) horizon scheduler).decisionInformationAntichain)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Opportunity runtime leaks (initialLaw setup) horizon scheduler delay)
    (inclusion : ProtectedInclusion runtime leaks (initialLaw setup) horizon scheduler bound)
    (timely : runtime.AsyncTimely delay bound)
    (completes : CompletesPlay runtime leaks (initialLaw setup) horizon scheduler)
    {payoffBound : ℝ} (nonnegative : 0 ≤ payoffBound)
    (payoffBounded : ∀ who (final : (E).History),
      |exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who| ≤
        payoffBound)
    (excludedBounded : ∀ who, |excludedPayoff who| ≤ payoffBound) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (N).InformationSite who),
        ¬ Vegas.FreeAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ¬ Vegas.OwingAgent setup runtime leaks bounds (initialLaw setup) horizon scheduler
          ((N).agentAt site) →
        ∀ {past : List (application setup runtime leaks).PlayerEntry}
          {view : (application setup runtime leaks).PlayerView}, site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
          view.application.publicView.ownTurn? who = some event →
        let common := (targetSequence n).strategy
        let certificate :=
          ((Menu).bounded (initialLaw setup) horizon scheduler).wellFoundedHistories
        let stopped := fun final : (E).History => ¬ Clear final.state ∨
          DecodedState setup runtime leaks (failureProfile setup.program)
            (ProtocolState.OwesFailure who setup.program) final.state
        let payoff := fun final : (E).History => if stopped final then excludedPayoff who else
          exclusionBase setup runtime parameter utility excludedPayoff leaks final.state who
        (∀ law : PMF ((N).Choice who site.1),
          |localValue (2 * horizon + 1) (fun final => final.state)
              (exclusionBase setup runtime parameter utility excludedPayoff leaks)
                (targetSequence n) site law -
            expect ((targetSequence n).belief who site) (fun history =>
              expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw site.1 law)) stopped history.1) payoff)| ≤ error n) ∧
        ∀ law : PMF ((N).Choice who site.1),
          |localGain (2 * horizon + 1) (fun final => final.state)
              (exclusionBase setup runtime parameter utility excludedPayoff leaks)
                (targetSequence n) site law -
            expect ((targetSequence n).belief who site) (fun history =>
              expect ((N).runBehavioralUntil certificate
                (Profile.update (sig := (N).behavioralSignature) common who
                  ((common who).withLaw site.1 law)) stopped history.1) payoff -
                expect ((N).runBehavioralUntil certificate common stopped history.1) payoff)| ≤
            2 * error n := by
  obtain ⟨drift, driftLimit, irregular⟩ := irregular_belief_bounds_of_assembled setup runtime leaks
    bounds horizon scheduler wellFormed independent observable sequence sourceMixed scale positive
    le_one scaleEq covers coversInputs capacity weights targetSequence assembled mixed bayes
  let cost := fun n => (scale n ^ 2 + scale n) * (2 * horizon + 1)
  let error := fun n => 2 * payoffBound * (|drift n| + cost n)
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    have identity : scale = fun n => trembleScale
        (combinedFloor setup runtime leaks bounds horizon scheduler (sequence n))
        (2 * horizon + 2) n := funext scaleEq
    rw [identity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup runtime leaks bounds horizon scheduler (sequence n))
      (fun n => combinedFloor_le_one setup runtime leaks bounds horizon scheduler (sequence n))
  have costLimit : Tendsto cost atTop (nhds 0) := by
    simpa [cost] using ((scaleLimit.pow 2).add scaleLimit).mul_const (2 * horizon + 1 : ℝ)
  refine ⟨error, ?_, ?_⟩
  · simpa [error] using (driftLimit.abs.add costLimit).const_mul (2 * payoffBound)
  intro n who site notFree notOwing past view atSite event turn common certificate stopped payoff
  let belief := (targetSequence n).belief who site
  let bad := fun history : (N).InformationHistory who site.1 =>
    if RegularTrace setup runtime leaks bounds horizon scheduler (sequence n) who
      history.1.trace then (0 : ℝ) else 1
  let terminalValue := fun (law : PMF ((N).Choice who site.1))
      (history : (N).InformationHistory who site.1) =>
    expect ((N).runBehavioralTerminalFrom certificate
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw site.1 law)) history.1)
      (fun final => exclusionBase setup runtime parameter utility excludedPayoff leaks
        final.state who)
  let stoppedValue := fun (law : PMF ((N).Choice who site.1))
      (history : (N).InformationHistory who site.1) =>
    expect ((N).runBehavioralUntil certificate
      (Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw site.1 law)) stopped history.1) payoff
  have payoffBoundedStop : ∀ final, |payoff final| ≤ payoffBound := by
    intro final
    dsimp only [payoff]
    split
    · exact excludedBounded who
    · exact payoffBounded who final
  have rowBound : ∀ (law : PMF ((N).Choice who site.1))
      (history : (N).InformationHistory who site.1),
      |terminalValue law history - stoppedValue law history| ≤
        2 * payoffBound * (bad history + cost n) := by
    intro law history
    have costNonnegative : 0 ≤ cost n :=
      mul_nonneg (add_nonneg (sq_nonneg _) (positive n).le) (by positivity)
    by_cases regular : RegularTrace setup runtime leaks bounds horizon scheduler (sequence n)
        who history.1.trace
    · simp only [bad, regular, ↓reduceIte, zero_add]
      rcases history with ⟨⟨state, trace⟩, observed⟩
      obtain ⟨remaining, execution, current, recallEq, observeEq⟩ :=
        state_of_site setup runtime leaks bounds horizon scheduler atSite ⟨⟨state, trace⟩, observed⟩
      dsimp only at current
      subst state
      have clear : execution.application.config.defaulted = ∅ :=
        runtime.informationHistory_clear leaks (Menu) (initialLaw setup) horizon scheduler site
          (Classical.not_not.mp notFree).1 ⟨⟨_, trace⟩, observed⟩ _ rfl
      have nativeTurn : execution.application.publicView.ownTurn? who = some event := by
        change (execution.observe (application setup runtime leaks)
          who).application.publicView.ownTurn? who = some event
        rw [observeEq]
        exact turn
      let installed := Profile.update (sig := (N).behavioralSignature) common who
        ((common who).withLaw site.1 law)
      let kernel := (N).runBehavioralUntil certificate installed stopped ⟨_, trace⟩
      let foreign := {final : (E).History |
        ¬ Clear final.state ∧
        (∀ control, final.state = some control →
          who ∉ control.execution.application.config.defaulted) ∧
        ¬ DecodedState setup runtime leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure who setup.program) final.state}
      have foreignMass := assembled_foreign_exit_mass_le_rank setup runtime leaks bounds horizon
        scheduler wellFormed covers capacity sequence scale positive le_one weights targetSequence
        assembled n who ((common who).withLaw site.1 law)
        (fun control prior _ => opportunity control ((Menu).toRawTrace (initialLaw setup) horizon
          scheduler prior))
        (fun control prior _ => inclusion control ((Menu).toRawTrace (initialLaw setup) horizon
          scheduler prior)) timely certificate (fun _ => False) ⟨remaining, some who, execution⟩
        trace event nativeTurn clear regular
      simp only [or_false] at foreignMass
      have subset : foreign ⊆ {final : (E).History | ¬ Clear final.state ∧
          (∀ control, final.state = some control →
            who ∉ control.execution.application.config.defaulted)} :=
        fun _ holds => ⟨holds.1, holds.2.1⟩
      have mass : (kernel.toOuterMeasure foreign).toReal ≤
          (scale n ^ 2 + scale n) *
            (application setup runtime leaks).rank horizon (some ⟨remaining, some who, execution⟩)
            := by
        refine (ENNReal.toReal_mono (outerMeasure_ne_top _ _)
          (MeasureTheory.measure_mono subset)).trans ?_
        exact foreignMass
      have depth := (application setup runtime leaks).trace_bound (initialLaw setup) horizon
        scheduler ((Menu).toRawTrace (initialLaw setup) horizon scheduler trace)
      have rankBound : ((application setup runtime leaks).rank horizon
          (some ⟨remaining, some who, execution⟩) : ℝ) ≤ 2 * horizon + 1 := by
        exact_mod_cast (show (application setup runtime leaks).rank horizon
          (some ⟨remaining, some who, execution⟩) ≤ 2 * horizon + 1 by omega)
      have massCost : (kernel.toOuterMeasure foreign).toReal ≤ cost n :=
        mass.trans (mul_le_mul_of_nonneg_left rankBound
          (add_nonneg (sq_nonneg _) (positive n).le))
      have pointwise := terminal_value_sub_stopped_le_foreign_default setup runtime leaks bounds
        horizon scheduler parameter utility excludedPayoff completes certificate installed who
        nonnegative (payoffBounded who) (excludedBounded who) ⟨_, trace⟩
      exact pointwise.trans (mul_le_mul_of_nonneg_left massCost (by positivity))
    · simp only [bad, regular, ↓reduceIte]
      have first : |terminalValue law history| ≤ payoffBound :=
        expect_abs_le_of_bounded nonnegative (payoffBounded who)
      have second : |stoppedValue law history| ≤ payoffBound :=
        expect_abs_le_of_bounded nonnegative payoffBoundedStop
      have gap := (abs_sub (terminalValue law history) (stoppedValue law history)).trans
        (add_le_add first second)
      nlinarith
  have values : ∀ law : PMF ((N).Choice who site.1),
      |localValue (2 * horizon + 1) (fun final => final.state)
          (exclusionBase setup runtime parameter utility excludedPayoff leaks)
            (targetSequence n) site law - expect belief (stoppedValue law)| ≤ error n := by
    intro law
    have actual : localValue (2 * horizon + 1) (fun final => final.state)
        (exclusionBase setup runtime parameter utility excludedPayoff leaks)
          (targetSequence n) site law = expect belief (terminalValue law) := by
      rw [localValue_eq_continuationContext (2 * horizon + 1) (fun final => final.state)
        (exclusionBase setup runtime parameter utility excludedPayoff leaks) (targetSequence n)
        site ((Menu).bounded (initialLaw setup) horizon scheduler),
        BehavioralAssessment.continuationContext_value, expect_bind_of_finite]
    rw [actual]
    have averaged := expect_mono (μ := belief) (fun history _ => rowBound law history)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    rw [expect_const_mul,
      expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_constant _ _),
      expect_constant] at averaged
    have irregularMass : expect belief bad ≤ |drift n| :=
      (irregular n who site notFree notOwing atSite turn).trans (le_abs_self _)
    have near := abs_expect_sub_le_expect_abs_sub belief (terminalValue law) (stoppedValue law)
      (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)
    exact near.trans (averaged.trans (mul_le_mul_of_nonneg_left
      (add_le_add irregularMass (le_refl (cost n))) (by positivity)))
  refine ⟨values, ?_⟩
  intro law
  have alternativeNear := values law
  have prescribedNear := values (common who site.1)
  dsimp only [stoppedValue] at alternativeNear prescribedNear
  simp only [BehavioralPolicy.withLaw_eq_self, Profile.update_eq_self] at prescribedNear
  rw [localGain_eq_sub, expect_sub (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)]
  exact abs_le.mpr ⟨by linarith [(abs_le.mp alternativeNear).1,
    (abs_le.mp prescribedNear).2], by linarith [(abs_le.mp alternativeNear).2,
      (abs_le.mp prescribedNear).1]⟩

end Assembled

end Vegas.OnePacketComparison
