/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RecoveryIrregularBeliefBounds
import Vegas.Game.RecoveryBeliefContinuation

/-! # Uniform foreign-exit bounds under the actual recovery posterior -/

noncomputable section

namespace Vegas.RecoveryOnePacket

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction EventGraphRuntime
  RecoveryProjection Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
  (bounds : MessageBounds (graph setup)) (horizon : Nat)
  (scheduler : (recoveryApplication (runtime setup) leaks).Scheduler)

local notation "Initial" => PMF.map
  (fun native => (RecoveryState.mk native ∅ : RecoveryState (graph setup))) (initialLaw setup)
local notation "NativeScheduler" => nativeScheduler (runtime setup) leaks scheduler
local notation "R" => model setup leaks bounds Initial horizon scheduler
local notation "N" => onePacketModel setup leaks bounds (initialLaw setup) horizon (NativeScheduler)
local notation "RP" => ReactiveApplication.ResponseMenu.protocol
  (Recovery.onePacketMenu (runtime setup) leaks bounds) Initial horizon scheduler
local notation "RApp" => recoveryApplication (runtime setup) leaks
local notation "RawNative" => ReactiveApplication.protocol (application setup leaks)
  (PMF.map RecoveryState.native (Initial)) horizon (NativeScheduler)
local notation "ClearState" => ReactiveApplication.stateInvariant
  (app := application setup leaks) (fun native => PublicExclusionRecord (RecoveryState.mk native ∅))
local notation "RMenu" => Recovery.onePacketMenu (runtime setup) leaks bounds
local notation "NMenu" => bounds.onePacketMenu (runtime setup) leaks


open Classical in
/-- The full posterior fiber at a nonfree recovery site consists of actual
controlled prefixes whose permanent excluded set is empty. -/
theorem belief_controlled_clear_of_notFree [Fintype (RP).History]
    [∀ player, DecidableEq ((R).InfoState player)]
    (assessment : (R).BehavioralAssessment) {who : Player} (site : (R).InformationSite who)
    (notFree : ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site)) :
    ∀ history ∈ ((assessment.belief who site).map Subtype.val).support,
      ∃ current : (recoveryApplication (runtime setup) leaks).Control,
        history.state = some current ∧ current.execution.application.excluded = ∅ := by
  intro history member
  obtain ⟨found, _supported, rfl⟩ := PMF.support_map .. ▸ member
  have active := InformationSite.active (R) site found
  obtain ⟨current, state, actor⟩ := (recoveryApplication (runtime setup) leaks).control_of_active
    Initial horizon scheduler ((RMenu).toRawHistory Initial horizon scheduler found.1) who active
  change found.1.state = some current at state
  have observed := ((RMenu).info Initial horizon scheduler who found.1.trace).symm.trans found.2
  rw [state] at observed
  simp only [ReactiveApplication.observe, actor, ↓reduceIte] at observed
  refine ⟨current, state, ?_⟩
  by_contra nonempty
  have forced : ForcedAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) :=
    Classical.not_not.mp notFree
  exact not_clearInput_of_publicExclusion setup leaks
    ⟨current.execution.recall who, current.execution.observe (RApp) who, observed.symm, nonempty⟩
      forced.1

private theorem control_turn_of_information {who : Player}
    {past : List (recoveryApplication (runtime setup) leaks).PlayerEntry}
    {view : (recoveryApplication (runtime setup) leaks).PlayerView}
    (history : (R).InformationHistory who (some (past, view)))
    {event : (graph setup).EventId}
    (turn : view.application.1.publicView.ownTurn? who = some event) :
    ∃ current : (recoveryApplication (runtime setup) leaks).Control,
      history.1.state = some current ∧
        current.execution.application.native.publicView.ownTurn? who = some event := by
  have observed := ((RMenu).info Initial horizon scheduler who history.1.trace).symm.trans history.2
  cases state : history.1.state with
  | none => rw [state] at observed; cases observed
  | some current =>
    rw [state] at observed
    by_cases active : current.actor = some who
    · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
      have viewEq : current.execution.observe (RApp) who = view :=
        congrArg Prod.snd (Option.some.inj observed)
      refine ⟨current, rfl, ?_⟩
      exact (congrArg (fun observed : (RApp).PlayerView =>
        observed.application.1.publicView.ownTurn? who) viewEq).trans turn
    · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
      cases observed

private theorem debtStoppedLaw_foreign_mass_le_rank [Fintype (RP).History]
    [(recoveryApplication (runtime setup) leaks).FiniteNature Initial scheduler]
    [∀ who, DecidableEq ((R).InfoState who)]
    (wellFormed : setup.WellFormed) (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (Part setup leaks bounds Initial horizon scheduler slots p))
    (n : ℕ) (fallback : ∀ who, (R).Policy who)
    (strategy : ∀ who, (R).BehavioralPolicy who)
    (assembled : strategy = (R).agentBehavior (R).playedInformation fallback
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (focal : Player) (alternative : (R).BehavioralPolicy focal)
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate : (onePacketProtocol setup leaks bounds horizon
      (NativeScheduler)).WellFoundedHistories)
    (rawCertificate : ((application setup leaks).protocol ((Initial).map RecoveryState.native)
      horizon (NativeScheduler)).WellFoundedHistories)
    (history : (RP).History)
    (clear : ∀ current, history.state = some current →
      current.execution.application.excluded = ∅)
    (current : (recoveryApplication (runtime setup) leaks).Control)
    (state : history.state = some current)
    (event : (graph setup).EventId)
    (turn : current.execution.application.native.publicView.ownTurn? focal = some event)
    (regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) focal
      (nativeClearHistory setup leaks bounds horizon scheduler history clear).trace) :
    ((nativeDebtStoppedLaw setup leaks bounds horizon scheduler rawCertificate
      (Profile.update (sig := (R).behavioralSignature) strategy focal alternative) focal
        history).toOuterMeasure
        {label | ForeignExclusionLabel focal label}).toReal ≤
      ((scale n) ^ 2 + scale n) * (application setup leaks).rank horizon
        (protocolState (runtime setup) leaks history.state) := by
  classical
  let updated := Profile.update (sig := (R).behavioralSignature) strategy focal alternative
  let native := (application setup leaks).information ((Initial).map RecoveryState.native)
    horizon (NativeScheduler)
  let nativePlayers := nativeProfile (runtime setup) leaks Initial horizon scheduler
    (fun who => (RMenu).embedPolicy Initial horizon scheduler who (updated who))
  let nativeStart := nativeHistory (runtime setup) leaks Initial horizon scheduler
    ((RMenu).toRawHistory Initial horizon scheduler history) clear
  let stop := fun final : (RawNative).History => ¬ ClearState final.state ∨
    DecodedState setup leaks (failureProfile setup.program)
      (ProtocolState.OwesFailure focal setup.program) final.state
  let exits := {final : (RawNative).History | ¬ ClearState final.state ∧
    focal ∉ nativeFailureOwners (runtime setup) leaks final.state}
  let law := native.runBehavioralUntil rawCertificate nativePlayers stop nativeStart
  have clearIff (final : (RawNative).History) :
      NativeClear (runtime setup) leaks Initial horizon scheduler final ↔
        ClearState final.state := by
    unfold NativeClear
    cases state : final.state with
    | none => simp [ReactiveApplication.stateInvariant]
    | some control =>
      constructor
      · intro valid
        exact valid control rfl
      · intro valid found same
        cases Option.some.inj same
        exact valid
  have stopEq : (fun final : (RawNative).History =>
      ¬ NativeClear (runtime setup) leaks Initial horizon scheduler final ∨
        DecodedState setup leaks (failureProfile setup.program)
          (ProtocolState.OwesFailure focal setup.program) final.state) = stop := by
    funext final
    exact propext (or_congr (not_congr (clearIff final)) Iff.rfl)
  have lawEq : nativeDebtStoppedLaw setup leaks bounds horizon scheduler rawCertificate updated
      focal history = law.map (nativeClassifiedReadout (runtime setup) leaks Initial horizon
        scheduler) := by
    unfold nativeDebtStoppedLaw
    rw [dite_eq_left clear]
    exact congrArg (fun stop =>
      (native.runBehavioralUntil rawCertificate nativePlayers stop nativeStart).map
        (nativeClassifiedReadout (runtime setup) leaks Initial horizon scheduler)) stopEq
  have eventEq : (nativeClassifiedReadout (runtime setup) leaks Initial horizon scheduler) ⁻¹'
      {label | ForeignExclusionLabel focal label} = exits := by
    ext final
    by_cases valid : NativeClear (runtime setup) leaks Initial horizon scheduler final
    · have invariant := (clearIff final).mp valid
      simp [nativeClassifiedReadout, valid, ForeignExclusionLabel, exits, invariant]
    · have invariant : ¬ ClearState final.state := fun found => valid ((clearIff final).mpr found)
      simp [nativeClassifiedReadout, valid, ForeignExclusionLabel, exits, invariant]
  have massBound := projected_foreign_exit_mass_le_rank setup leaks bounds horizon scheduler
    wellFormed covers capacity sequence scale positive le_one weights n fallback strategy assembled
      focal alternative opportunity inclusion timely certificate rawCertificate history clear
        current state event turn regular
  change (law.toOuterMeasure exits).toReal ≤ _ at massBound
  calc
    _ = ((law.map (nativeClassifiedReadout (runtime setup) leaks Initial
        horizon scheduler)).toOuterMeasure
        {label | ForeignExclusionLabel focal label}).toReal :=
      congrArg (fun probability : PMF (Finset Player ⊕ (RawNative).History) =>
        (probability.toOuterMeasure {label | ForeignExclusionLabel focal label}).toReal) lawEq
    _ = (law.toOuterMeasure exits).toReal := by
      rw [PMF.toOuterMeasure_map_apply, eventEq]
    _ ≤ _ := massBound


open Classical in
/-- The original common recovery assessment assigns uniformly vanishing mass
to foreign first exits of its actual projected debt-stopped continuation, under
any focal recovery policy. Past irregularity is controlled by concrete directed
counterparts, and future exceptional responses by the protocol depth. -/
theorem recovery_common_foreign_exit_bounds [Fintype (RP).History]
    [(recoveryApplication (runtime setup) leaks).FiniteNature Initial scheduler]
    [Finite setup.intendedProtocol.History]
    [∀ player, DecidableEq ((R).InfoState player)]
    (wellFormed : setup.WellFormed) (independent : setup.PrivateInputsIndependent)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (sourceMixed : ∀ n, (sequence n).IsFullyMixed)
    (scale : ℕ → ℝ) (positive : ∀ n, 0 < scale n) (le_one : ∀ n, scale n ≤ 1)
    (scaleEq : ∀ n, scale n = trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
      (2 * horizon + 2) n)
    (covers : bounds.CoversOutputValues) (coversInputs : bounds.CoversInputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    (weights : ℕ → ∀ p,
      PMF (Part setup leaks bounds Initial horizon scheduler bounds.candidateCount p))
    (assessments : ℕ → (R).BehavioralAssessment)
    (fallback : ℕ → ∀ player, (R).Policy player)
    (assembled : ∀ n, (assessments n).strategy = (R).agentBehavior (R).playedInformation
      (fallback n)
      (fun agent => (weights n (pool setup leaks bounds Initial horizon scheduler agent)).bind
        (component setup leaks bounds Initial horizon scheduler (sequence n) (scale n)
          (positive n).le (le_one n) agent)))
    (bayes : ∀ n, BehavioralAssessment.IsBayesConsistent (R) (assessments n)
      ((RMenu).decisionInformationAntichain Initial horizon scheduler))
    {delay bound : (graph setup).EventId → Nat}
    (opportunity : Recovery.Opportunity (runtime setup) leaks Initial horizon scheduler delay)
    (inclusion : Recovery.ProtectedInclusion (runtime setup) leaks Initial horizon scheduler bound)
    (timely : (runtime setup).AsyncTimely delay bound)
    (certificate : ((NMenu).protocol (initialLaw setup) horizon
      (NativeScheduler)).WellFoundedHistories)
    (rawCertificate : (RawNative).WellFoundedHistories) :
    ∃ error : ℕ → ℝ, Tendsto error atTop (nhds 0) ∧
      ∀ n who (site : (R).InformationSite who),
        ¬ FreeAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ¬ OwingAgent setup leaks bounds Initial horizon scheduler ((R).agentAt site) →
        ∀ {past : List (recoveryApplication (runtime setup) leaks).PlayerEntry}
          {view : (recoveryApplication (runtime setup) leaks).PlayerView},
        site.1 = some (past, view) →
        ∀ {event : (graph setup).EventId},
        view.application.1.publicView.ownTurn? who = some event →
        ∀ alternative : (R).BehavioralPolicy who,
        (((((assessments n).belief who site).map Subtype.val).bind
          (nativeDebtStoppedLaw setup leaks bounds horizon scheduler rawCertificate
            (Profile.update (sig := (R).behavioralSignature) (assessments n).strategy who
              alternative)
            who)).toOuterMeasure {label | ForeignExclusionLabel who label}).toReal ≤ error n := by
  classical
  obtain ⟨drift, driftLimit, irregular⟩ := recovery_irregular_belief_bounds setup leaks bounds
    horizon scheduler wellFormed independent sequence sourceMixed scale positive le_one scaleEq
      covers coversInputs capacity weights assessments fallback assembled bayes
  have scaleIdentity : scale = (fun n => trembleScale
      (combinedFloor setup leaks bounds horizon (NativeScheduler) (sequence n))
        (2 * horizon + 2) n) := funext scaleEq
  have scaleLimit : Tendsto scale atTop (nhds 0) := by
    rw [scaleIdentity]
    exact tendsto_trembleScale _
      (fun n => combinedFloor_pos setup leaks bounds horizon (NativeScheduler) (sequence n))
      (fun n => combinedFloor_le_one setup leaks bounds horizon (NativeScheduler) (sequence n))
  have deltaLimit : Tendsto (fun n => (scale n) ^ 2 + scale n) atTop (nhds 0) := by
    simpa using (scaleLimit.pow 2).add scaleLimit
  let error := fun n => drift n + ((scale n) ^ 2 + scale n) * (2 * horizon + 1)
  refine ⟨error, ?_, ?_⟩
  · simpa only [error, zero_mul, add_zero] using
      driftLimit.add (deltaLimit.mul_const (2 * (horizon : ℝ) + 1))
  intro n who site notFree notOwing past view atSite event turn alternative
  obtain ⟨nativeSite, project, _nativeInput, projection, states, _law, irregularMass⟩ :=
    irregular n who site notFree notOwing atSite turn
  let posterior := (assessments n).belief who site
  let updated := Profile.update (sig := (R).behavioralSignature) (assessments n).strategy who
    alternative
  let kernel := nativeDebtStoppedLaw setup leaks bounds horizon scheduler rawCertificate updated who
  let exits := {label : Finset Player ⊕ (RawNative).History | ForeignExclusionLabel who label}
  let indicator := fun label => @ite ℝ (label ∈ exits) (Classical.propDecidable _) 1 0
  let forget := fun history : (R).InformationHistory who site.1 => (project history).1
  let bad := {history : ((NMenu).protocol (initialLaw setup) horizon (NativeScheduler)).History |
    ¬ RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who history.trace}
  let badIndicator := fun history => @ite ℝ (history ∈ bad) (Classical.propDecidable _) 1 0
  let badPayoff := badIndicator ∘ forget
  let future := fun history : (R).InformationHistory who site.1 =>
    expect (kernel history.1) indicator
  let cost := ((scale n) ^ 2 + scale n) * (2 * horizon + 1)
  let clear := fun history : (R).InformationHistory who site.1 => (projection history).choose
  have indicatorBounded : ∀ label, |indicator label| ≤ 1 := by
    intro label
    dsimp only [indicator]
    split <;> norm_num
  have futureBounded : ∀ history, |future history| ≤ 1 :=
    fun _ => expect_abs_le_of_bounded (by norm_num) indicatorBounded
  have costNonnegative : 0 ≤ cost :=
    mul_nonneg (add_nonneg (sq_nonneg _) (positive n).le) (by positivity)
  have pointwise : ∀ history ∈ posterior.support,
      future history ≤ badPayoff history + cost := by
    intro history _member
    by_cases regular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who
        (project history).1.trace
    · have same := nativeClearHistory_eq_of_raw setup leaks bounds horizon scheduler history.1
        (clear history) (project history).1 (projection history).choose_spec
      have nativeRegular : RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n)
          who (nativeClearHistory setup leaks bounds horizon scheduler
            history.1 (clear history)).trace :=
        Eq.mp (congrArg (fun prior :
          (onePacketProtocol setup leaks bounds horizon (NativeScheduler)).History =>
            RegularTrace setup leaks bounds horizon (NativeScheduler) (sequence n) who prior.trace)
          same.symm) regular
      let normalized : (R).InformationHistory who (some (past, view)) :=
        ⟨history.1, history.2.trans atSite⟩
      obtain ⟨control, state, currentTurn⟩ := control_turn_of_information setup leaks bounds horizon
        scheduler normalized turn
      have row := debtStoppedLaw_foreign_mass_le_rank setup leaks bounds horizon scheduler
        wellFormed covers capacity sequence scale positive le_one weights n (fallback n)
          (assessments n).strategy (assembled n) who alternative opportunity inclusion timely
          certificate rawCertificate history.1 (clear history) control state event currentTurn
          nativeRegular
      have depth := (application setup leaks).trace_bound (initialLaw setup) horizon
        (NativeScheduler) ((NMenu).toRawTrace (initialLaw setup) horizon (NativeScheduler)
          (project history).1.trace)
      have rankBound : (application setup leaks).rank horizon
          (protocolState (runtime setup) leaks history.1.state) ≤ 2 * horizon + 1 := by
        rw [← states history]
        omega
      have rankReal : ((application setup leaks).rank horizon
          (protocolState (runtime setup) leaks history.1.state) : ℝ) ≤ 2 * horizon + 1 := by
        exact_mod_cast rankBound
      have value : future history ≤ cost := by
        calc
          future history = ((kernel history.1).toOuterMeasure exits).toReal :=
            expect_indicator (kernel history.1) exits
          _ ≤ ((scale n) ^ 2 + scale n) * (application setup leaks).rank horizon
              (protocolState (runtime setup) leaks history.1.state) := row
          _ ≤ cost := mul_le_mul_of_nonneg_left rankReal
            (add_nonneg (sq_nonneg _) (positive n).le)
      have badFalse : badPayoff history = 0 := by
        simp [badPayoff, badIndicator, bad, forget, regular]
      simpa only [badFalse, zero_add] using value
    · have badTrue : badPayoff history = 1 := by
        simp [badPayoff, badIndicator, bad, forget, regular]
      have upper : future history ≤ 1 + cost :=
        (le_abs_self _).trans
          ((futureBounded history).trans (le_add_of_nonneg_right costNonnegative))
      simpa only [badTrue] using upper
  have badExpectation : expect posterior badPayoff ≤ drift n := by
    have equal : expect posterior badPayoff =
        ((posterior.map forget).toOuterMeasure bad).toReal :=
      (expect_map forget posterior badIndicator).symm.trans
        (expect_indicator (posterior.map forget) bad)
    exact equal.trans_le irregularMass
  have averaged := expect_mono pointwise (payoffIntegrable_of_finite _ _)
    (payoffIntegrable_of_finite _ _)
  calc
    _ = expect ((posterior.map Subtype.val).bind kernel) indicator :=
      (expect_indicator ((posterior.map Subtype.val).bind kernel) exits).symm
    _ = expect (posterior.map Subtype.val) (fun history => expect (kernel history) indicator) :=
      expect_bind_tower_bounded (posterior.map Subtype.val) kernel indicator indicatorBounded
    _ = expect posterior future := expect_map Subtype.val posterior _
    _ ≤ expect posterior (fun history => badPayoff history + cost) := averaged
    _ = expect posterior badPayoff + cost :=
      (expect_add (payoffIntegrable_of_finite _ _) (payoffIntegrable_of_finite _ _)).trans
        (congrArg (fun value => expect posterior badPayoff + value)
          (expect_constant posterior cost))
    _ ≤ drift n + cost := add_le_add badExpectation (le_refl cost)
    _ = error n := rfl

end Vegas.RecoveryOnePacket
