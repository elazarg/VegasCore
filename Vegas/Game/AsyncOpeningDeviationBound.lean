/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncWithholdReadout
import Vegas.Game.AsyncServiceDeviationBound
import GameTheoryExtensions.Math.Probability.GatedExpectation

/-! # The first-turn deviation bound for clients that open

On a reveal-relaxed graph, against the first-turn clients of a source profile
that opens effectively, one player follows an arbitrary native policy. Along
the runs on which it does not withhold one of its disclosures, the typed
outcome is dominated by a source deviation's; along the others it records a
failed reveal of that player (`Vegas.asyncDeviation_withheld_readout`), whose
forfeit, no smaller than the payoff range, leaves it at most the least payoff.

Paying the least payoff at every outcome with a failed reveal of the deviator
is therefore at least as good for it, and that payoff is read from the source
outcome. Failure buys nothing (`Vegas.SourceProgram.Setup.exists_valueBinding_parameter_expect_ge`).
In the source game, a failed reveal of the deviator is a debt, so the retained
conditional of the deviation in the intended game is at least as good
(`GameTheory.Protocol.InformationModel.ActionRestriction.expect_deviation_le_retained`),
and it extends to a source deviation with the same forfeited payoff. Hence
every native policy against the opening clients has audited expected payoff at
most that of a source deviation of the same player
(`Vegas.AsyncServiceSpec.openingFirstTurn_deviation_bound`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace AsyncServiceSpec

variable [Fintype Player] (service : AsyncServiceSpec Player L)

/-- **The first-turn deviation bound for opening clients.** On a reveal-relaxed
graph of a well-formed setup, with a forfeit no smaller than the payoff range,
for every authentic audit and every nonnegative deposit, against the first-turn
clients of a source profile that extends a profile of the intended game and
whose clients open effectively, every native policy of one player has audited
expected payoff at most that of some source deviation of the same player under
the forfeit. -/
theorem openingFirstTurn_deviation_bound {Parameter : Type}
    (relaxed : (serviceGraph service.setup service.mode).RevealRelaxedOrdered)
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who) {turns : Nat}
    (intended : Profile service.setup.intendedModel.behavioralSignature)
    (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature)
    (agrees : service.setup.intendedRestriction.ExtendsProfile intended source)
    (opens : ∀ player, (sourceServiceClientProfile service.setup
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source) player).OpensEffectively service.setup.program []
          (Revelations.initial service.setup.context))
    (who : Player)
    (alternative : (serviceApplication service.setup service.mode service.deadline
      service.leaks).Policy) :
    let forfeited := forfeitUtility service.setup.program forfeit utility
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    let clients := sourceServiceClientProfile service.setup
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source)
    ∃ deviation : (service.sourceModel (CommitmentInterface.values
      service.setup.program)).BehavioralPolicy who,
      expect (((serviceApplication service.setup service.mode service.deadline
        service.leaks).roundsFrom (serviceInitialLaw service.setup service.mode)
          service.scheduler (deviatedTurnProfile service.bound turns
            (firstTurnTiming service.setup turns service.mode) clients who alternative)
          service.horizon).map (serviceApplication service.setup service.mode service.deadline
            service.leaks).finished)
        (fun final => payoff final who) ≤
      expect ((service.sourceModel (CommitmentInterface.values
        service.setup.program)).runBehavioral (Profile.update source who deviation)
        (instructionCount service.setup.program + 1))
        (fun final => (service.setup.protocolReadout final.state).elim 0
          (fun state => forfeited (service.setup.parameterOutcome parameter state) who)) := by
  intro forfeited base payoff clients
  classical
  have := service.initialFinite
  let app := serviceApplication service.setup service.mode service.deadline service.leaks
  let admission := CommitmentInterface.values service.setup.program
  let decoded := service.setup.decodeBehavioralProfile admission source
  let outcomeOf := service.setup.parameterOutcome parameter
  -- The deviator's unforfeited and forfeited payoffs of a terminal state.
  let plain := fun state : State L service.setup.program.terminalCtx =>
    utility (outcomeOf state) who
  let value := fun state : State L service.setup.program.terminalCtx =>
    forfeited (outcomeOf state) who
  obtain ⟨reference, _⟩ := (service.setup.run decoded).support_nonempty
  have forfeitNonneg : 0 ≤ forfeit := by
    have := range (outcomeOf reference) (outcomeOf reference) who
    linarith
  have plainBelow (state other : State L service.setup.program.terminalCtx) :
      plain state - forfeit ≤ plain other := by
    have := range (outcomeOf state) (outcomeOf other) who
    simp only [plain]
    linarith
  -- The least unforfeited payoff.
  have bddBelow : BddBelow (Set.range plain) :=
    ⟨plain reference - forfeit, by
      rintro _ ⟨state, rfl⟩
      exact plainBelow reference state⟩
  have : Nonempty (State L service.setup.program.terminalCtx) := ⟨reference⟩
  let floor := ⨅ state, plain state
  have floorLe (state : State L service.setup.program.terminalCtx) : floor ≤ plain state :=
    ciInf_le bddBelow state
  have forfeitedLe (state : State L service.setup.program.terminalCtx) :
      plain state - forfeit ≤ floor :=
    le_ciInf fun other => plainBelow state other
  -- Failed reveals cost at least the forfeit.
  have failedBelow (state : State L service.setup.program.terminalCtx)
      (failed : 0 < failedReveals service.setup.program who (publicOutcome service.setup.program
        state)) : value state ≤ floor := by
    have count : (1 : ℝ) ≤ (failedReveals service.setup.program who
        (outcomeOf state).2 : ℝ) := Nat.one_le_cast.mpr failed
    have := forfeitedLe state
    simp only [value, forfeited, forfeitUtility]
    change utility (outcomeOf state) who - forfeit * _ ≤ floor
    nlinarith
  -- The payoff that charges the floor at every failed reveal of the deviator.
  let charged := fun outcome : Parameter × PublicOutcome service.setup.program =>
    if failedReveals service.setup.program who outcome.2 = 0 then utility outcome who else floor
  let better := fun state : State L service.setup.program.terminalCtx => charged (outcomeOf state)
  have betterAbove (state : State L service.setup.program.terminalCtx) :
      value state ≤ better state := by
    simp only [better, charged]
    split_ifs with clean
    · simp only [value, forfeited, forfeitUtility]
      rw [clean]
      simp
    · exact failedBelow state (Nat.pos_of_ne_zero clean)
  have floorBelow (state : State L service.setup.program.terminalCtx) : floor ≤ better state := by
    simp only [better, charged]
    split_ifs
    · exact floorLe state
    · exact le_rfl
  -- Uniform bounds.
  let count := (revealCells service.setup.program).length
  let bound := |plain reference| + forfeit + forfeit * count
  have countNonneg : (0 : ℝ) ≤ forfeit * count := mul_nonneg forfeitNonneg (Nat.cast_nonneg _)
  have plainBound (state : State L service.setup.program.terminalCtx) :
      |plain state| ≤ |plain reference| + forfeit := by
    have upper := plainBelow reference state
    have lower := plainBelow state reference
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (plain reference), le_abs_self (plain reference)]
  have valueBound (state : State L service.setup.program.terminalCtx) : |value state| ≤ bound := by
    have failedLe : (failedReveals service.setup.program who (outcomeOf state).2 : ℝ) ≤ count :=
      Nat.cast_le.mpr (List.length_filter_le _ _)
    have failedNonneg : (0 : ℝ) ≤ failedReveals service.setup.program who (outcomeOf state).2 :=
      Nat.cast_nonneg _
    have plainAbs := plainBound state
    simp only [value, forfeited, forfeitUtility]
    change |utility (outcomeOf state) who - forfeit * _| ≤ bound
    rw [abs_le] at plainAbs ⊢
    change -(|plain reference| + forfeit) ≤ utility (outcomeOf state) who ∧
      utility (outcomeOf state) who ≤ |plain reference| + forfeit at plainAbs
    constructor <;> nlinarith
  have betterBound (state : State L service.setup.program.terminalCtx) :
      |better state| ≤ bound := by
    have floorUpper := floorLe reference
    have floorLower := forfeitedLe reference
    simp only [better, charged]
    split_ifs
    · exact (plainBound state).trans (by linarith)
    · rw [abs_le]
      constructor <;> linarith [neg_abs_le (plain reference), le_abs_self (plain reference)]
  -- The native law up to withholding.
  obtain ⟨policy, dominated, withheldFailed⟩ := asyncDeviation_withheld_readout service.setup
    service.leaks relaxed service.contract service.timely turns clients opens who alternative
  let runs := app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler
    (deviatedTurnProfile service.bound turns (firstTurnTiming service.setup turns service.mode)
      clients who alternative) service.horizon
  let valueOf := fun outcome : Option (State L service.setup.program.terminalCtx) =>
    outcome.elim 0 value
  have valueOfBound (outcome : Option (State L service.setup.program.terminalCtx)) :
      |valueOf outcome| ≤ bound := by
    cases outcome with
    | none =>
        simp only [valueOf, Option.elim_none, abs_zero]
        linarith [abs_nonneg (plain reference)]
    | some state => exact valueBound state
  -- Charges only lower the payoff.
  have chargedLe : expect (runs.map app.finished) (fun final => payoff final who) ≤
      expect (runs.map app.finished) (fun final => base final who) := by
    apply expect_mono _ (payoffIntegrable_of_bounded _ _ (C := bound + |deposit who|)
        fun final => ?_) (payoffIntegrable_of_bounded _ _ (C := bound)
          fun final => valueOfBound _)
    · intro final _
      have rate := TerminalAudit.charge_mem_Icc
        ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
          service.leaks)
        (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) final
          who
      change base final who - TerminalAudit.charge _ _ final who * deposit who ≤ base final who
      nlinarith [rate.1, nonnegative who]
    · have rate := TerminalAudit.charge_mem_Icc
        ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
          service.leaks)
        (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) final
          who
      change |base final who - TerminalAudit.charge _ _ final who * deposit who| ≤ _
      have baseBound : |base final who| ≤ bound := valueOfBound _
      have chargeBound : |TerminalAudit.charge ((serviceRuntime service.setup service.mode
        service.deadline).serviceAuditObservation
          service.leaks) (serviceSourceAudit service.setup service.mode service.deadline
            service.leaks sample) final who *
            deposit who| ≤ |deposit who| := by
        rw [abs_mul]
        have : |TerminalAudit.charge ((serviceRuntime service.setup service.mode
          service.deadline).serviceAuditObservation
            service.leaks) (serviceSourceAudit service.setup service.mode service.deadline
              service.leaks sample) final who| ≤ 1 :=
          abs_le.mpr ⟨by linarith [rate.1], rate.2⟩
        nlinarith [abs_nonneg (deposit who), abs_nonneg (TerminalAudit.charge
          ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
            service.leaks)
          (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample)
            final who)]
      calc _ ≤ |base final who| + |TerminalAudit.charge _ _ final who * deposit who| :=
            abs_sub _ _
        _ ≤ bound + |deposit who| := add_le_add baseBound chargeBound
  -- Charging the floor at every failed reveal of the deviator is at least as good.
  have gated : expect (runs.map app.finished) (fun final => base final who) ≤
      expect (service.setup.run (Function.update clients who policy)) better := by
    change expect (runs.map app.finished) (fun final => valueOf
      (serviceSourceReadout service.setup service.mode service.deadline service.leaks final)) ≤ _
    rw [expect_map]
    refine expect_le_of_gated runs
      (fun execution => ¬ DeviatorWithheld who execution.application.config)
      (fun execution => serviceSourceReadout service.setup service.mode service.deadline
        service.leaks (app.finished execution)) _ (fun outcome => ?_) valueOf better floor
      valueOfBound betterBound (fun execution member notPassing => ?_) betterAbove floorBelow
    · refine le_trans (le_of_eq ?_) (dominated outcome)
      congr 2
      funext execution
      by_cases withheld : DeviatorWithheld who execution.application.config
      · simp only [withheld, not_true_eq_false, ↓reduceIte]
      · simp only [withheld, not_false_eq_true, ↓reduceIte]
        rfl
    · obtain ⟨terminal, read, failed⟩ := withheldFailed execution member (not_not.mp notPassing)
      rw [read]
      exact failedBelow terminal failed
  -- Normalizing the clients' disclosures changes no source law.
  have normalized : service.setup.run (Function.update clients who policy) =
      service.setup.run (Function.update decoded who policy) :=
    run_update_normalizeDisclosureProfile service.setup decoded who policy
  -- Binding failure buys nothing.
  have finite := sourceService_finiteBindingTypes service.setup service.bounds service.values
  obtain ⟨improved, valueBinding, improvedLe⟩ :=
    service.setup.exists_valueBinding_parameter_expect_ge finite parameter charged
      ⟨bound, betterBound⟩ decoded who policy
  have allowed : improved.Admitted service.setup.program admission :=
    (BehavioralPolicy.admitted_values_iff_valueBinding service.setup.program improved).mpr
      valueBinding
  let sourceDeviation := (service.setup.behavioralPolicyEquiv admission who) ⟨improved, allowed⟩
  have readout : ((service.sourceModel (CommitmentInterface.values
    service.setup.program)).runBehavioral (Profile.update source who sourceDeviation)
      (instructionCount service.setup.program + 1)).map
        (fun final => service.setup.protocolReadout final.state) =
      (service.setup.run (Function.update decoded who improved)).map some := by
    have readoutLaw := service.setup.runBehavioralFrom_readout admission
      (Profile.update source who sourceDeviation) (instructionCount service.setup.program + 1)
      (service.setup.executionProtocol admission).initHistory (Nat.le_refl _)
    rw [service.setup.decodeBehavioralProfile_update admission source who improved allowed]
      at readoutLaw
    exact readoutLaw
  let targetPayoff := fun final : (service.setup.executionProtocol admission).History =>
    (service.setup.protocolReadout final.state).elim 0 better
  let sourcePayoff := fun final : service.setup.intendedProtocol.History =>
    (service.setup.protocolReadout final.state).elim 0 plain
  have sourceValue : expect (service.setup.run (Function.update decoded who improved)) better =
      expect ((service.sourceModel (CommitmentInterface.values
        service.setup.program)).runBehavioral (Profile.update source who sourceDeviation)
        (instructionCount service.setup.program + 1)) targetPayoff := by
    have mapped := congrArg (fun law => expect law
      (fun outcome : Option (State L service.setup.program.terminalCtx) => outcome.elim 0 better))
      readout
    simp only [expect_map, Function.comp_def] at mapped
    exact mapped.symm
  -- A failed reveal of the deviator is a debt; the retained conditional is at least as good.
  have : Finite (service.setup.executionProtocol admission).History :=
    service.setup.finite_history finite _
  have matching : ∀ history, targetPayoff (service.setup.intendedRestriction.history history) =
      sourcePayoff history := by
    intro history
    change (service.setup.protocolReadout history.state).elim 0 _ =
      (service.setup.protocolReadout history.state).elim 0 _
    cases read : service.setup.protocolReadout history.state with
    | none => rfl
    | some terminal =>
        have zero := service.setup.failedReveals_eq_zero_of_intendedState
          (service.setup.intendedState_trace wellFormed history.trace) who read
        change charged (outcomeOf terminal) = plain terminal
        exact ite_eq_left zero
  have forfeits : ∀ (indebted : (service.setup.executionProtocol admission).History)
      (history : service.setup.intendedProtocol.History),
      service.setup.IndebtedState who indebted.state →
      (service.setup.executionProtocol admission).terminal indebted.state →
      service.setup.intendedProtocol.terminal history.state →
      targetPayoff indebted ≤ sourcePayoff history := by
    intro indebted history owing stopped intendedStopped
    obtain ⟨intendedTerminal, intendedRead⟩ :=
      service.setup.exists_protocolReadout_of_terminal admission intendedStopped
    cases finalState : indebted.state with
    | none =>
        rw [finalState] at owing
        exact owing.elim
    | some state =>
        rw [finalState] at owing stopped
        obtain ⟨terminal, read⟩ :=
          ProtocolState.exists_readout_of_terminal service.setup.program state stopped
        have positive :=
          ProtocolState.failedReveals_pos_of_indebted who service.setup.program state owing read
        change (service.setup.protocolReadout indebted.state).elim 0 _ ≤
          (service.setup.protocolReadout history.state).elim 0 _
        have read' : service.setup.protocolReadout indebted.state = some terminal := by
          rw [finalState]
          exact read
        rw [read', intendedRead]
        change charged (outcomeOf terminal) ≤ plain intendedTerminal
        rw [show charged (outcomeOf terminal) = floor from
          ite_eq_right (Nat.pos_iff_ne_zero.mp positive)]
        exact floorLe intendedTerminal
  let retainedDeviation := service.setup.intendedRestriction.retainedPolicy who sourceDeviation
    (intended who)
  have retained := service.setup.intendedRestriction.expect_deviation_le_retained
    (service.setup.protocol_bounded _)
    ((service.setup.informationModel _).menuRestriction_reflecting _ _
      service.setup.intendedMenu_subset)
    intended source agrees who sourceDeviation (intended who) (service.setup.IndebtedState who)
    (service.setup.indebted_localStep who)
    (fun original choices next running _ extra reached =>
      service.setup.indebted_of_extra wellFormed who original choices next running extra reached)
    sourcePayoff targetPayoff matching forfeits
  -- The retained conditional extends to a source deviation with the same forfeited payoff.
  let extension := service.setup.intendedRestriction.extendProfile
    (Function.update intended who retainedDeviation) source who
  have extended := agrees.update_extendProfile who retainedDeviation
  have law := service.setup.intendedRestriction.initialized_law _ _ extended
    (instructionCount service.setup.program + 1)
  refine ⟨extension, ?_⟩
  have extensionValue : expect (service.setup.intendedModel.runBehavioral
      (Function.update intended who retainedDeviation)
        (instructionCount service.setup.program + 1)) sourcePayoff =
      expect ((service.sourceModel (CommitmentInterface.values
        service.setup.program)).runBehavioral (Profile.update source who extension)
        (instructionCount service.setup.program + 1))
        (fun final => (service.setup.protocolReadout final.state).elim 0 value) := by
    change _ = expect ((service.sourceModel (CommitmentInterface.values
      service.setup.program)).runBehavioral (Function.update source who extension)
      (instructionCount service.setup.program + 1)) _
    rw [← law, expect_map]
    congr 1
    funext history
    change (service.setup.protocolReadout history.state).elim 0 plain =
      (service.setup.protocolReadout history.state).elim 0 value
    cases read : service.setup.protocolReadout history.state with
    | none => rfl
    | some terminal =>
        have zero := service.setup.failedReveals_eq_zero_of_intendedState
          (service.setup.intendedState_trace wellFormed history.trace) who read
        change plain terminal = forfeitUtility service.setup.program forfeit utility
          (outcomeOf terminal) who
        simp only [forfeitUtility, plain]
        change _ = _ - forfeit * (failedReveals service.setup.program who
          (publicOutcome service.setup.program terminal) : ℝ)
        rw [zero]
        simp
  calc expect (runs.map app.finished) (fun final => payoff final who)
      ≤ expect (runs.map app.finished) (fun final => base final who) := chargedLe
    _ ≤ expect (service.setup.run (Function.update clients who policy)) better := gated
    _ = expect (service.setup.run (Function.update decoded who policy)) better := by
        rw [normalized]
    _ ≤ expect (service.setup.run (Function.update decoded who improved)) better := improvedLe
    _ = expect ((service.sourceModel (CommitmentInterface.values
      service.setup.program)).runBehavioral (Profile.update source who sourceDeviation)
          (instructionCount service.setup.program + 1)) targetPayoff := sourceValue
    _ ≤ expect (service.setup.intendedModel.runBehavioral
          (Function.update intended who retainedDeviation)
            (instructionCount service.setup.program + 1)) sourcePayoff := retained
    _ = _ := extensionValue

end AsyncServiceSpec

end Vegas
