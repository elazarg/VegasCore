/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncDeviationReadout
import Vegas.Game.IntendedAsyncNash
import Vegas.Source.Purification
import Vegas.Source.ValueBindingAdmission

/-! # The first-turn deviation bound under an arbitrary contract builder

Against the first-turn clients of a source profile, under a scheduler
satisfying the asynchronous contract, every native policy of one player has the
typed outcome law of a source deviation that may bind failure
(`Vegas.asyncDeviation_readout_law`). Binding failure buys a pure policy
nothing: a value-binding policy has the same law of initial parameter and public
result (`Vegas.SourceProgram.bindValues_run_publicOutcome_eq`), and every policy
is a mixture of pure ones (`Vegas.SourceProgram.exists_pureMixture_run`). With a
nonnegative deposit, audit charges only lower the realized payoff. Hence every
native policy against the first-turn clients has audited expected payoff at
most that of a source deviation of the same player
(`Vegas.AsyncServiceSpec.firstTurn_deviation_bound`).

This discharges the hypothesis of
`Vegas.AsyncServiceSpec.isεNash_clientProfile_of_firstTurn_bounds`: for every
contract builder, a source `ε`-Nash equilibrium has turn-counted clients that
are an `(ε + 2 * δ * R)`-Nash equilibrium of every admitting response menu on
the audited raw ledger (`Vegas.AsyncServiceSpec.isεNash_clientProfile`), and
with the reflection this is an approximate correspondence
(`Vegas.AsyncServiceSpec.isεNash_clientProfile_approximate`); likewise for the
intended game (`Vegas.AsyncServiceSpec.intended_clientProfile_isεNash`). The
forward direction needs no audit coverage: it holds for every authentic audit
and every nonnegative deposit.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace SourceProgram.Setup

/-- **Failure buys a deviator nothing.** For every policy of one player, some
value-binding policy of that player has at least the same expected value of the
initial parameter and public result, against unchanged opponents. -/
theorem exists_valueBinding_parameter_expect_ge {Parameter : Type}
    (setup : Setup (Player := Player) (L := L)) (finite : setup.program.FiniteBindingTypes)
    [setup.FiniteInitialLaw] (parameter : State L setup.context → Parameter)
    (value : Parameter × PublicOutcome setup.program → ℝ)
    (bounded : ∃ bound, ∀ state, |value (setup.parameterOutcome parameter state)| ≤ bound)
    (profile : BehavioralProfile setup.program) (who : Player)
    (policy : BehavioralPolicy who setup.program) :
    ∃ alternative : BehavioralPolicy who setup.program,
      ValueBinding setup.program alternative ∧
      expect (setup.run (Function.update profile who policy))
          (fun state => value (setup.parameterOutcome parameter state)) ≤
        expect (setup.run (Function.update profile who alternative))
          (fun state => value (setup.parameterOutcome parameter state)) := by
  obtain ⟨bound, valueBound⟩ := bounded
  have integrable (law : PMF (State L setup.program.terminalCtx)) :
      PayoffIntegrable law (fun state => value (setup.parameterOutcome parameter state)) :=
    payoffIntegrable_of_bounded _ _ (C := bound) fun state => valueBound state
  obtain ⟨mixture, mixtureFinite, mixtureLaw⟩ := exists_pureMixture_run setup finite profile
    policy
  let score := fun choice : PurePolicy who setup.program =>
    expect (setup.run (Function.update profile who
      (PurePolicy.toBehavioral setup.program choice)))
      (fun state => value (setup.parameterOutcome parameter state))
  have tower : expect (setup.run (Function.update profile who policy))
      (fun state => value (setup.parameterOutcome parameter state)) = expect mixture score := by
    rw [mixtureLaw]
    exact expect_bind_tower _ _ _ (by rw [← mixtureLaw]; exact integrable _)
  obtain ⟨choice, _, best⟩ := exists_mem_support_expect_le mixture score
    (payoffIntegrable_of_finite_support _ _ mixtureFinite)
  refine ⟨PurePolicy.toBehavioral setup.program (PurePolicy.bindValues setup.program choice),
    valueBinding_bindValues setup.program choice, ?_⟩
  have laws : (setup.run (Function.update profile who (PurePolicy.toBehavioral setup.program
      (PurePolicy.bindValues setup.program choice)))).map (setup.parameterOutcome parameter) =
      (setup.run (Function.update profile who
        (PurePolicy.toBehavioral setup.program choice))).map
          (setup.parameterOutcome parameter) := by
    rw [run_map_parameterOutcome, run_map_parameterOutcome]
    unfold parameterRun
    apply bind_congr_on_support _
    intro initial _
    have outcomes := bindValues_run_publicOutcome_eq setup.program profile choice initial
    have mapped := congrArg (PMF.map fun outcome => (parameter initial, outcome)) outcomes
    simpa only [PMF.map_comp, Function.comp_def] using mapped
  have same : expect (setup.run (Function.update profile who (PurePolicy.toBehavioral
      setup.program (PurePolicy.bindValues setup.program choice))))
      (fun state => value (setup.parameterOutcome parameter state)) = score choice := by
    have valued := congrArg (fun law => expect law value) laws
    simpa only [expect_map, Function.comp_def] using valued
  rw [same, tower]
  exact best

end SourceProgram.Setup

namespace AsyncServiceSpec

variable [Fintype Player] (service : AsyncServiceSpec Player L)

/-- **The first-turn deviation bound.** Under the asynchronous contract, for
every authentic audit and every nonnegative deposit, every native policy of
one player against the first-turn clients of a source profile has audited
expected payoff at most that of some source deviation of the same player. Its
typed outcome law is that of a source deviation whose bindings may fail
(`Vegas.asyncDeviation_readout_law`); failure buys nothing, and charges only
lower the payoff. -/
theorem firstTurn_deviation_bound {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (bounded : ∀ who, ∃ bound, ∀ state : State L service.setup.program.terminalCtx,
      |utility (service.setup.parameterOutcome parameter state) who| ≤ bound)
    {turns : Nat} (source : Profile service.sourceModel.behavioralSignature) (who : Player)
    (alternative : (serviceApplication service.setup service.mode service.deadline
      service.leaks).Policy) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    let clients := sourceServiceClientProfile service.setup
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source)
    ∃ deviation : service.sourceModel.BehavioralPolicy who,
      expect (((serviceApplication service.setup service.mode service.deadline
        service.leaks).roundsFrom (serviceInitialLaw service.setup service.mode)
          service.scheduler (deviatedTurnProfile service.bound turns
            (firstTurnTiming service.setup turns service.mode) clients who alternative)
          service.horizon).map (serviceApplication service.setup service.mode service.deadline
            service.leaks).finished)
        (fun final => payoff final who) ≤
      expect (service.sourceModel.runBehavioral (Profile.update source who deviation)
        (instructionCount service.setup.program + 1))
        (fun final => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who)) := by
  intro base payoff clients
  classical
  let app := serviceApplication service.setup service.mode service.deadline service.leaks
  let admission := CommitmentInterface.values service.setup.program
  let decoded := service.setup.decodeBehavioralProfile admission source
  obtain ⟨bound, valueBound⟩ := bounded who
  let value := fun outcome : Option (State L service.setup.program.terminalCtx) =>
    outcome.elim 0 (fun state => utility (service.setup.parameterOutcome parameter state) who)
  have valueBounded (outcome : Option (State L service.setup.program.terminalCtx)) :
      |value outcome| ≤ |bound| := by
    cases outcome with
    | none => simp [value]
    | some state => exact (valueBound _).trans (le_abs_self _)
  obtain ⟨policy, law⟩ := asyncDeviation_readout_law service.setup service.leaks ordered
    service.contract service.timely turns decoded who alternative
  let native := ((app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler
    (deviatedTurnProfile service.bound turns (firstTurnTiming service.setup turns service.mode)
      clients who
      alternative) service.horizon).map app.finished)
  -- Charges only lower the payoff.
  have charged : expect native (fun final => payoff final who) ≤
      expect native (fun final => base final who) := by
    apply expect_mono _ (payoffIntegrable_of_bounded _ _ (C := |bound| + |deposit who|)
        fun final => ?_) (payoffIntegrable_of_bounded _ _ (C := |bound|)
          fun final => valueBounded _)
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
      have baseBound : |base final who| ≤ |bound| := valueBounded _
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
        _ ≤ |bound| + |deposit who| := add_le_add baseBound chargeBound
  -- The base payoff is read from the typed outcome, whose law is a source deviation's.
  have native_value : expect native (fun final => base final who) =
      expect (service.setup.run (Function.update decoded who policy))
        (fun state => utility (service.setup.parameterOutcome parameter state) who) := by
    have mapped := congrArg (fun distribution => expect distribution value) law
    simp only [expect_map, Function.comp_def] at mapped
    change expect (PMF.map app.finished _) (fun final => value
      (serviceSourceReadout service.setup service.mode service.deadline service.leaks final)) = _
    rw [expect_map]
    exact mapped
  -- Binding failure buys nothing.
  obtain ⟨better, valueBinding, improved⟩ :=
    service.setup.exists_valueBinding_parameter_expect_ge
      (sourceService_finiteBindingTypes service.setup service.bounds service.values) parameter
      (fun outcome => utility outcome who) ⟨bound, valueBound⟩ decoded who policy
  have allowed : better.Admitted service.setup.program admission :=
    (BehavioralPolicy.admitted_values_iff_valueBinding service.setup.program better).mpr
      valueBinding
  refine ⟨(service.setup.behavioralPolicyEquiv admission who) ⟨better, allowed⟩, ?_⟩
  have readout : (service.sourceModel.runBehavioral (Profile.update source who
      ((service.setup.behavioralPolicyEquiv admission who) ⟨better, allowed⟩))
      (instructionCount service.setup.program + 1)).map
        (fun final => service.setup.protocolReadout final.state) =
      (service.setup.run (Function.update decoded who better)).map some := by
    have readoutLaw := service.setup.runBehavioralFrom_readout admission
      (Profile.update source who ((service.setup.behavioralPolicyEquiv admission who)
        ⟨better, allowed⟩)) (instructionCount service.setup.program + 1)
      (service.setup.executionProtocol admission).initHistory (Nat.le_refl _)
    rw [service.setup.decodeBehavioralProfile_update admission source who better allowed]
      at readoutLaw
    exact readoutLaw
  have sourceValue := congrArg (fun distribution => expect distribution value) readout
  simp only [expect_map, Function.comp_def] at sourceValue
  change expect native (fun final => payoff final who) ≤ _
  calc expect native (fun final => payoff final who)
      ≤ expect native (fun final => base final who) := charged
    _ = _ := native_value
    _ ≤ _ := improved
    _ = _ := by
      rw [sourceValue]
      rfl

omit [Fintype Player] in
/-- An interval containing every realized payoff value bounds the utility of
every typed outcome. -/
private theorem bounded_of_within {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (deposit : Player → ℝ) (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range) (who : Player) :
    ∃ bound, ∀ state : State L service.setup.program.terminalCtx,
      |utility (service.setup.parameterOutcome parameter state) who| ≤ bound := by
  refine ⟨|low who| + |range|, fun state => ?_⟩
  have inside := within who (some state) false
  simp only [Option.elim_some, Bool.false_eq_true, ↓reduceIte, sub_zero] at inside
  rw [abs_le]
  constructor <;> linarith [neg_abs_le (low who), le_abs_self (low who), le_abs_self range,
    abs_nonneg range, inside.1, inside.2]

/-- **Approximate Nash transfer under an arbitrary contract builder.** Under the
asynchronous contract, for every authentic audit and every nonnegative deposit,
if a source profile is an `ε`-Nash equilibrium of the source protocol model,
its turn-counted clients are an `(ε + 2 * δ * R)`-Nash equilibrium of every
response menu that admits every profile's clients, for the audited payoff. Here
`δ` is the total deferral weight of the turn timing and every realized payoff
value, charged or not, lies in an interval of length `R`. -/
theorem isεNash_clientProfile {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (menu : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile service.sourceModel.behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.deadline service.leaks
          service.bound turns timing
          (sourceServiceClientProfile service.setup (service.setup.decodeBehavioralProfile
            (CommitmentInterface.values service.setup.program) source)) who))
    (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range)
    (ε : ℝ) (source : Profile service.sourceModel.behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * range)
        (service.clientProfile menu timing source) :=
  service.isεNash_clientProfile_of_firstTurn_bounds ordered parameter utility sample
    authentic deposit
    menu timing covered low range within ε source
    (fun who alternative => service.firstTurn_deviation_bound ordered
      parameter utility sample deposit
      nonnegative (service.bounded_of_within parameter utility deposit low range within) source
      who alternative)

/-- **Approximate Nash correspondence under an arbitrary contract builder.**
Under the asynchronous contract, for every authentic audit and every
nonnegative deposit, a source `ε`-Nash equilibrium has turn-counted clients
that are an `(ε + 2 * δ * R)`-Nash equilibrium of every admitting response menu
for the audited payoff, and conversely a native `ε`-Nash equilibrium of the
clients comes from a source `(ε + 2 * δ * R)`-Nash equilibrium. -/
theorem isεNash_clientProfile_approximate {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (menu : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile service.sourceModel.behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.deadline service.leaks
          service.bound turns timing
          (sourceServiceClientProfile service.setup (service.setup.decodeBehavioralProfile
            (CommitmentInterface.values service.setup.program) source)) who))
    (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range)
    (ε : ℝ) (source : Profile service.sourceModel.behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    (IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * range)
        (service.clientProfile menu timing source)) ∧
    (IsεNash ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile menu timing source) →
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * (∑ event, timing.deferral event) * range) source) :=
  ⟨service.isεNash_clientProfile ordered parameter utility sample authentic deposit
    nonnegative menu
      timing covered low range within ε source,
    service.isεNash_of_clientProfile ordered parameter utility sample authentic deposit menu
      timing
      covered low range within ε source⟩

/-- **Intended approximate Nash equilibria under an arbitrary contract
builder.** For a well-formed setup, a forfeit no smaller than the payoff range,
every authentic audit and every nonnegative deposit, the turn-counted clients
of a source profile extending an `ε`-Nash equilibrium of the intended game are
an `(ε + 2 * δ * R)`-Nash equilibrium of every admitting response menu under the
forfeit pass, and their joint law of typed outcome and realized settlement is
within `δ` in total variation of the intended joint law of terminal store and
payoff. -/
theorem intended_clientProfile_isεNash {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (menu : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile service.sourceModel.behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.deadline service.leaks
          service.bound turns timing
          (sourceServiceClientProfile service.setup (service.setup.decodeBehavioralProfile
            (CommitmentInterface.values service.setup.program) source)) who))
    (low : Player → ℝ) (spread : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => forfeitUtility service.setup.program forfeit utility
          (service.setup.parameterOutcome parameter state) who) -
            (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => forfeitUtility service.setup.program forfeit utility
          (service.setup.parameterOutcome parameter state) who) -
            (if charged then deposit who else 0) ≤ low who + spread)
    (intended : Profile service.setup.intendedModel.behavioralSignature)
    (source : Profile service.sourceModel.behavioralSignature)
    (agrees : service.setup.intendedRestriction.ExtendsProfile intended source) (ε : ℝ)
    (equilibrium : IsεNash (service.setup.intendedModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
      (fun final who => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)) ε
      intended) :
    let forfeited := forfeitUtility service.setup.program forfeit utility
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    IsεNash ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * spread)
        (service.clientProfile menu timing source) ∧
      PMF.WithinTV (∑ event, timing.deferral event)
        (((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
          service.scheduler).runBehavioral (service.clientProfile menu timing source)
            (2 * service.horizon + 1)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                (serviceSourceReadout service.setup service.mode service.deadline service.leaks
                  final.state, payoffs)))
        ((service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => (service.setup.protocolReadout final.state,
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) :=
  service.intended_clientProfile_isεNash_of_firstTurn_bounds ordered wellFormed parameter
    utility forfeit
    range sample authentic deposit menu timing covered low spread within intended source agrees ε
    equilibrium (fun who alternative => service.firstTurn_deviation_bound
      ordered parameter (forfeitUtility service.setup.program forfeit utility)
      sample deposit nonnegative
      (service.bounded_of_within parameter _ deposit low spread within) source who alternative)

end AsyncServiceSpec

end Vegas
