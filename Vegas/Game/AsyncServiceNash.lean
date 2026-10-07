/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceSpec
import Vegas.Game.SourceServiceTurnSettlement
import Vegas.Game.SourceServiceClientPolicy
import GameTheory.Core.Approximate

/-! # Reflection of approximate Nash under an arbitrary contract builder

For a full-source service whose public scheduler satisfies the asynchronous
contract, the turn-counted clients of a source profile
(`Vegas.AsyncServiceSpec.clientProfile`) are played in an arbitrary response
menu that admits them; the bounded raw menu does
(`Vegas.AsyncServiceSpec.rawMenu_admits`). Their joint law of typed outcome and realized
settlement is within the total deferral weight `δ` of the source law in total
variation (`Vegas.sourceServiceClients_settlement_lawError`). When every
realized payoff value lies in an interval of length `R`, expected payoffs are
within `δ * R`. Each player's client depends only on its own source policy, so
a compiled source deviation is a native deviation, and a native `ε`-Nash
equilibrium of the clients reflects to a source `(ε + 2 * δ * R)`-Nash
equilibrium (`Vegas.AsyncServiceSpec.isεNash_of_clientProfile`).

In the forward direction, the turn-counted clients against any native policy of
one player are within `δ` of the first-turn clients against it
(`Vegas.deviatedTurnProfile_roundsFrom_bind_within`). Hence, if
every native policy against the first-turn clients is bounded in audited
expected payoff by a source deviation, every source `ε`-Nash equilibrium has
clients that are an `(ε + 2 * δ * R)`-Nash equilibrium of every admitting menu
(`Vegas.AsyncServiceSpec.isεNash_clientProfile_of_firstTurn_bounds`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace AsyncServiceSpec

variable (service : AsyncServiceSpec Player L)

/-- The source information model of the service's program, with every binding
value admitted. -/
abbrev sourceModel := service.setup.informationModel
  (CommitmentInterface.values service.setup.program)

/-- **The turn-counted clients** of a source profile in a response menu: each
player follows the turn-counted policy of its disclosure-normalized source
policy, completed by silence after its own off-policy responses
(`Vegas.sourceServiceClientPolicy`). -/
def clientProfile (menu : (serviceApplication service.setup service.mode service.deadline
    service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source : Profile service.sourceModel.behavioralSignature) :
    Profile (menu.information (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler).behavioralSignature := fun who =>
  menu.restrictPolicy (serviceInitialLaw service.setup service.mode) service.horizon
    service.scheduler who
    (serviceClientPolicy service.setup service.mode service.deadline service.leaks service.bound
      turns timing
      (sourceServiceClientProfile service.setup
        (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
          source)) who)

omit [Fintype Player] in
private theorem clientPolicy_congr {turns : Nat} (timing : TurnTiming service.setup turns
    service.mode)
    (profile other : BehavioralProfile service.setup.program) (who : Player)
    (same : profile who = other who) :
    serviceClientPolicy service.setup service.mode service.deadline service.leaks service.bound
      turns timing profile who =
      serviceClientPolicy service.setup service.mode service.deadline service.leaks service.bound
        turns timing other
        who := by
  unfold serviceClientPolicy serviceTurnPolicy serviceTurnFamily serviceCanonicalOpportunity
    serviceCanonicalPolicy compileEventProfile
  rw [same]

omit [Fintype Player] in
/-- Each player's client depends only on its own source policy. -/
theorem clientProfile_congr (menu : (serviceApplication service.setup service.mode service.deadline
    service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source other : Profile service.sourceModel.behavioralSignature) (who : Player)
    (same : source who = other who) :
    service.clientProfile menu timing source who = service.clientProfile menu timing other who := by
  have decoded : sourceServiceClientProfile service.setup
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source) who =
    sourceServiceClientProfile service.setup
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        other) who := by
    simp only [sourceServiceClientProfile, normalizeDisclosureProfile,
      Setup.decodeBehavioralProfile, same]
  exact congrArg (menu.restrictPolicy (serviceInitialLaw service.setup service.mode) service.horizon
    service.scheduler who) (clientPolicy_congr service timing _ _ who decoded)

omit [Fintype Player] in
/-- The clients of a unilateral source deviation are a unilateral deviation of
the clients. -/
theorem clientProfile_update (menu : (serviceApplication service.setup service.mode
    service.deadline service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (source : Profile service.sourceModel.behavioralSignature) (who : Player)
    (alternative : service.sourceModel.BehavioralPolicy who) :
    Profile.update (service.clientProfile menu timing source) who
        (service.clientProfile menu timing (Profile.update source who alternative) who) =
      service.clientProfile menu timing (Profile.update source who alternative) := by
  funext other
  by_cases same : other = who
  · subst other
    simp only [Profile.update, Function.update_self]
  · simp only [Profile.update, Function.update_of_ne same]
    exact service.clientProfile_congr menu timing _ _ other (by
      simp only [Function.update_of_ne same])

/-- For every source profile, the clients' audited expected payoff is within
the total deferral weight times the payoff range of the source expected
payoff, in both directions, and both expectations are of integrable payoffs. -/
private theorem clientProfile_value_close {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.deadline
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
    (source : Profile service.sourceModel.behavioralSignature) (who : Player) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    let native := (menu.information (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler).runBehavioral (service.clientProfile menu timing source)
        (2 * service.horizon + 1)
    let original := service.sourceModel.runBehavioral source
      (instructionCount service.setup.program + 1)
    let sourcePayoff := fun final : (service.setup.executionProtocol
        (CommitmentInterface.values service.setup.program)).History =>
      (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)
    PayoffIntegrable native (fun final => payoff final.state who) ∧
      PayoffIntegrable original sourcePayoff ∧
      expect native (fun final => payoff final.state who) - expect original sourcePayoff ≤
        (∑ event, timing.deferral event) * range ∧
      expect original sourcePayoff - expect native (fun final => payoff final.state who) ≤
        (∑ event, timing.deferral event) * range := by
  intro base payoff native original sourcePayoff
  classical
  let settle := TerminalAudit.settlement base
    ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
      service.leaks)
    (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
  let decoded := service.setup.decodeBehavioralProfile
    (CommitmentInterface.values service.setup.program) source
  let stateUtility := fun state : State L service.setup.program.terminalCtx =>
    utility (service.setup.parameterOutcome parameter state)
  let nativeJoint := native.bind fun final =>
    (settle final.state).map fun payoffs =>
      (serviceSourceReadout service.setup service.mode service.deadline service.leaks final.state,
        payoffs)
  let sourceJoint := (service.setup.run decoded).map fun state =>
    (some state, stateUtility state)
  have close : PMF.WithinTV (∑ event, timing.deferral event) nativeJoint sourceJoint :=
    sourceServiceClients_clientPolicy_settlement_lawError ordered service.contract
      service.timely timing
      decoded menu (covered source) sample authentic stateUtility deposit
  have settled (state : (serviceApplication service.setup service.mode service.deadline
    service.leaks).ProtocolState)
      (pair : Option (State L service.setup.program.terminalCtx) × (Player → ℝ))
      (member : pair ∈ ((settle state).map fun payoffs =>
        (serviceSourceReadout service.setup service.mode service.deadline service.leaks state,
          payoffs)).support) :
      ∃ charged : Bool, pair.2 who =
        (serviceSourceReadout service.setup service.mode service.deadline service.leaks state).elim
          0
          (fun state => stateUtility state who) - (if charged then deposit who else 0) := by
    rw [PMF.support_map] at member
    obtain ⟨payoffs, drawn, rfl⟩ := member
    change payoffs ∈ ((serviceSourceAudit service.setup service.mode service.deadline service.leaks
      sample
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks state)).map
        (fun verdict who => base state who - if verdict who then deposit who else 0)).support
      at drawn
    rw [PMF.support_map] at drawn
    obtain ⟨verdict, _, rfl⟩ := drawn
    exact ⟨verdict who, rfl⟩
  have bounded : ∀ pair, pair ∈ nativeJoint.support ∨ pair ∈ sourceJoint.support →
      low who ≤ pair.2 who ∧ pair.2 who ≤ low who + range := by
    rintro pair (member | member)
    · obtain ⟨final, _, inner⟩ := Set.mem_iUnion₂.mp (PMF.support_bind .. ▸ member)
      obtain ⟨charged, value⟩ := settled final.state pair inner
      rw [value]
      exact within who _ charged
    · obtain ⟨state, _, rfl⟩ := PMF.support_map .. ▸ member
      simpa only [Option.elim_some, Bool.false_eq_true, ↓reduceIte, sub_zero] using
        within who (some state) false
  have nativeIntegrable : PayoffIntegrable native (fun final => payoff final.state who) := by
    apply payoffIntegrable_of_bounded native _ (C := |low who| + |range|)
    intro final
    have unclear := within who (serviceSourceReadout service.setup service.mode service.deadline
      service.leaks final.state) false
    have charged := within who (serviceSourceReadout service.setup service.mode service.deadline
      service.leaks final.state) true
    simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at unclear charged
    have rate := TerminalAudit.charge_mem_Icc
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample)
        final.state who
    change |base final.state who - TerminalAudit.charge _ _ final.state who * deposit who| ≤ _
    change low who ≤ base final.state who ∧ base final.state who ≤ low who + range at unclear
    change low who ≤ base final.state who - deposit who ∧
      base final.state who - deposit who ≤ low who + range at charged
    obtain ⟨zero, one⟩ := rate
    have lower : low who ≤ base final.state who -
        TerminalAudit.charge ((serviceRuntime service.setup service.mode
          service.deadline).serviceAuditObservation service.leaks)
          (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample)
            final.state who *
            deposit who := by
      have first := mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr unclear.1)
      have second := mul_nonneg zero (sub_nonneg.mpr charged.1)
      linarith
    have upper : base final.state who -
        TerminalAudit.charge ((serviceRuntime service.setup service.mode
          service.deadline).serviceAuditObservation service.leaks)
          (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample)
            final.state who * deposit who ≤
          low who + range := by
      have first := mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr unclear.2)
      have second := mul_nonneg zero (sub_nonneg.mpr charged.2)
      linarith
    rw [abs_le]
    constructor <;> linarith [neg_abs_le (low who), le_abs_self range, abs_nonneg range,
      le_abs_self (low who)]
  have jointIntegrable : PayoffIntegrable nativeJoint (fun pair => pair.2 who) :=
    payoffIntegrable_of_bounded_on_support nativeJoint _ (C := |low who| + |range|)
      fun pair member => by
        obtain ⟨lower, upper⟩ := bounded pair (Or.inl member)
        rw [abs_le]
        constructor <;> linarith [neg_abs_le (low who), le_abs_self range, abs_nonneg range,
          le_abs_self (low who)]
  have nativeValue : expect native (fun final => payoff final.state who) =
      expect nativeJoint (fun pair => pair.2 who) := by
    rw [expect_bind_tower _ _ _ jointIntegrable]
    apply expect_congr_on_support
    intro final _
    rw [expect_map]
    exact (TerminalAudit.settlement_expect base _ _ deposit final.state who).symm
  have readoutLaw : original.map (fun final => service.setup.protocolReadout final.state) =
      (service.setup.run decoded).map some :=
    service.setup.runBehavioralFrom_readout (CommitmentInterface.values service.setup.program)
      source (instructionCount service.setup.program + 1)
      (service.setup.executionProtocol
        (CommitmentInterface.values service.setup.program)).initHistory
      (Nat.le_refl _)
  have sourceValue :
      expect original sourcePayoff = expect sourceJoint (fun pair => pair.2 who) := by
    have mapped := congrArg (fun law => expect law (fun output =>
      output.elim 0 (fun state => stateUtility state who))) readoutLaw
    simp only [expect_map] at mapped
    refine mapped.trans ?_
    rw [expect_map]
    rfl
  have := service.setup.finite_history
    (sourceService_finiteBindingTypes service.setup service.bounds service.values)
    (CommitmentInterface.values service.setup.program)
  refine ⟨nativeIntegrable, payoffIntegrable_of_finite _ _, ?_, ?_⟩
  · rw [nativeValue, sourceValue]
    exact close.expect_sub_le _ (low who) range bounded
  · rw [nativeValue, sourceValue]
    exact close.symm.expect_sub_le _ (low who) range fun pair member =>
      bounded pair member.symm

/-- **Reflection of approximate Nash under an arbitrary contract builder.**
Under the asynchronous contract, if the turn-counted clients of a source profile
are an `ε`-Nash equilibrium of an admitting response menu, for the audited
payoff with any deposit, then the source profile is an `(ε + 2 * δ * R)`-Nash
equilibrium of the source protocol model, where `δ` is the total deferral
weight of the turn timing and every realized payoff value, charged or not,
lies in an interval of length `R`. -/
theorem isεNash_of_clientProfile {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.deadline
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
    IsεNash ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile menu timing source) →
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * (∑ event, timing.deferral event) * range) source := by
  intro base payoff native
  rw [isεNash_iff] at native ⊢
  intro who alternative
  obtain ⟨_, _, compared⟩ :=
    native who (service.clientProfile menu timing (Profile.update source who alternative) who)
  rw [service.clientProfile_update] at compared
  obtain ⟨honestNative, honestSource, honestAbove, honestBelow⟩ :=
    service.clientProfile_value_close ordered
    parameter utility sample authentic deposit menu timing covered low range within source who
  obtain ⟨deviationNative, deviationSource, deviationAbove, deviationBelow⟩ :=
    service.clientProfile_value_close ordered parameter utility sample authentic deposit menu
      timing
      covered low range within (Profile.update source who alternative) who
  let nativeUtility := fun (history : (menu.protocol (serviceInitialLaw service.setup service.mode)
    service.horizon
      service.scheduler).History) (who : Player) => payoff history.state who
  let sourceUtility := fun (final : (service.setup.executionProtocol
      (CommitmentInterface.values service.setup.program)).History) (who : Player) =>
    (service.setup.protocolReadout final.state).elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who)
  have honestNative' : UtilityIntegrable nativeUtility who
      ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).runBehavioral
        (service.clientProfile menu timing source) (2 * service.horizon + 1)) := honestNative
  have deviationNative' : UtilityIntegrable nativeUtility who
      ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).runBehavioral
        (service.clientProfile menu timing (Profile.update source who alternative))
          (2 * service.horizon + 1)) := deviationNative
  have honestSource' : UtilityIntegrable sourceUtility who
      (service.sourceModel.runBehavioral source (instructionCount service.setup.program + 1)) :=
    honestSource
  have deviationSource' : UtilityIntegrable sourceUtility who
      (service.sourceModel.runBehavioral (Profile.update source who alternative)
        (instructionCount service.setup.program + 1)) := deviationSource
  change extendedExpectedUtility nativeUtility who _ ≤
    extendedExpectedUtility nativeUtility who _ + _
    at compared
  rw [extendedExpectedUtility_eq deviationNative', extendedExpectedUtility_eq honestNative',
    ← EReal.coe_add, EReal.coe_le_coe_iff] at compared
  refine ⟨honestSource'.hasExpectation, deviationSource'.hasExpectation, ?_⟩
  change extendedExpectedUtility sourceUtility who _ ≤
    extendedExpectedUtility sourceUtility who _ + _
  rw [extendedExpectedUtility_eq deviationSource', extendedExpectedUtility_eq honestSource',
    ← EReal.coe_add, EReal.coe_le_coe_iff]
  change expect _ _ ≤ expect _ _ + _ at compared
  change expect _ _ ≤ expect _ _ + _
  linarith

omit [Fintype Player] in
/-- Every audited payoff value lies in the interval containing every realized
payoff value, charged or not. -/
private theorem auditedPayoff_within {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (deposit : Player → ℝ) (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range)
    (state : (serviceApplication service.setup service.mode service.deadline
      service.leaks).ProtocolState) (who : Player) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    low who ≤ payoff state who ∧ payoff state who ≤ low who + range := by
  intro base payoff
  have unclear := within who (serviceSourceReadout service.setup service.mode service.deadline
    service.leaks state) false
  have charged := within who (serviceSourceReadout service.setup service.mode service.deadline
    service.leaks state) true
  simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at unclear charged
  have rate := TerminalAudit.charge_mem_Icc
    ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
      service.leaks)
    (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) state who
  change low who ≤ base state who ∧ base state who ≤ low who + range at unclear
  change low who ≤ base state who - deposit who ∧
    base state who - deposit who ≤ low who + range at charged
  change low who ≤ base state who - TerminalAudit.charge _ _ state who * deposit who ∧
    base state who - TerminalAudit.charge _ _ state who * deposit who ≤ low who + range
  obtain ⟨zero, one⟩ := rate
  constructor
  · have first := mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr unclear.1)
    have second := mul_nonneg zero (sub_nonneg.mpr charged.1)
    linarith
  · have first := mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr unclear.2)
    have second := mul_nonneg zero (sub_nonneg.mpr charged.2)
    linarith

/-- **Approximate Nash transfer from the first-turn bound.** Under the
asynchronous contract, suppose every native policy of one player against the
first-turn clients of a source profile has audited expected payoff at most that
of some source deviation of the same player. Then, if the source profile is an
`ε`-Nash equilibrium of the source protocol model, its turn-counted clients are
an `(ε + 2 * δ * R)`-Nash equilibrium of every admitting response menu, where `δ`
is the total deferral weight of the turn timing and every realized payoff
value, charged or not, lies in an interval of length `R`. The turn-counted
clients against a deviation are within `δ` of the first-turn clients against it
in total variation (`Vegas.deviatedTurnProfile_roundsFrom_bind_within`). -/
theorem isεNash_clientProfile_of_firstTurn_bounds {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (serviceApplication service.setup service.mode service.deadline
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
    let clients := sourceServiceClientProfile service.setup
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source)
    (∀ who (alternative : (serviceApplication service.setup service.mode service.deadline
      service.leaks).Policy),
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
            (fun state => utility (service.setup.parameterOutcome parameter state) who))) →
    IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash ((menu.information (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * range)
        (service.clientProfile menu timing source) := by
  intro base payoff clients firstTurn equilibrium
  classical
  let app := serviceApplication service.setup service.mode service.deadline service.leaks
  let model := menu.information (serviceInitialLaw service.setup service.mode) service.horizon
    service.scheduler
  let sourceUtility := fun (final : (service.setup.executionProtocol
      (CommitmentInterface.values service.setup.program)).History) (who : Player) =>
    (service.setup.protocolReadout final.state).elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who)
  let nativeUtility := fun (history : (menu.protocol (serviceInitialLaw service.setup service.mode)
    service.horizon
      service.scheduler).History) (who : Player) => payoff history.state who
  have bounded : ∀ state who, |payoff state who| ≤ |low who| + |range| := by
    intro state who
    obtain ⟨lower, upper⟩ := service.auditedPayoff_within parameter utility sample deposit low
      range within state who
    exact abs_le.mpr ⟨by linarith [neg_abs_le (low who), abs_nonneg range],
      by linarith [le_abs_self (low who), le_abs_self range]⟩
  rw [isεNash_iff] at equilibrium ⊢
  intro who replacement
  let alternative := app.decodePolicy (menu.embedPolicy (serviceInitialLaw service.setup
    service.mode)
    service.horizon service.scheduler who replacement)
  let players := Function.update (serviceClientPolicy service.setup service.mode service.deadline
    service.leaks
    service.bound turns timing clients) who alternative
  let turnPlayers := deviatedTurnProfile service.bound turns timing clients who alternative
  have completed : app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler
    players
      service.horizon =
      app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler turnPlayers
        service.horizon :=
    sourceServiceClientPolicy_deviation_roundsFrom service.scheduler service.bound turns timing
      clients who alternative service.horizon
  have admissible : ∀ player, menu.Admissible (serviceInitialLaw service.setup service.mode)
    service.horizon
      service.scheduler player (players player) := by
    intro player
    by_cases same : player = who
    · subst same
      intro control _ _ action member
      simp only [players, Function.update_self] at member
      exact menu.decode_embedPolicy_covered (serviceInitialLaw service.setup service.mode)
        service.horizon
        service.scheduler player replacement _ _ action member
    · simp only [players, Function.update_of_ne same]
      exact covered source player
  have restricted : (fun player => menu.restrictPolicy (serviceInitialLaw service.setup
    service.mode)
      service.horizon service.scheduler player (players player)) =
      Profile.update (service.clientProfile menu timing source) who replacement := by
    funext player
    by_cases same : player = who
    · subst same
      simp only [players, Function.update_self, Profile.update]
      exact menu.restrict_decode_embedPolicy (serviceInitialLaw service.setup service.mode)
        service.horizon
        service.scheduler player replacement
    · simp only [players, Function.update_of_ne same, Profile.update]
      rfl
  have physical := menu.run_restrict_eq_finish (serviceInitialLaw service.setup service.mode)
    service.horizon
    service.scheduler players admissible (2 * service.horizon + 1)
    (menu.protocol (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler).initHistory le_rfl
  rw [restricted] at physical
  have deviationLaw : (model.runBehavioral
      (Profile.update (service.clientProfile menu timing source) who replacement)
      (2 * service.horizon + 1)).map History.state =
      (app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler players
        service.horizon).map app.finished := by
    refine physical.trans ?_
    unfold ReactiveApplication.roundsFrom
    simp only [ReactiveApplication.finish, PMF.map_bind]
    rfl
  rw [completed] at deviationLaw
  -- The turn-counted and first-turn deviations are close.
  have coupled := deviatedTurnProfile_roundsFrom_bind_within
    (serviceInitialLaw service.setup service.mode) service.scheduler service.horizon service.bound
    timing clients who alternative (fun execution => PMF.pure execution)
  simp only [PMF.bind_pure] at coupled
  let limit := deviatedTurnProfile service.bound turns (firstTurnTiming service.setup turns
    service.mode)
    clients who alternative
  have deviationGap : expect (app.roundsFrom (serviceInitialLaw service.setup service.mode)
    service.scheduler
        turnPlayers service.horizon) (fun execution => payoff (app.finished execution) who) -
      expect (app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler limit
        service.horizon)
        (fun execution => payoff (app.finished execution) who) ≤
      (∑ event, timing.deferral event) * range :=
    coupled.expect_sub_le (fun execution => payoff (app.finished execution) who)
      (low who) range (fun execution _ => service.auditedPayoff_within parameter utility sample
        deposit low range within _ who)
  obtain ⟨deviation, firstBound⟩ := firstTurn who alternative
  rw [expect_map] at firstBound
  have firstBound' : expect (app.roundsFrom (serviceInitialLaw service.setup service.mode)
    service.scheduler limit
        service.horizon) (fun execution => payoff (app.finished execution) who) ≤
      expect (service.sourceModel.runBehavioral (Profile.update source who deviation)
        (instructionCount service.setup.program + 1)) (fun final => sourceUtility final who) :=
    firstBound
  obtain ⟨sourceHonest, sourceDeviation, sourceCompared⟩ := equilibrium who deviation
  -- Honest closeness.
  have honestClose := service.clientProfile_value_close ordered parameter utility sample
    authentic
    deposit menu timing covered low range within source who
  obtain ⟨honestIntegrable, sourceIntegrable, _, honestBelow⟩ := honestClose
  have finiteHistory := service.setup.finite_history
    (sourceService_finiteBindingTypes service.setup service.bounds service.values)
    (CommitmentInterface.values service.setup.program)
  have deviationIntegrable : UtilityIntegrable sourceUtility who
      (service.sourceModel.runBehavioral (Profile.update source who deviation)
        (instructionCount service.setup.program + 1)) := payoffIntegrable_of_finite _ _
  have sourceIntegrable' : UtilityIntegrable sourceUtility who
      (service.sourceModel.runBehavioral source (instructionCount service.setup.program + 1)) :=
    sourceIntegrable
  change extendedExpectedUtility sourceUtility who _ ≤
    extendedExpectedUtility sourceUtility who _ + _ at sourceCompared
  rw [extendedExpectedUtility_eq deviationIntegrable, extendedExpectedUtility_eq sourceIntegrable',
    ← EReal.coe_add, EReal.coe_le_coe_iff] at sourceCompared
  have nativeDeviationIntegrable : UtilityIntegrable nativeUtility who
      (model.runBehavioral (Profile.update (service.clientProfile menu timing source) who
        replacement) (2 * service.horizon + 1)) :=
    payoffIntegrable_of_bounded _ _ (C := |low who| + |range|) fun history =>
      bounded history.state who
  have nativeHonestIntegrable : UtilityIntegrable nativeUtility who
      (model.runBehavioral (service.clientProfile menu timing source)
        (2 * service.horizon + 1)) := honestIntegrable
  refine ⟨nativeHonestIntegrable.hasExpectation, nativeDeviationIntegrable.hasExpectation, ?_⟩
  change extendedExpectedUtility nativeUtility who _ ≤
    extendedExpectedUtility nativeUtility who _ + _
  rw [extendedExpectedUtility_eq nativeDeviationIntegrable,
    extendedExpectedUtility_eq nativeHonestIntegrable, ← EReal.coe_add, EReal.coe_le_coe_iff]
  have deviationValue : expectedUtility nativeUtility who
      (model.runBehavioral (Profile.update (service.clientProfile menu timing source) who
        replacement) (2 * service.horizon + 1)) =
      expect (app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler
        turnPlayers
        service.horizon) (fun execution => payoff (app.finished execution) who) := by
    unfold expectedUtility
    have mapped := congrArg (fun law => expect law (fun state => payoff state who)) deviationLaw
    simp only [expect_map] at mapped
    exact mapped
  change expect _ _ - expect _ _ ≤ _ at honestBelow
  change expect (service.sourceModel.runBehavioral source _) (fun final => sourceUtility final who)
    - expect (model.runBehavioral (service.clientProfile menu timing source) _)
      (fun history => nativeUtility history who) ≤ _ at honestBelow
  change expectedUtility nativeUtility who _ ≤ expectedUtility nativeUtility who _ + _
  rw [deviationValue]
  unfold expectedUtility
  change expect _ (fun final => sourceUtility final who) ≤
    expect _ (fun final => sourceUtility final who) + ε at sourceCompared
  linarith

end AsyncServiceSpec


end Vegas
