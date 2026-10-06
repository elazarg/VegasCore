/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceSpec
import Vegas.Game.SourceServiceTurnSettlement
import GameTheory.Core.Approximate

/-! # Reflection of approximate Nash under an arbitrary contract builder

For a full-source service whose public scheduler satisfies the asynchronous
contract, the turn-counted clients of a source profile
(`Vegas.AsyncServiceSpec.clientProfile`) are played in an arbitrary response
menu that admits them. Their joint law of typed outcome and realized
settlement is within the total deferral weight `δ` of the source law in total
variation (`Vegas.sourceServiceClients_settlement_lawError`). When every
realized payoff value lies in an interval of length `R`, expected payoffs are
within `δ * R`. Each player's client depends only on its own source policy, so
a compiled source deviation is a native deviation, and a native `ε`-Nash
equilibrium of the clients reflects to a source `(ε + 2 * δ * R)`-Nash
equilibrium (`Vegas.AsyncServiceSpec.isεNash_of_clientProfile`).
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
policy. -/
def clientProfile (menu : (application service.setup service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns)
    (source : Profile service.sourceModel.behavioralSignature) :
    Profile (menu.information (initialLaw service.setup) service.horizon
      service.scheduler).behavioralSignature := fun who =>
  menu.restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
    (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing
      (sourceServiceClientProfile service.setup
        (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
          source)) who)

omit [Fintype Player] in
private theorem turnPolicy_congr {turns : Nat} (timing : TurnTiming service.setup turns)
    (profile other : BehavioralProfile service.setup.program) (who : Player)
    (same : profile who = other who) :
    sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing profile who =
      sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing other who := by
  unfold sourceServiceTurnPolicy sourceServiceTurnFamily sourceServiceCanonicalOpportunity
    sourceServiceCanonicalPolicy compileEventProfile
  rw [same]

omit [Fintype Player] in
/-- Each player's client depends only on its own source policy. -/
theorem clientProfile_congr (menu : (application service.setup service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns)
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
  exact congrArg (menu.restrictPolicy (initialLaw service.setup) service.horizon
    service.scheduler who) (turnPolicy_congr service timing _ _ who decoded)

omit [Fintype Player] in
/-- The clients of a unilateral source deviation are a unilateral deviation of
the clients. -/
theorem clientProfile_update (menu : (application service.setup service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns)
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
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (application service.setup service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns)
    (covered : ∀ (source : Profile service.sourceModel.behavioralSignature) who,
      menu.Admissible (initialLaw service.setup) service.horizon service.scheduler who
        (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing
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
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    let native := (menu.information (initialLaw service.setup) service.horizon
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
    ((runtime service.setup).serviceAuditObservation service.leaks)
    (sourceServiceAudit service.setup service.leaks sample) deposit
  let decoded := service.setup.decodeBehavioralProfile
    (CommitmentInterface.values service.setup.program) source
  let stateUtility := fun state : State L service.setup.program.terminalCtx =>
    utility (service.setup.parameterOutcome parameter state)
  let nativeJoint := native.bind fun final =>
    (settle final.state).map fun payoffs =>
      (sourceReadout service.setup service.leaks final.state, payoffs)
  let sourceJoint := (service.setup.run decoded).map fun state =>
    (some state, stateUtility state)
  have close : PMF.WithinTV (∑ event, timing.deferral event) nativeJoint sourceJoint :=
    sourceServiceClients_settlement_lawError service.contract service.timely timing decoded menu
      (covered source) sample authentic stateUtility deposit
  have settled (state : (application service.setup service.leaks).ProtocolState)
      (pair : Option (State L service.setup.program.terminalCtx) × (Player → ℝ))
      (member : pair ∈ ((settle state).map fun payoffs =>
        (sourceReadout service.setup service.leaks state, payoffs)).support) :
      ∃ charged : Bool, pair.2 who =
        (sourceReadout service.setup service.leaks state).elim 0
          (fun state => stateUtility state who) - (if charged then deposit who else 0) := by
    rw [PMF.support_map] at member
    obtain ⟨payoffs, drawn, rfl⟩ := member
    change payoffs ∈ ((sourceServiceAudit service.setup service.leaks sample
      ((runtime service.setup).serviceAuditObservation service.leaks state)).map
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
    have unclear := within who (sourceReadout service.setup service.leaks final.state) false
    have charged := within who (sourceReadout service.setup service.leaks final.state) true
    simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] at unclear charged
    have rate := TerminalAudit.charge_mem_Icc
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) final.state who
    change |base final.state who - TerminalAudit.charge _ _ final.state who * deposit who| ≤ _
    change low who ≤ base final.state who ∧ base final.state who ≤ low who + range at unclear
    change low who ≤ base final.state who - deposit who ∧
      base final.state who - deposit who ≤ low who + range at charged
    obtain ⟨zero, one⟩ := rate
    have lower : low who ≤ base final.state who -
        TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) final.state who *
            deposit who := by
      have first := mul_nonneg (sub_nonneg.mpr one) (sub_nonneg.mpr unclear.1)
      have second := mul_nonneg zero (sub_nonneg.mpr charged.1)
      linarith
    have upper : base final.state who -
        TerminalAudit.charge ((runtime service.setup).serviceAuditObservation service.leaks)
          (sourceServiceAudit service.setup service.leaks sample) final.state who * deposit who ≤
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
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (menu : (application service.setup service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns)
    (covered : ∀ (source : Profile service.sourceModel.behavioralSignature) who,
      menu.Admissible (initialLaw service.setup) service.horizon service.scheduler who
        (sourceServiceTurnPolicy service.setup service.leaks service.bound turns timing
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
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    IsεNash ((menu.information (initialLaw service.setup) service.horizon
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
  obtain ⟨honestNative, honestSource, honestAbove, honestBelow⟩ := service.clientProfile_value_close
    parameter utility sample authentic deposit menu timing covered low range within source who
  obtain ⟨deviationNative, deviationSource, deviationAbove, deviationBelow⟩ :=
    service.clientProfile_value_close parameter utility sample authentic deposit menu timing
      covered low range within (Profile.update source who alternative) who
  let nativeUtility := fun (history : (menu.protocol (initialLaw service.setup) service.horizon
      service.scheduler).History) (who : Player) => payoff history.state who
  let sourceUtility := fun (final : (service.setup.executionProtocol
      (CommitmentInterface.values service.setup.program)).History) (who : Player) =>
    (service.setup.protocolReadout final.state).elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who)
  have honestNative' : UtilityIntegrable nativeUtility who
      ((menu.information (initialLaw service.setup) service.horizon service.scheduler).runBehavioral
        (service.clientProfile menu timing source) (2 * service.horizon + 1)) := honestNative
  have deviationNative' : UtilityIntegrable nativeUtility who
      ((menu.information (initialLaw service.setup) service.horizon service.scheduler).runBehavioral
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

end AsyncServiceSpec

end Vegas
