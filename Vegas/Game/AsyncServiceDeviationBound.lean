/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.IntendedAsyncNash
import Vegas.Game.AsyncDeviationReadout
import Vegas.Game.SourceServiceChoiceSupport
import GameTheory.Math.Probability.ExpectationMap
import GameTheory.Math.Probability.ExpectationAlgebra
import Vegas.Source.ValueBindingAdmission
import Vegas.Source.BindingNormalization

/-! # The first-turn deviation bound under an arbitrary contract builder

Against the first-turn clients of a source profile, under a scheduler
satisfying the asynchronous contract, every native policy of one player has the
typed outcome law of a source deviation that may bind failure
(`Vegas.asyncDeviation_readout_law`). Binding failure buys a pure policy
nothing when its value-binding normalization preserves the joint initial
parameter and public-default outcome law. Every policy
is a mixture of pure ones (`Vegas.SourceProgram.exists_pureMixture_run`). With a
nonnegative deposit, audit charges only lower the realized payoff. Hence every
native policy against the first-turn clients has audited expected payoff at
most that of a source deviation of the same player
(`Vegas.AsyncServiceSpec.firstTurn_deviation_bound`).

This discharges the hypothesis of
`Vegas.AsyncServiceSpec.isεBestResponse_clientProfile_of_firstTurn_bounds`: for every
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



namespace AsyncServiceSpec

variable [Finite Player] (service : AsyncServiceSpec Player L)
  (admission : CommitmentInterface service.setup.program)

/-- **The first-turn deviation bound.** Under the asynchronous contract, for
every authentic audit and every nonnegative deposit, every native policy of
one player against the first-turn clients of a source profile has audited
expected payoff at most that of some source deviation of the same player. Its
typed outcome law is that of a source deviation whose bindings may fail
(`Vegas.asyncDeviation_readout_law`); failure buys nothing, and charges only
lower the payoff. Finite actual source support supplies integrability without a
uniform utility bound. -/
theorem firstTurn_deviation_bound {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    {turns : Nat} (source : Profile (service.sourceModel admission).behavioralSignature)
    (who : Player)
    (alternative : (serviceApplication service.setup service.mode service.duration
      service.leaks).Policy) :
    let base := serviceBaseUtility service.setup service.mode service.duration service.leaks
      (fun config => utility (service.setup.parameterOutcome parameter config))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    let clients := normalizeDisclosureProfile service.setup.program
      (service.setup.decodeBehavioralProfile admission source)
    ∃ deviation : (service.sourceModel admission).BehavioralPolicy who,
      expect (((serviceApplication service.setup service.mode service.duration
        service.leaks).roundsFrom (serviceInitialLaw service.setup service.mode)
          service.scheduler (Function.update (serviceTurnPolicy service.setup service.mode
            service.duration service.leaks service.bound turns
            (firstTurnTiming service.setup turns service.mode) clients) who alternative)
          service.horizon).map (serviceApplication service.setup service.mode service.duration
            service.leaks).finished)
        (fun final => payoff final who) ≤
      expect ((service.sourceModel admission).runBehavioral (Profile.update source who deviation)
        (instructionCount service.setup.program + 1))
        (fun final => (service.setup.protocolReadout final.state).elim 0
          (fun config => utility (service.setup.parameterOutcome parameter config) who)) := by
  let : Fintype Player := Fintype.ofFinite Player
  intro base payoff clients
  classical
  let app := serviceApplication service.setup service.mode service.duration service.leaks
  let decoded := service.setup.decodeBehavioralProfile admission source
  let value := fun outcome : Option (Config Player L service.setup.program.terminalCtx) =>
    outcome.elim 0 (fun config => utility (service.setup.parameterOutcome parameter config) who)
  let pairValue := fun outcome : Option (State L service.setup.program.terminalCtx ×
      DefaultHistory Player) => outcome.elim 0 fun result =>
    utility (parameter (initialState service.setup.program result.1),
      ⟨sourcePublicEnv result.1, result.2⟩) who
  let readPair := fun final : app.ProtocolState =>
    (serviceSourceReadout service.setup service.mode service.duration service.leaks final).map
      (fun config => (config.state, config.defaults))
  let native := ((app.roundsFrom (serviceInitialLaw service.setup service.mode) service.scheduler
    (Function.update (serviceTurnPolicy service.setup service.mode service.duration service.leaks
      service.bound turns (firstTurnTiming service.setup turns service.mode) clients) who
      alternative) service.horizon).map app.finished)
  obtain ⟨policy, law⟩ := asyncDeviation_readout_law service.setup service.leaks ordered
    service.contract service.timely turns decoded who alternative
  let original := service.setup.run (Function.update decoded who policy)
  have nativeLaw : native.map readPair =
      original.map (fun config => some (config.state, config.defaults)) := by
    simpa only [native, readPair, original, decoded, clients, PMF.map_comp, Function.comp_def]
      using law
  have finite : service.setup.program.FiniteBindingTypes :=
    sourceService_finiteBindingTypes service.setup service.bounds service.values
  have sourceIntegrable : PayoffIntegrable original
      (fun config => utility (service.setup.parameterOutcome parameter config) who) :=
    payoffIntegrable_of_finite_support _ _ (service.setup.run_support_finite _
      (FiniteBindingTypes.profileFiniteSupport service.setup.program finite _))
  have mappedIntegrable : PayoffIntegrable (native.map readPair) pairValue := by
    rw [nativeLaw]
    apply (payoffIntegrable_map_iff _ _ _).2
    simpa only [pairValue, Function.comp_def, Option.elim_some, Setup.parameterOutcome,
      publicOutcome] using sourceIntegrable
  have baseValue : (fun final => base final who) = pairValue ∘ readPair := by
    funext final
    dsimp only [base, serviceBaseUtility, pairValue, readPair, Function.comp_def]
    cases serviceSourceReadout service.setup service.mode service.duration service.leaks final <;>
      rfl
  have baseIntegrable : PayoffIntegrable native (fun final => base final who) := by
    rw [baseValue]
    exact (payoffIntegrable_map_iff readPair native pairValue).1 mappedIntegrable
  have chargeIntegrable : PayoffIntegrable native (fun final =>
      TerminalAudit.charge
        ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
          service.leaks)
        (serviceSourceAudit service.setup service.mode service.duration service.leaks sample)
        final who * deposit who) := by
    simpa only [mul_comm] using payoffIntegrable_const_mul (c := deposit who)
      (TerminalAudit.payoffIntegrable_charge native
        ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
          service.leaks)
        (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) who)
  have charged : expect native (fun final => payoff final who) ≤
      expect native (fun final => base final who) := by
    apply expect_mono _ (payoffIntegrable_sub baseIntegrable chargeIntegrable) baseIntegrable
    intro final _
    exact sub_le_self _ (mul_nonneg (TerminalAudit.charge_mem_Icc _ _ final who).1
      (nonnegative who))
  have nativeValue : expect native (fun final => base final who) =
      expect original (fun config => utility (service.setup.parameterOutcome parameter config)
        who) := by
    rw [baseValue]
    have mapped := congrArg (fun distribution => expect distribution pairValue) nativeLaw
    simpa only [expect_map, Function.comp_def, pairValue, Option.elim_some,
      Setup.parameterOutcome, publicOutcome] using mapped
  obtain ⟨better, valueBinding, improved⟩ :=
    service.setup.exists_valueBinding_parameter_expect_ge finite parameter
      (fun outcome => utility outcome who) decoded who policy
  have allowed : better.Admitted service.setup.program admission :=
    BehavioralPolicy.admitted_of_valueBinding service.setup.program better valueBinding admission
  refine ⟨(service.setup.behavioralPolicyEquiv admission who) ⟨better, allowed⟩, ?_⟩
  have readout : ((service.sourceModel admission).runBehavioral (Profile.update source who
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
    _ = _ := nativeValue
    _ ≤ _ := improved
    _ = _ := by
      rw [sourceValue]
      rfl


/-- **Approximate Nash transfer under an arbitrary contract builder.** Under the
asynchronous contract, for every authentic audit and every nonnegative deposit,
if a source profile is an `ε`-Nash equilibrium of the source protocol model,
its turn-counted clients are an `(ε + 2 * δ * R)`-Nash equilibrium of every
response menu that admits every profile's clients, for the audited payoff. Here
`δ` is the product deferral error of the turn timing and every realized payoff
value, charged or not, lies in an interval of length `R`. -/
theorem isεNash_clientProfile {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (menu : (serviceApplication service.setup service.mode service.duration
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel admission).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing
          (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
            admission source)) who))
    (low : Player → ℝ) (range : ℝ)
    (within : service.SettlementRange parameter utility sample deposit low (fun _ => range))
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.duration service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash (service.gameForm menu)
        (fun history who => payoff history.state who)
        (ε + 2 * timing.deferralError * range)
        (service.clientProfile admission menu timing source) := by
  let : Fintype Player := Fintype.ofFinite Player
  intro base payoff equilibrium
  apply (isεNash_iff_εBestResponse _ _).mpr
  exact service.isεBestResponse_clientProfile_of_firstTurn_bounds admission parameter utility sample
    authentic deposit menu timing covered low (fun _ => range) within ε source
    (firstTurn_readout_law service.setup service.leaks ordered service.contract service.timely
      turns _ (fun _ => BehavioralPolicy.normalizeDisclosures_authentic _ _))
    (fun who alternative => service.firstTurn_deviation_bound admission ordered
      parameter utility sample deposit
      nonnegative source who alternative) equilibrium

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
    (menu : (serviceApplication service.setup service.mode service.duration
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel admission).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing
          (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
            admission source)) who))
    (low : Player → ℝ) (range : ℝ)
    (within : service.SettlementRange parameter utility sample deposit low (fun _ => range))
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.duration service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    (IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash (service.gameForm menu)
        (fun history who => payoff history.state who)
        (ε + 2 * timing.deferralError * range)
        (service.clientProfile admission menu timing source)) ∧
    (IsεNash (service.gameForm menu)
        (fun history who => payoff history.state who) ε
        (service.clientProfile admission menu timing source) →
      IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * timing.deferralError * range) source) :=
  ⟨service.isεNash_clientProfile admission ordered parameter utility sample authentic deposit
    nonnegative menu
      timing covered low range within ε source,
    fun native => (isεNash_iff_εBestResponse _ _).mpr
      (service.isεBestResponse_of_clientProfile admission ordered parameter utility sample authentic
        deposit menu timing covered low (fun _ => range) within ε source native)⟩

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
    (forfeit : ℝ)
    (range : service.setup.TerminalPayoffSpread (CommitmentInterface.values
      service.setup.program) parameter utility forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (menu : (serviceApplication service.setup service.mode service.duration
      service.leaks).ResponseMenu)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (covered : ∀ (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature) who,
      menu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
        service.scheduler who
        (serviceClientPolicy service.setup service.mode service.duration service.leaks
          service.bound turns timing
          (normalizeDisclosureProfile service.setup.program (service.setup.decodeBehavioralProfile
            (CommitmentInterface.values service.setup.program) source)) who))
    (low : Player → ℝ) (spread : ℝ)
    (within : service.SettlementRange parameter
      (forfeitUtility service.setup.program forfeit utility) sample deposit low (fun _ => spread))
    (intended : Profile service.setup.intendedModel.behavioralSignature)
    (source : Profile (service.sourceModel (CommitmentInterface.values
      service.setup.program)).behavioralSignature)
    (agrees : (service.setup.intendedRestriction (CommitmentInterface.values
      service.setup.program)).ExtendsProfile intended source) (ε : ℝ)
    (equilibrium : IsεNash (service.setup.intendedModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
      (fun final who => (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)) ε
      intended) :
    let forfeited := forfeitUtility service.setup.program forfeit utility
    let base := serviceBaseUtility service.setup service.mode service.duration service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((serviceAuditObservation (serviceTimeouts service.setup service.mode service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.duration service.leaks sample) deposit
    IsεNash (service.gameForm menu)
        (fun history who => payoff history.state who)
        (ε + 2 * timing.deferralError * spread)
        (service.clientProfile (CommitmentInterface.values service.setup.program) menu timing
          source) ∧
      PMF.WithinTV timing.deferralError
        ((service.run menu (service.clientProfile (CommitmentInterface.values
            service.setup.program) menu timing source)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                ((serviceSourceReadout service.setup service.mode service.duration service.leaks
                  final.state).map (fun config => (config.state, config.defaults)), payoffs)))
        ((service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => ((service.setup.protocolReadout final.state).map
              (fun config => (config.state, config.defaults)),
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) :=
  service.intended_clientProfile_isεNash_of_firstTurn_bounds wellFormed parameter
    utility forfeit
    range sample authentic deposit menu timing covered low spread within intended source agrees
    (firstTurn_readout_law service.setup service.leaks ordered service.contract service.timely
      turns _ (fun _ => BehavioralPolicy.normalizeDisclosures_authentic _ _)) ε
    equilibrium (fun who alternative => service.firstTurn_deviation_bound
      (CommitmentInterface.values service.setup.program)
      ordered parameter (forfeitUtility service.setup.program forfeit utility)
      sample deposit nonnegative source who alternative)

end AsyncServiceSpec

end Vegas
