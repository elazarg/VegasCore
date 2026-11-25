module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Interaction.ReactiveFiniteAssessment
public import Vegas.Game.AsyncServiceDeviationBound
public import Vegas.Game.SourceServiceTurnSettlement

@[expose] public section

/-! # Approximate Nash correspondence on the bounded raw ledger

The source commitment interface may independently admit failed binding choices
at each site. The bounded raw response menu (`Vegas.AsyncServiceSpec.rawMenu`) admits every
native response within the service's message bounds, including every packet
error. It admits the turn-counted clients of every source profile
(`Vegas.AsyncServiceSpec.rawMenu_admits`): each client completes its
turn-counted policy by silence after its own off-policy responses
(`Vegas.serviceClientPolicy`), and on every bounded raw history where its
own responses follow that policy, its canonical decisions fit the bounds
(`Vegas.sourceServiceClientPolicy_raw_admissible`). This uses only the
service's own fields: binding-value coverage, initial candidate values and
candidate capacity.

Hence the approximate Nash correspondence and its intended end-to-end form hold
on the audited bounded raw ledger for every contract builder, with no
admissibility premise (`Vegas.AsyncServiceSpec.isεNash_rawClientProfile_approximate`,
`Vegas.AsyncServiceSpec.intended_rawClientProfile_isεNash`). With the first-turn
timing the deferral weight is zero and the correspondence is exact, with the
same `ε` (`Vegas.AsyncServiceSpec.isεNash_firstTurnClientProfile_iff`,
`Vegas.AsyncServiceSpec.intended_firstTurnClientProfile_isεNash`).
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
  (admission : CommitmentInterface service.setup.program)


theorem isεNash_rawClientProfile_approximate {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.setup.informationDependencies) →
      PMF (List (SettledEvidence service.setup service.setup.informationDependencies)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    {turns : Nat} (timing : TurnTiming service.setup turns service.setup.informationDependencies)
    (low : Player → ℝ) (range : ℝ)
    (within : service.SettlementRange parameter utility sample deposit low (fun _ => range))
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.setup.informationDependencies
      service.duration service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup
        service.setup.informationDependencies service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.setup.informationDependencies service.duration
        service.leaks sample) deposit
    (IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash (service.gameForm service.rawMenu)
        (fun history who => payoff history.state who)
        (ε + 2 * timing.deferralError * range)
        (service.clientProfile admission service.rawMenu timing source)) ∧
    (IsεNash (service.gameForm service.rawMenu)
        (fun history who => payoff history.state who) ε
        (service.clientProfile admission service.rawMenu timing source) →
      IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * timing.deferralError * range) source) :=
  service.isεNash_clientProfile_approximate admission parameter utility sample authentic
    deposit nonnegative
    service.rawMenu timing (service.rawMenu_admits admission timing) low range within ε source

/-- **Intended approximate Nash equilibria on the bounded raw ledger, for
every contract builder.** For a well-formed setup, a forfeit no smaller than
the payoff range, every authentic audit and every nonnegative deposit, the
turn-counted clients of a source profile extending an `ε`-Nash equilibrium of
the intended game are an `(ε + 2 * δ * R)`-Nash equilibrium of the bounded raw
response menu under the forfeit pass, and their joint law of typed outcome and
realized settlement is within `δ` in total variation of the intended joint law
of typed cells, public default history and payoff. -/
theorem intended_rawClientProfile_isεNash {Parameter : Type}
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ)
    (range : service.setup.TerminalPayoffSpread (CommitmentInterface.values
      service.setup.program) parameter utility forfeit)
    (sample : List (SettledEvidence service.setup service.setup.informationDependencies) →
      PMF (List (SettledEvidence service.setup service.setup.informationDependencies)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    {turns : Nat} (timing : TurnTiming service.setup turns service.setup.informationDependencies)
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
    let base := serviceBaseUtility service.setup service.setup.informationDependencies
      service.duration service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup
        service.setup.informationDependencies service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.setup.informationDependencies service.duration
        service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((serviceAuditObservation (serviceTimeouts service.setup
        service.setup.informationDependencies service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.setup.informationDependencies service.duration
        service.leaks sample) deposit
    IsεNash (service.gameForm service.rawMenu)
        (fun history who => payoff history.state who)
        (ε + 2 * timing.deferralError * spread)
        (service.clientProfile (CommitmentInterface.values service.setup.program) service.rawMenu
          timing source) ∧
      PMF.WithinTV timing.deferralError
        ((service.run service.rawMenu (service.clientProfile (CommitmentInterface.values
            service.setup.program) service.rawMenu timing source)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                ((serviceSourceReadout service.setup service.setup.informationDependencies
                  service.duration service.leaks
                  final.state).map (fun config => (config.state, config.defaults)), payoffs)))
        ((service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => ((service.setup.protocolReadout final.state).map
              (fun config => (config.state, config.defaults)),
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) :=
  service.intended_clientProfile_isεNash wellFormed parameter utility forfeit range
    sample
    authentic deposit nonnegative service.rawMenu timing (service.rawMenu_admits
      (CommitmentInterface.values service.setup.program)
      timing) low
    spread within intended source agrees ε equilibrium

/-- A bounded utility agrees with the supplied utility on every legal history
of both finite games, including histories reached only by a deviation. -/
private theorem exists_bounded_utility {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.setup.informationDependencies) →
      PMF (List (SettledEvidence service.setup service.setup.informationDependencies)))
    (deposit : Player → ℝ) :
    let read := serviceSourceReadout service.setup service.setup.informationDependencies
      service.duration service.leaks
    ∃ (bounded : Parameter × PublicOutcome service.setup.program → Player → ℝ) (bound : ℝ),
      service.SettlementRange parameter bounded sample deposit
        (fun _ => -bound) (fun _ => 2 * bound) ∧
      (∀ (h : (service.setup.executionProtocol admission).History) who,
        (service.setup.protocolReadout h.state).elim 0
          (fun s => bounded (service.setup.parameterOutcome parameter s) who) =
        (service.setup.protocolReadout h.state).elim 0
          (fun s => utility (service.setup.parameterOutcome parameter s) who)) ∧
      ∀ (h : (service.gameForm service.rawMenu).sig.Outcome) who,
        (read h.state).elim 0 (fun s => bounded (service.setup.parameterOutcome parameter s) who) =
        (read h.state).elim 0
          (fun s => utility (service.setup.parameterOutcome parameter s) who) := by
  classical
  intro read
  let source := (service.setup.executionProtocol admission).History
  let ledger := (service.gameForm service.rawMenu).sig.Outcome
  let : Finite source := service.setup.finite_history
    (sourceService_finiteBindingTypes service.setup service.bounds service.values) admission
  let : Finite ledger := ReactiveApplication.ResponseMenu.finite_history _ _ _ _
  let value := fun (config : Option (Config Player L service.setup.program.terminalCtx))
      (who : Player) =>
    config.elim 0 (fun s => utility (service.setup.parameterOutcome parameter s) who)
  let amounts : (source ⊕ ledger ⊕ Unit) × Player → ℝ := fun entry => match entry.1 with
    | .inl h => |value (service.setup.protocolReadout h.state) entry.2|
    | .inr (.inl h) => |value (read h.state) entry.2|
    | .inr (.inr _) => |deposit entry.2|
  obtain ⟨b, hb⟩ := (Set.finite_range amounts).bddAbove
  let cap := max 0 b
  have covers (x) : amounts x ≤ cap := (hb (Set.mem_range_self x)).trans (le_max_right _ _)
  have pos : 0 ≤ cap := le_max_left _ _
  let bounded := fun x who => max (-cap) (min cap (utility x who))
  have agrees (x) (who) (inside : |value x who| ≤ cap) :
      x.elim 0 (fun s => bounded (service.setup.parameterOutcome parameter s) who) =
        value x who := by
    cases x with
    | none => rfl
    | some s =>
      obtain ⟨lo, hi⟩ := abs_le.mp inside
      exact (congrArg (max (-cap)) (min_eq_right hi)).trans (max_eq_right lo)
  refine ⟨bounded, 2 * cap, ?_, fun h who => agrees _ _ (covers (.inl h, who)),
    fun h who => agrees _ _ (covers (.inr (.inl h), who))⟩
  intro control _ payoffs member who
  rw [TerminalAudit.settlement, PMF.support_map] at member
  obtain ⟨verdict, _, rfl⟩ := member
  have pay := abs_le.mp (covers (.inr (.inr ()), who))
  change -cap ≤ deposit who ∧ deposit who ≤ cap at pay
  have baseBound : ∀ x : Option (Config Player L service.setup.program.terminalCtx),
      -cap ≤ x.elim 0 (fun s => bounded (service.setup.parameterOutcome parameter s) who) ∧
      x.elim 0 (fun s => bounded (service.setup.parameterOutcome parameter s) who) ≤ cap := by
    intro x
    cases x with
    | none => simpa using And.intro (neg_nonpos.mpr pos) pos
    | some s => exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩
  specialize baseBound (read (some control))
  change -(2 * cap) ≤ _ - _ ∧ _ - _ ≤ -(2 * cap) + 2 * (2 * cap)
  dsimp only [serviceBaseUtility]
  cases verdict who <;> simp only [Bool.false_eq_true, ↓reduceIte, sub_zero] <;>
    dsimp only [read] at baseBound <;> constructor <;> linarith

/-- **Exact Nash correspondence on the bounded raw ledger, for every contract
builder.** Under the asynchronous contract, for every authentic audit and every
nonnegative deposit, the first-turn clients of a source profile, which make
each source decision at the owner's first opportunity, are an `ε`-Nash
equilibrium of the bounded raw response menu for the audited payoff exactly when
the source profile is an `ε`-Nash equilibrium of the source protocol model, for
every `ε`. Finiteness of the two games suffices for arbitrary real-valued utilities. -/
theorem isεNash_firstTurnClientProfile_iff {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.setup.informationDependencies) →
      PMF (List (SettledEvidence service.setup service.setup.informationDependencies)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (turns : Nat)
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.setup.informationDependencies
      service.duration service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup
        service.setup.informationDependencies service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.setup.informationDependencies service.duration
        service.leaks sample) deposit
    IsεNash (service.gameForm service.rawMenu)
        (fun history who => payoff history.state who) ε
        (service.clientProfile admission service.rawMenu (firstTurnTiming service.setup turns
          service.setup.informationDependencies)
          source) ↔
      IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source := by
  intro base payoff
  obtain ⟨bounded, size, within, sourceEq, ledgerEq⟩ :=
    service.exists_bounded_utility admission parameter utility sample deposit
  have approximate := service.isεNash_rawClientProfile_approximate admission parameter bounded
    sample authentic deposit nonnegative (firstTurnTiming service.setup turns
      service.setup.informationDependencies) (fun _ => -size) (2 * size) within ε source
  simp only [firstTurnTiming_deferralError, mul_zero, zero_mul, add_zero] at approximate
  have ledgerUtilityEq :
      (fun (history : (service.gameForm service.rawMenu).sig.Outcome) who =>
        TerminalAudit.utility
          (serviceBaseUtility service.setup service.setup.informationDependencies service.duration
            service.leaks (fun s => bounded (service.setup.parameterOutcome parameter s)))
          (serviceAuditObservation (serviceTimeouts service.setup
            service.setup.informationDependencies service.duration) service.leaks)
          (serviceSourceAudit service.setup service.setup.informationDependencies
            service.duration service.leaks sample) deposit history.state who) =
        (fun history who => payoff history.state who) := by
    funext history who
    exact congrArg (fun x => x - _) (ledgerEq history who)
  rw [ledgerUtilityEq, (funext fun h => funext (sourceEq h))] at approximate
  exact ⟨approximate.2, approximate.1⟩

/-- Every commitment interface preserves the exact joint law of typed terminal
store and realized settlement when clients act at their first opportunities.
Every admitted binding choice incurs no audit charge on the prescribed execution. -/
theorem firstTurnClientProfile_settlement_distribution {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.setup.informationDependencies) →
      PMF (List (SettledEvidence service.setup service.setup.informationDependencies)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (turns : Nat)
    (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.setup.informationDependencies
      service.duration service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let settle := TerminalAudit.settlement base
      ((serviceAuditObservation (serviceTimeouts service.setup
        service.setup.informationDependencies service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.setup.informationDependencies service.duration
        service.leaks sample) deposit
    ((service.run service.rawMenu
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.setup.informationDependencies) source)).bind
          fun final =>
        (settle final.state).map fun payoffs =>
          ((serviceSourceReadout service.setup service.setup.informationDependencies
            service.duration service.leaks
            final.state).map (fun config => (config.state, config.defaults)), payoffs)) =
      (service.setup.run (service.setup.decodeBehavioralProfile
        admission source)).map
        (fun config => (some (config.state, config.defaults),
          utility (service.setup.parameterOutcome parameter config))) := by
  intro base settle
  have close := sourceServiceClients_clientPolicy_settlement_distributionError
    (fun event => (service.setup.dataflowGraph.sequentialize_solitary event).ownerSolitary)
    service.contract
    (firstTurnTiming service.setup turns service.setup.informationDependencies)
    (service.setup.decodeBehavioralProfile admission
      source)
    (firstTurn_readout_distribution service.setup service.leaks service.contract service.timely
      turns _ (fun _ => BehavioralPolicy.normalizeDisclosures_authentic _ _))
    service.rawMenu
    (service.rawMenu_admits admission (firstTurnTiming service.setup turns
      service.setup.informationDependencies) source)
    sample authentic (fun result => utility
      (parameter (initialState service.setup.program result.1),
        ⟨sourcePublicEnv result.1, result.2⟩)) deposit
  simp only [firstTurnTiming_deferralError] at close
  exact close.eq_of_zero


/-- **Intended Nash equilibria on the bounded raw ledger, for every contract
builder.** For a well-formed setup, a forfeit no smaller than the payoff range,
every authentic audit and every nonnegative deposit, the first-turn clients of
a source profile extending an `ε`-Nash equilibrium of the intended game are an
`ε`-Nash equilibrium of the bounded raw response menu under the forfeit pass,
with the same `ε`, and their joint law of typed outcome and realized settlement
is the intended joint law of typed cells, public default history and payoff. -/
theorem intended_firstTurnClientProfile_isεNash {Parameter : Type}
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ)
    (range : service.setup.TerminalPayoffSpread (CommitmentInterface.values
      service.setup.program) parameter utility forfeit)
    (sample : List (SettledEvidence service.setup service.setup.informationDependencies) →
      PMF (List (SettledEvidence service.setup service.setup.informationDependencies)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (turns : Nat)
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
    let base := serviceBaseUtility service.setup service.setup.informationDependencies
      service.duration service.leaks
      (fun state => forfeited (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceAuditObservation (serviceTimeouts service.setup
        service.setup.informationDependencies service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.setup.informationDependencies service.duration
        service.leaks sample) deposit
    let settle := TerminalAudit.settlement base
      ((serviceAuditObservation (serviceTimeouts service.setup
        service.setup.informationDependencies service.duration))
        service.leaks)
      (serviceSourceAudit service.setup service.setup.informationDependencies service.duration
        service.leaks sample) deposit
    IsεNash (service.gameForm service.rawMenu)
        (fun history who => payoff history.state who) ε
        (service.clientProfile (CommitmentInterface.values service.setup.program) service.rawMenu
          (firstTurnTiming service.setup turns service.setup.informationDependencies)
          source) ∧
      (service.run service.rawMenu
            (service.clientProfile (CommitmentInterface.values service.setup.program)
              service.rawMenu (firstTurnTiming service.setup turns
              service.setup.informationDependencies) source)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                ((serviceSourceReadout service.setup service.setup.informationDependencies
                  service.duration service.leaks
                  final.state).map (fun config => (config.state, config.defaults)), payoffs)) =
        (service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => ((service.setup.protocolReadout final.state).map
              (fun config => (config.state, config.defaults)),
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who))) := by
  intro forfeited base payoff settle
  let admission := CommitmentInterface.values service.setup.program
  obtain ⟨sourceNash, _, sourceLaw⟩ := service.setup.intended_forfeit_isεNash_preserved admission
    (sourceService_finiteBindingTypes service.setup service.bounds service.values)
    wellFormed parameter utility forfeit range intended source agrees ε equilibrium
  refine ⟨(service.isεNash_firstTurnClientProfile_iff admission parameter forfeited sample
    authentic deposit nonnegative turns ε source).2 sourceNash, ?_⟩
  rw [service.firstTurnClientProfile_settlement_distribution admission parameter forfeited
    sample authentic deposit turns source]
  let observe := fun (output : Option (Config Player L service.setup.program.terminalCtx)) =>
    (output.map (fun config => (config.state, config.defaults)), fun who => output.elim 0
      (fun config => forfeited (service.setup.parameterOutcome parameter config) who))
  have decoded : ((service.sourceModel admission).runBehavioral source
      (service.setup.program.instructionCount + 1)).map
        (fun h => service.setup.protocolReadout h.state) =
      (service.setup.run (service.setup.decodeBehavioralProfile admission source)).map some :=
    service.setup.runBehavioralFrom_readout admission source
    (instructionCount service.setup.program + 1)
    (service.setup.executionProtocol admission).initHistory (Nat.le_refl _)
  have projected := congrArg (PMF.map fun outcome =>
    (outcome.1.map (fun config => (config.state, config.defaults)), outcome.2)) sourceLaw
  simpa only [observe, PMF.map_comp, Function.comp_def, Option.map_some, Option.elim_some]
    using (congrArg (PMF.map observe) decoded).symm.trans (by
      simpa only [observe, PMF.map_comp, Function.comp_def] using projected)

end AsyncServiceSpec

end Vegas
