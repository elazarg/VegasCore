/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.AsyncServiceDeviationBound

/-! # Approximate Nash correspondence on the bounded raw ledger

The source commitment interface may independently admit failed binding choices
at each site. The bounded raw response menu (`Vegas.AsyncServiceSpec.rawMenu`) admits every
native response within the service's message bounds, including every packet
error. It admits the turn-counted clients of every source profile
(`Vegas.AsyncServiceSpec.rawMenu_admits`): each client completes its
turn-counted policy by silence after its own off-policy responses
(`Vegas.sourceServiceClientPolicy`), and on every bounded raw history where its
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

/-- The bounded raw response menu: every native response within the service's
message bounds. -/
abbrev rawMenu : (serviceApplication service.setup service.mode service.deadline
    service.leaks).ResponseMenu :=
  service.bounds.rawMenu (serviceRuntime service.setup service.mode service.deadline) service.leaks

/-- **The bounded raw menu admits every profile's clients.** For every turn
timing and every source profile, each player's client policy is admissible in
the bounded raw response menu. -/
theorem rawMenu_admits {turns : Nat}
    (timing : TurnTiming service.setup turns service.mode)
    (source : Profile (service.sourceModel admission).behavioralSignature) (who : Player) :
    service.rawMenu.Admissible (serviceInitialLaw service.setup service.mode) service.horizon
      service.scheduler who
      (serviceClientPolicy service.setup service.mode service.deadline service.leaks service.bound
        turns timing
        (sourceServiceClientProfile service.setup (service.setup.decodeBehavioralProfile
          admission source)) who) :=
  sourceServiceClientPolicy_raw_admissible service.bounds service.values service.initialValues
    service.capacity service.bound turns timing _ service.horizon service.scheduler who

theorem isεNash_rawClientProfile_approximate {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
    (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range)
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    (IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * range)
        (service.clientProfile admission service.rawMenu timing source)) ∧
    (IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
      service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile admission service.rawMenu timing source) →
      IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        (ε + 2 * (∑ event, timing.deferral event) * range) source) :=
  service.isεNash_clientProfile_approximate admission ordered parameter utility sample authentic
    deposit nonnegative
    service.rawMenu timing (service.rawMenu_admits admission timing) low range within ε source

/-- **Intended approximate Nash equilibria on the bounded raw ledger, for
every contract builder.** For a well-formed setup, a forfeit no smaller than
the payoff range, every authentic audit and every nonnegative deposit, the
turn-counted clients of a source profile extending an `ε`-Nash equilibrium of
the intended game are an `(ε + 2 * δ * R)`-Nash equilibrium of the bounded raw
response menu under the forfeit pass, and their joint law of typed outcome and
realized settlement is within `δ` in total variation of the intended joint law
of terminal store and payoff. -/
theorem intended_rawClientProfile_isεNash {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    {turns : Nat} (timing : TurnTiming service.setup turns service.mode)
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
    IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
      service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who)
        (ε + 2 * (∑ event, timing.deferral event) * spread)
        (service.clientProfile (CommitmentInterface.values service.setup.program) service.rawMenu
          timing source) ∧
      PMF.WithinTV (∑ event, timing.deferral event)
        (((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
          service.horizon
          service.scheduler).runBehavioral (service.clientProfile (CommitmentInterface.values
            service.setup.program) service.rawMenu timing source)
            (2 * service.horizon + 1)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                (serviceSourceReadout service.setup service.mode service.deadline service.leaks
                  final.state, payoffs)))
        ((service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => (service.setup.protocolReadout final.state,
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who)))) :=
  service.intended_clientProfile_isεNash ordered wellFormed parameter utility forfeit range
    sample
    authentic deposit nonnegative service.rawMenu timing (service.rawMenu_admits
      (CommitmentInterface.values service.setup.program)
      timing) low
    spread within intended source agrees ε equilibrium

/-- **Exact Nash correspondence on the bounded raw ledger, for every contract
builder.** Under the asynchronous contract, for every authentic audit and every
nonnegative deposit, the first-turn clients of a source profile, which make
each source decision at the owner's first opportunity, are an `ε`-Nash
equilibrium of the bounded raw response menu for the audited payoff exactly when
the source profile is an `ε`-Nash equilibrium of the source protocol model, for
every `ε`. Realized payoffs need only lie in some bounded interval. -/
theorem isεNash_firstTurnClientProfile_iff {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (turns : Nat)
    (low : Player → ℝ) (range : ℝ)
    (within : ∀ who (output : Option (State L service.setup.program.terminalCtx))
      (charged : Bool),
      low who ≤ output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ∧
        output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter
          state) who) - (if charged then deposit who else 0) ≤ low who + range)
    (ε : ℝ) (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let payoff := TerminalAudit.utility base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
      service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile admission service.rawMenu (firstTurnTiming service.setup turns
          service.mode)
          source) ↔
      IsεNash ((service.sourceModel admission).toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source := by
  intro base payoff
  have approximate := service.isεNash_rawClientProfile_approximate admission ordered parameter
    utility
    sample
    authentic deposit nonnegative (firstTurnTiming service.setup turns service.mode) low range
      within ε source
  simp only [firstTurnTiming_deferral, Finset.sum_const_zero, mul_zero, zero_mul, add_zero]
    at approximate
  exact ⟨approximate.2, approximate.1⟩

/-- **Intended Nash equilibria on the bounded raw ledger, for every contract
builder.** For a well-formed setup, a forfeit no smaller than the payoff range,
every authentic audit and every nonnegative deposit, the first-turn clients of
a source profile extending an `ε`-Nash equilibrium of the intended game are an
`ε`-Nash equilibrium of the bounded raw response menu under the forfeit pass,
with the same `ε`, and their joint law of typed outcome and realized settlement
is the intended joint law of terminal store and payoff. -/
theorem intended_firstTurnClientProfile_isεNash {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (wellFormed : service.setup.WellFormed)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (forfeit : ℝ) (range : ∀ high low who, utility high who - utility low who ≤ forfeit)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (nonnegative : ∀ who, 0 ≤ deposit who)
    (turns : Nat)
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
    IsεNash ((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
      service.horizon
        service.scheduler).toBehavioralGameForm (2 * service.horizon + 1))
        (fun history who => payoff history.state who) ε
        (service.clientProfile (CommitmentInterface.values service.setup.program) service.rawMenu
          (firstTurnTiming service.setup turns service.mode)
          source) ∧
      ((service.rawMenu.information (serviceInitialLaw service.setup service.mode) service.horizon
          service.scheduler).runBehavioral
            (service.clientProfile (CommitmentInterface.values service.setup.program)
              service.rawMenu (firstTurnTiming service.setup turns
              service.mode) source)
            (2 * service.horizon + 1)).bind (fun final =>
              (settle final.state).map fun payoffs =>
                (serviceSourceReadout service.setup service.mode service.deadline service.leaks
                  final.state, payoffs)) =
        (service.setup.intendedModel.runBehavioral intended
            (instructionCount service.setup.program + 1)).map
          (fun final => (service.setup.protocolReadout final.state,
            fun who => (service.setup.protocolReadout final.state).elim 0
              (fun state => utility (service.setup.parameterOutcome parameter state) who))) := by
  intro forfeited base payoff settle
  have approximate := service.intended_rawClientProfile_isεNash ordered wellFormed parameter
    utility
    forfeit range sample authentic deposit nonnegative (firstTurnTiming service.setup turns
      service.mode) low
    spread within intended source agrees ε equilibrium
  simp only [firstTurnTiming_deferral, Finset.sum_const_zero, mul_zero, zero_mul, add_zero]
    at approximate
  exact ⟨approximate.1, approximate.2.eq_of_zero⟩

/-- Every commitment interface preserves the exact joint law of typed terminal
store and realized settlement when clients act at their first opportunities.
Every admitted binding choice incurs no audit charge on the prescribed execution. -/
theorem firstTurnClientProfile_settlement_law {Parameter : Type}
    (ordered : (serviceGraph service.setup service.mode).BarrierOrdered)
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup service.mode) →
      PMF (List (SettledEvidence service.setup service.mode)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ) (turns : Nat)
    (source : Profile (service.sourceModel admission).behavioralSignature) :
    let base := serviceBaseUtility service.setup service.mode service.deadline service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let settle := TerminalAudit.settlement base
      ((serviceRuntime service.setup service.mode service.deadline).serviceAuditObservation
        service.leaks)
      (serviceSourceAudit service.setup service.mode service.deadline service.leaks sample) deposit
    (((service.rawMenu.information (serviceInitialLaw service.setup service.mode)
        service.horizon service.scheduler).runBehavioral
      (service.clientProfile admission service.rawMenu
        (firstTurnTiming service.setup turns service.mode) source)
      (2 * service.horizon + 1)).bind fun final =>
        (settle final.state).map fun payoffs =>
          (serviceSourceReadout service.setup service.mode service.deadline service.leaks
            final.state, payoffs)) =
      (service.setup.run (service.setup.decodeBehavioralProfile
        admission source)).map
        (fun state => (some state, utility (service.setup.parameterOutcome parameter state))) := by
  intro base settle
  have close := sourceServiceClients_clientPolicy_settlement_lawError service.contract
    service.timely (firstTurnTiming service.setup turns service.mode)
    (service.setup.decodeBehavioralProfile admission
      source)
    (firstTurn_readout_law service.setup service.leaks ordered service.contract service.timely
      turns _ (sourceServiceClientProfile_effective _))
    service.rawMenu
    (service.rawMenu_admits admission (firstTurnTiming service.setup turns service.mode) source)
    sample authentic (fun state => utility (service.setup.parameterOutcome parameter state)) deposit
  simp only [firstTurnTiming_deferral, Finset.sum_const_zero] at close
  exact close.eq_of_zero


end AsyncServiceSpec

end Vegas
