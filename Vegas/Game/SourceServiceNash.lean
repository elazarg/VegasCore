/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompilation
import Vegas.Game.SourceServiceInitialRepair
import Vegas.Game.SourceServiceDeviationReadout
import GameTheory.Core.UtilityTransfer
import GameTheory.Core.MixtureSimulation

/-! # Approximate Nash equilibrium on the audited calendar ledger

The compiled raw profile of a source profile is built player by player: the
source policy is decoded, normalized and played with the roster timing law at
weight one half in the permitted menu (`Vegas.sourceServiceTimedProfile`),
extended by a fixed fallback to the effective menu, and given its canonical raw
response names (`Vegas.EventGraphRuntime.MessageBounds.canonicalRawPolicy`).

For every source profile, the compiled profile's joint law of typed source
outcome and audited payoff vector is the source law of typed outcome and payoff
(`Vegas.SourceServiceSpec.compileProfile_payoff_law`). Hence native approximate
Nash of the compiled profile reflects to the source with the same slack
(`Vegas.SourceServiceSpec.isεNash_of_compileProfile`).

In the other direction every raw deviation against the compiled profile is
bounded by a deviation in the permitted menu
(`Vegas.SourceServiceSpec.exists_menu_deviation_ge`): private response aliases
are erased exactly, and the fixed binding repair dominates an effective
deviation by the range-sized deposit. Every deviation in the permitted menu
against the timed profile has exactly the typed outcome law of a source
deviation (`Vegas.SourceServiceSpec.exists_source_deviation_law`, packaged as
the mixture simulation `Vegas.SourceServiceSpec.menuSimulation`). Hence the
compiled raw profile is an approximate Nash equilibrium exactly when the source
profile is one, with the same slack
(`Vegas.SourceServiceSpec.isεNash_compileProfile_iff`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

/-- The roster timing law at weight one half: every owner decides at a
uniformly drawn roster visit with probability one half, and at its last visit
otherwise. -/
def calendarTiming : TimingLaw service.setup service.rosters :=
  rosterTiming service.setup service.rosters service.opportunities (1 / 2) (by norm_num)
    (by norm_num)

omit [Fintype Player] in
theorem calendarTiming_fullSupport (event : (graph service.setup).EventId) (who : Player)
    (owned : (graph service.setup).actor? event = some who) :
    FullSupport (service.calendarTiming event who owned) :=
  rosterTiming_fullSupport service.setup service.rosters service.opportunities (1 / 2)
    (by norm_num) (by norm_num) (by norm_num) event who owned

/-- The effective response menu: every bounded native response up to private
aliases. -/
abbrev effective := service.bounds.menu (runtime service.setup) service.leaks

/-- The raw response menu: every bounded native response. -/
abbrev raw := service.bounds.rawMenu (runtime service.setup) service.leaks

/-- The permitted menu as a restriction of the effective menu. -/
abbrev restriction := (sourceServiceMenu_in_effective service.setup service.leaks service.bounds
  service.rosters).actionRestriction (initialLaw service.setup) service.planLength
    service.scheduler

/-- The timed calendar profile of a source profile in the permitted menu. -/
def timedProfile (source : Profile service.sourceModel.behavioralSignature) :
    Profile service.model.behavioralSignature :=
  sourceServiceTimedProfile service.setup service.leaks service.bounds service.rosters
    service.network service.calendarTiming
    (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
      source)

/-- The timed calendar profile in the effective menu; responses outside the
permitted menu are never reached and follow the uniform policy. -/
def effectiveProfile (source : Profile service.sourceModel.behavioralSignature) :
    ∀ who, (service.effective.information (initialLaw service.setup) service.planLength
      service.scheduler).BehavioralPolicy who :=
  service.restriction.extendProfile (service.timedProfile source)
    (service.effective.uniformPolicy (initialLaw service.setup) service.planLength
      service.scheduler)

/-- **The compiled raw profile** of a source profile. -/
def compileProfile (source : Profile service.sourceModel.behavioralSignature) :
    Profile (service.raw.information (initialLaw service.setup) service.planLength
      service.scheduler).behavioralSignature := fun who =>
  service.bounds.canonicalRawPolicy (runtime service.setup) service.leaks
    (initialLaw service.setup) service.planLength service.scheduler who
    (service.effectiveProfile source who)

omit [Fintype Player] in
private theorem timedPolicy_congr (profile other : BehavioralProfile service.setup.program)
    (who : Player) (same : profile who = other who) :
    sourceServiceTimedPolicy service.setup service.leaks service.rosters service.calendarTiming
        profile who =
      sourceServiceTimedPolicy service.setup service.leaks service.rosters service.calendarTiming
        other who := by
  unfold sourceServiceTimedPolicy sourceServiceTimedFamily sourceServiceOpportunity
    sourceServicePolicy compileEventProfile
  rw [same]

omit [DecidableEq Player] [Fintype Player] [IExpr.ResultTypes L] in
private theorem extendProfile_congr {ι : Type*} {E T : ExecutionProtocol ι}
    {M : InformationModel E} {N : InformationModel T} (restriction : M.ActionRestriction N)
    (source other : ∀ who, M.BehavioralPolicy who) (fallback : ∀ who, N.BehavioralPolicy who)
    (who : ι) (same : source who = other who) :
    restriction.extendProfile source fallback who =
      restriction.extendProfile other fallback who := by
  unfold InformationModel.ActionRestriction.extendProfile
    InformationModel.ActionRestriction.retainedLaw
  rw [same]

/-- Each player's timed calendar policy depends only on its own source
policy. -/
theorem timedProfile_congr (source other : Profile service.sourceModel.behavioralSignature)
    (who : Player) (same : source who = other who) :
    service.timedProfile source who = service.timedProfile other who := by
  have decoded : normalizeDisclosureProfile service.setup.program []
      (Revelations.initial service.setup.context)
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        source) who =
    normalizeDisclosureProfile service.setup.program []
      (Revelations.initial service.setup.context)
      (service.setup.decodeBehavioralProfile (CommitmentInterface.values service.setup.program)
        other) who := by
    simp only [normalizeDisclosureProfile, Setup.decodeBehavioralProfile, same]
  exact congrArg (service.menu.restrictPolicy (initialLaw service.setup) service.planLength
    service.scheduler who) (timedPolicy_congr service _ _ who decoded)

/-- Each player's compiled policy depends only on its own source policy. -/
theorem compileProfile_congr (source other : Profile service.sourceModel.behavioralSignature)
    (who : Player) (same : source who = other who) :
    service.compileProfile source who = service.compileProfile other who := by
  have timed := service.timedProfile_congr source other who same
  exact congrArg (service.bounds.canonicalRawPolicy (runtime service.setup) service.leaks
    (initialLaw service.setup) service.planLength service.scheduler who)
    (extendProfile_congr service.restriction _ _ _ who timed)

/-- Compiling a unilateral deviation is a unilateral deviation of the compiled
profile. -/
theorem compileProfile_update (source : Profile service.sourceModel.behavioralSignature)
    (who : Player) (alternative : service.sourceModel.BehavioralPolicy who) :
    Profile.update (service.compileProfile source) who
        (service.compileProfile (Profile.update source who alternative) who) =
      service.compileProfile (Profile.update source who alternative) := by
  funext other
  by_cases same : other = who
  · subst other
    simp only [Profile.update, Function.update_self]
  · simp only [Profile.update, Function.update_of_ne same]
    exact service.compileProfile_congr _ _ other (by
      simp only [Function.update_of_ne same])

/-- The audited payoff is invariant under private response normalization. -/
private theorem auditedPayoff_normalization {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (probability : Player → ℝ) (state : (application service.setup service.leaks).ProtocolState) :
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    payoff (((runtime service.setup).reactiveNormalization service.leaks).state state) =
      payoff state := by
  intro base deposit payoff
  have baseInvariant :
      base (((runtime service.setup).reactiveNormalization service.leaks).state state) =
        base state :=
    baseUtility_normalization service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state)) state
  have observation := (runtime service.setup).serviceAuditObservation_normalization
    service.leaks ((runtime service.setup).reactiveNormalization service.leaks) state
  funext who
  simp only [payoff, TerminalAudit.utility, TerminalAudit.charge, baseInvariant, observation]

/-- The compiled raw profile of every source profile has the source joint law
of typed outcome and payoff vector, the payoff realized as the audited
expected payoff. -/
theorem compileProfile_payoff_law {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ)
    (source : Profile service.sourceModel.behavioralSignature) :
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    ((service.raw.information (initialLaw service.setup) service.planLength
        service.scheduler).runBehavioral (service.compileProfile source) service.fuel).map
        (fun final => (sourceReadout service.setup service.leaks final.state,
          payoff final.state)) =
      (service.sourceModel.runBehavioral source (instructionCount service.setup.program + 1)).map
        (fun final => (service.setup.protocolReadout final.state,
          fun who => (service.setup.protocolReadout final.state).elim 0
            (fun state => utility (service.setup.parameterOutcome parameter state) who))) := by
  intro base deposit payoff
  let observe := fun state : (application service.setup service.leaks).ProtocolState =>
    (sourceReadout service.setup service.leaks state, payoff state)
  let outcome := fun output : Option (State L service.setup.program.terminalCtx) =>
    (output, fun who => output.elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who))
  have invariant (state : (application service.setup service.leaks).ProtocolState) :
      observe (((runtime service.setup).reactiveNormalization service.leaks).state state) =
        observe state := by
    have payoffInvariant :
        payoff (((runtime service.setup).reactiveNormalization service.leaks).state state) =
          payoff state :=
      service.auditedPayoff_normalization parameter utility sample probability state
    change (sourceReadout service.setup service.leaks
      (((runtime service.setup).reactiveNormalization service.leaks).state state),
        payoff (((runtime service.setup).reactiveNormalization service.leaks).state state)) = _
    rw [payoffInvariant, sourceReadout_normalization]
  have clear (history : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).History) :
      observe history.state =
        outcome (sourceReadout service.setup service.leaks history.state) := by
    have matching (who : Player) : payoff history.state who = base history.state who := by
      have clean := sourceService_history_audit_clear service.setup service.leaks service.bounds
        service.values service.capacity service.rosters service.opportunities.binding
        service.network sample authentic history who
      change base history.state who - TerminalAudit.charge
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) history.state who *
          deposit who = base history.state who
      rw [clean, zero_mul, sub_zero]
    change (sourceReadout service.setup service.leaks history.state, payoff history.state) = _
    rw [funext matching]
    rfl
  have rawLaw := ((runtime service.setup).reactiveNormalization
    service.leaks).canonical_initial_stateLaw service.raw
    (service.bounds.rawMenu_recall (runtime service.setup) service.leaks)
    (service.bounds.rawMenu_closed (runtime service.setup) service.leaks)
    (initialLaw service.setup) service.planLength service.scheduler
    (service.effectiveProfile source) service.fuel
  have effectiveLaw := service.restriction.initialized_law (service.timedProfile source)
    (service.effectiveProfile source)
    (service.restriction.extendProfile_extends (service.timedProfile source) _) service.fuel
  have menuLaw := sourceServiceTimedProfile_protocol_law service.setup service.leaks
    service.bounds service.values service.initialValues service.capacity service.rosters
    service.opportunities.binding service.calendarTiming service.calendarTiming_fullSupport
    service.network source
  have first : ((service.raw.information (initialLaw service.setup) service.planLength
      service.scheduler).runBehavioral (service.compileProfile source) service.fuel).map
        (fun final => observe final.state) =
      (((service.effective.information (initialLaw service.setup) service.planLength
        service.scheduler).runBehavioral (service.effectiveProfile source) service.fuel).map
          History.state).map observe := by
    have mapped := congrArg (PMF.map observe) rawLaw
    rw [PMF.map_comp] at mapped
    refine Eq.trans ?_ mapped
    exact congrArg (fun view => PMF.map view ((service.raw.information (initialLaw service.setup)
      service.planLength service.scheduler).runBehavioral (service.compileProfile source)
        service.fuel)) (funext fun final => (invariant final.state).symm)
  have second : (((service.effective.information (initialLaw service.setup) service.planLength
      service.scheduler).runBehavioral (service.effectiveProfile source) service.fuel).map
        History.state).map observe =
      ((service.model.runBehavioral (service.timedProfile source) service.fuel).map
        (fun final => sourceReadout service.setup service.leaks final.state)).map outcome := by
    have mapped := congrArg (fun law => (law.map History.state).map observe) effectiveLaw
    simp only [PMF.map_comp] at mapped ⊢
    refine mapped.symm.trans ?_
    exact congrArg (fun view => PMF.map view (service.model.runBehavioral
      (service.timedProfile source) service.fuel)) (funext clear)
  refine first.trans (second.trans ?_)
  have mapped := congrArg (PMF.map outcome) menuLaw
  simp only [PMF.map_comp] at mapped ⊢
  exact mapped

/-- Every player's audited payoff has an expectation under the compiled raw
profile, and the expectation is the source expected payoff. -/
private theorem compileProfile_expectation {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ)
    (source : Profile service.sourceModel.behavioralSignature) (who : Player) :
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    let nativeForm := (service.raw.information (initialLaw service.setup) service.planLength
      service.scheduler).toBehavioralGameForm service.fuel
    let sourceForm := service.sourceModel.toBehavioralGameForm
      (instructionCount service.setup.program + 1)
    let nativeUtility := fun (history : nativeForm.sig.Outcome) who => payoff history.state who
    let sourceUtility := fun (final : sourceForm.sig.Outcome) who =>
      (service.setup.protocolReadout final.state).elim 0
        (fun state => utility (service.setup.parameterOutcome parameter state) who)
    (UtilityHasExpectation nativeUtility who (nativeForm.play (service.compileProfile source)) ↔
      UtilityHasExpectation sourceUtility who (sourceForm.play source)) ∧
    extendedExpectedUtility nativeUtility who (nativeForm.play (service.compileProfile source)) =
      extendedExpectedUtility sourceUtility who (sourceForm.play source) := by
  intro base deposit payoff nativeForm sourceForm nativeUtility sourceUtility
  have law := congrArg (PMF.map Prod.snd) (service.compileProfile_payoff_law parameter utility
    sample authentic probability source)
  simp only [PMF.map_comp, Function.comp_def] at law
  exact ⟨hasExpectation_observed_law_iff _ _ _ _ (fun payoffs : Player → ℝ => payoffs who) law,
    extendedExpect_observed_law_eq _ _ _ _ (fun payoffs : Player → ℝ => payoffs who) law⟩

/-- **Reflection of approximate Nash.** If the compiled raw profile of a
source profile is an `ε`-Nash equilibrium of the audited bounded raw runtime,
then the source profile is an `ε`-Nash equilibrium of the source protocol
model, for the same `ε`. -/
theorem isεNash_of_compileProfile {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (ε : ℝ)
    (source : Profile service.sourceModel.behavioralSignature) :
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    IsεNash ((service.raw.information (initialLaw service.setup) service.planLength
        service.scheduler).toBehavioralGameForm service.fuel)
        (fun history who => payoff history.state who) ε (service.compileProfile source) →
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source := by
  intro base deposit payoff native
  rw [isεNash_iff] at native ⊢
  intro who alternative
  obtain ⟨baseExpectation, deviationExpectation, compared⟩ :=
    native who (service.compileProfile (Profile.update source who alternative) who)
  rw [service.compileProfile_update] at deviationExpectation compared
  obtain ⟨honestIff, honestValue⟩ := service.compileProfile_expectation parameter utility sample
    authentic probability source who
  obtain ⟨deviationIff, deviationValue⟩ := service.compileProfile_expectation parameter utility
    sample authentic probability (Profile.update source who alternative) who
  refine ⟨honestIff.mp baseExpectation, deviationIff.mp deviationExpectation, ?_⟩
  rw [← honestValue, ← deviationValue]
  exact compared

/-- **Raw deviations reduce to the permitted menu.** Every raw whole-policy
deviation against the compiled profile is bounded, in audited expected payoff,
by a deviation in the permitted menu against the timed profile, valued at its
base payoff. Private response aliases are erased exactly; the fixed binding
repair of the erased deviation dominates it under the range-sized deposit. -/
theorem exists_menu_deviation_ge {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (source : Profile service.sourceModel.behavioralSignature) (who : Player)
    (replacement : (service.raw.information (initialLaw service.setup) service.planLength
      service.scheduler).BehavioralPolicy who) :
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    ∃ alternative : service.model.BehavioralPolicy who,
      expect ((service.raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioral
          (Profile.update (service.compileProfile source) who replacement) service.fuel)
          (fun final => payoff final.state who) ≤
        expect (service.model.runBehavioral
          (Profile.update (service.timedProfile source) who alternative) service.fuel)
          (fun final => base final.state who) := by
  intro base deposit payoff
  let erased := ((runtime service.setup).reactiveNormalization service.leaks).aliasDeviation
    service.raw (initialLaw service.setup) service.planLength service.scheduler who [] replacement
  let repair := BindingMemory.retainedPolicy (runtime service.setup) service.leaks service.menu
    (initialLaw service.setup) service.planLength service.scheduler who []
    ((application service.setup service.leaks).decodePolicy (service.effective.embedPolicy
      (initialLaw service.setup) service.planLength service.scheduler who erased))
  refine ⟨repair, ?_⟩
  have compared : expect ((service.effective.information (initialLaw service.setup)
      service.planLength service.scheduler).runBehavioral
        (Function.update (service.effectiveProfile source) who erased) service.fuel)
        (fun final => payoff final.state who) ≤
      expect (service.model.runBehavioral
        (Function.update (service.timedProfile source) who repair) service.fuel)
        (fun final => base final.state who) :=
    sourceService_initial_settlement_comparison service.setup service.leaks
      service.bounds service.values service.capacity service.rosters
      service.opportunities.binding service.network parameter utility sample authentic
      probability positive coverage (service.timedProfile source) (service.effectiveProfile source)
      (service.restriction.extendProfile_extends (service.timedProfile source) _) who erased
  have aliasLaw : (((service.raw.information (initialLaw service.setup) service.planLength
      service.scheduler).runBehavioral
        (Profile.update (service.compileProfile source) who replacement) service.fuel).map
          History.state).map ((runtime service.setup).reactiveNormalization service.leaks).state =
      ((service.effective.information (initialLaw service.setup) service.planLength
        service.scheduler).runBehavioral
          (Function.update (service.effectiveProfile source) who erased) service.fuel).map
            History.state :=
    ((runtime service.setup).reactiveNormalization service.leaks).aliasDeviation_initialLaw
      service.raw (service.bounds.rawMenu_recall (runtime service.setup) service.leaks)
      (service.bounds.rawMenu_closed (runtime service.setup) service.leaks)
      (initialLaw service.setup) service.planLength service.scheduler
      (service.effectiveProfile source) who replacement
  have rawValue : expect ((service.raw.information (initialLaw service.setup) service.planLength
      service.scheduler).runBehavioral
        (Profile.update (service.compileProfile source) who replacement) service.fuel)
        (fun final => payoff final.state who) =
      expect ((service.effective.information (initialLaw service.setup) service.planLength
        service.scheduler).runBehavioral
          (Function.update (service.effectiveProfile source) who erased) service.fuel)
        (fun final => payoff final.state who) := by
    calc
      _ = expect ((((service.raw.information (initialLaw service.setup) service.planLength
          service.scheduler).runBehavioral
            (Profile.update (service.compileProfile source) who replacement) service.fuel).map
              History.state).map
                ((runtime service.setup).reactiveNormalization service.leaks).state)
          (fun state => payoff state who) := by
        rw [expect_map, expect_map]
        apply expect_congr_on_support
        intro final _
        exact (congrFun (service.auditedPayoff_normalization parameter utility sample probability
          final.state) who).symm
      _ = _ := by
        rw [aliasLaw, expect_map]
        rfl
  exact rawValue.trans_le compared

/-- **Approximate Nash transfer from a menu bound.** If every deviation in the
permitted menu against the timed profile is bounded, in base expected payoff,
by some source deviation, then every source `ε`-Nash equilibrium compiles to an
`ε`-Nash equilibrium of the audited bounded raw runtime. The bound holds for
every source profile (`Vegas.SourceServiceSpec.exists_source_deviation_ge`). -/
theorem isεNash_compileProfile_of_menu_bounds {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (ε : ℝ) (source : Profile service.sourceModel.behavioralSignature) :
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    (∀ who (alternative : service.model.BehavioralPolicy who),
      ∃ deviation : service.sourceModel.BehavioralPolicy who,
        expect (service.model.runBehavioral
          (Profile.update (service.timedProfile source) who alternative) service.fuel)
          (fun final => base final.state who) ≤
        expect (service.sourceModel.runBehavioral (Profile.update source who deviation)
          (instructionCount service.setup.program + 1))
          (fun final => (service.setup.protocolReadout final.state).elim 0
            (fun state => utility (service.setup.parameterOutcome parameter state) who))) →
    IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source →
      IsεNash ((service.raw.information (initialLaw service.setup) service.planLength
        service.scheduler).toBehavioralGameForm service.fuel)
        (fun history who => payoff history.state who) ε (service.compileProfile source) := by
  intro base deposit payoff menuBound equilibrium
  have := service.setup.finite_history
    (sourceService_finiteBindingTypes service.setup service.bounds service.values)
    (CommitmentInterface.values service.setup.program)
  refine GameForm.isεNash_of_deviation_bounds
    (source := service.sourceModel.toBehavioralGameForm
      (instructionCount service.setup.program + 1))
    (target := (service.raw.information (initialLaw service.setup) service.planLength
      service.scheduler).toBehavioralGameForm service.fuel)
    (sourceUtility := fun final who => (service.setup.protocolReadout final.state).elim 0
      (fun state => utility (service.setup.parameterOutcome parameter state) who))
    (targetUtility := fun history who => payoff history.state who)
    source (service.compileProfile source)
    (fun who sourceExpectation => ?_) (fun who replacement => ?_) ε equilibrium
  · obtain ⟨honestIff, honestValue⟩ := service.compileProfile_expectation parameter utility sample
      authentic probability source who
    exact ⟨honestIff.mpr sourceExpectation, honestValue⟩
  · obtain ⟨alternative, nativeBound⟩ := service.exists_menu_deviation_ge parameter utility
      sample authentic probability positive coverage source who replacement
    obtain ⟨deviation, menuValue⟩ := menuBound who alternative
    refine ⟨deviation, fun _ => ?_⟩
    have nativeIntegrable : UtilityIntegrable (fun history who => payoff history.state who) who
        (((service.raw.information (initialLaw service.setup) service.planLength
          service.scheduler).toBehavioralGameForm service.fuel).play
            (Profile.update (service.compileProfile source) who replacement)) :=
      payoffIntegrable_of_finite _ _
    have sourceIntegrable : UtilityIntegrable
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who)) who
        ((service.sourceModel.toBehavioralGameForm
          (instructionCount service.setup.program + 1)).play
            (Profile.update source who deviation)) :=
      payoffIntegrable_of_finite _ _
    refine ⟨nativeIntegrable.hasExpectation, ?_⟩
    rw [extendedExpectedUtility_eq nativeIntegrable, extendedExpectedUtility_eq sourceIntegrable]
    exact EReal.coe_le_coe_iff.mpr (nativeBound.trans menuValue)

/-- **Every permitted deviation is a source deviation.** Against the timed
calendar profile of any source profile, every deviation of one player within
the permitted menu has exactly the typed outcome law of a deviation of the same
player in the source protocol model. -/
theorem exists_source_deviation_law (source : Profile service.sourceModel.behavioralSignature)
    (who : Player) (replacement : service.model.BehavioralPolicy who) :
    ∃ alternative : service.sourceModel.BehavioralPolicy who,
      (service.model.runBehavioral (Profile.update (service.timedProfile source) who replacement)
        service.fuel).map (fun final => sourceReadout service.setup service.leaks final.state) =
      (service.sourceModel.runBehavioral (Profile.update source who alternative)
        (instructionCount service.setup.program + 1)).map
          (fun final => service.setup.protocolReadout final.state) := by
  let admission := CommitmentInterface.values service.setup.program
  have permitted (player : Player) :
      (service.setup.decodeBehavioralProfile admission source player).Admitted
        service.setup.program admission :=
    ((service.setup.behavioralPolicyEquiv admission player).symm (source player)).2
  obtain ⟨policy, allowed, law⟩ := sourceServiceDeviation_readout_law service.setup service.leaks
    service.bounds service.values service.initialValues service.capacity service.rosters
    service.opportunities.binding service.calendarTiming service.calendarTiming_fullSupport
    service.network (service.setup.decodeBehavioralProfile admission source) permitted who
    replacement
  refine ⟨(service.setup.behavioralPolicyEquiv admission who) ⟨policy, allowed⟩, ?_⟩
  have readout := service.setup.runBehavioralFrom_readout admission
    (Profile.update source who ((service.setup.behavioralPolicyEquiv admission who)
      ⟨policy, allowed⟩)) (instructionCount service.setup.program + 1)
    (service.setup.executionProtocol admission).initHistory (Nat.le_refl _)
  rw [service.setup.decodeBehavioralProfile_update _ source who policy allowed] at readout
  exact law.trans readout.symm

/-- A fixed source policy of every player, used only to complete a profile
around one player's strategy. -/
private def defaultSourcePolicy (who : Player) : service.sourceModel.BehavioralPolicy who :=
  fun info => PMF.pure (Classical.choice (service.setup.choice_nonempty
    (CommitmentInterface.values service.setup.program) who info))

/-- **The permitted menu simulates the source protocol model.** A source
strategy compiles to its timed calendar policy; the compiled profile has the
source typed outcome law, and every unilateral deviation within the permitted
menu has the typed outcome law of a source deviation (a point mixture). -/
def menuSimulation :
    GameForm.MixtureSimulationOn
      (service.sourceModel.toBehavioralGameForm (instructionCount service.setup.program + 1))
      (service.model.toBehavioralGameForm service.fuel)
      (fun final => service.setup.protocolReadout final.state)
      (fun final => sourceReadout service.setup service.leaks final.state)
      (fun _ _ => True) where
  compileStrategy who strategy :=
    service.timedProfile (Profile.update service.defaultSourcePolicy who strategy) who
  honest_law profile := by
    have same : Profile.map (fun who strategy =>
        service.timedProfile (Profile.update service.defaultSourcePolicy who strategy) who)
        profile = service.timedProfile profile := by
      funext who
      exact service.timedProfile_congr _ _ who (by simp only [Profile.update,
        Function.update_self])
    change (service.model.runBehavioral (Profile.map (fun who strategy =>
      service.timedProfile (Profile.update service.defaultSourcePolicy who strategy) who)
        profile) service.fuel).map _ = _
    rw [same]
    exact sourceServiceTimedProfile_protocol_law service.setup service.leaks service.bounds
      service.values service.initialValues service.capacity service.rosters
      service.opportunities.binding service.calendarTiming service.calendarTiming_fullSupport
      service.network profile
  compiled_considered _ _ := trivial
  deviation_mixture profile who replacement _ := by
    have same : Profile.map (fun who strategy =>
        service.timedProfile (Profile.update service.defaultSourcePolicy who strategy) who)
        profile = service.timedProfile profile := by
      funext who
      exact service.timedProfile_congr _ _ who (by simp only [Profile.update,
        Function.update_self])
    obtain ⟨alternative, law⟩ := service.exists_source_deviation_law profile who replacement
    refine ⟨PMF.pure alternative, ?_⟩
    rw [PMF.pure_bind]
    change (service.model.runBehavioral (Profile.update (Profile.map (fun who strategy =>
      service.timedProfile (Profile.update service.defaultSourcePolicy who strategy) who)
        profile) who replacement) service.fuel).map _ = _
    rw [same]
    exact law

/-- **The menu bound.** Every deviation in the permitted menu against the timed
profile has the base expected payoff of some source deviation. -/
theorem exists_source_deviation_ge {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (source : Profile service.sourceModel.behavioralSignature) (who : Player)
    (alternative : service.model.BehavioralPolicy who) :
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    ∃ deviation : service.sourceModel.BehavioralPolicy who,
      expect (service.model.runBehavioral
        (Profile.update (service.timedProfile source) who alternative) service.fuel)
        (fun final => base final.state who) ≤
      expect (service.sourceModel.runBehavioral (Profile.update source who deviation)
        (instructionCount service.setup.program + 1))
        (fun final => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who)) := by
  intro base
  obtain ⟨deviation, law⟩ := service.exists_source_deviation_law source who alternative
  refine ⟨deviation, le_of_eq ?_⟩
  let value := fun output : Option (State L service.setup.program.terminalCtx) =>
    output.elim 0 (fun state => utility (service.setup.parameterOutcome parameter state) who)
  calc
    _ = expect ((service.model.runBehavioral
          (Profile.update (service.timedProfile source) who alternative) service.fuel).map
          (fun final => sourceReadout service.setup service.leaks final.state)) value := by
      rw [expect_map]
      rfl
    _ = expect ((service.sourceModel.runBehavioral (Profile.update source who deviation)
          (instructionCount service.setup.program + 1)).map
          (fun final => service.setup.protocolReadout final.state)) value := by
      rw [law]
    _ = _ := by
      rw [expect_map]
      rfl

/-- **Approximate Nash correspondence on the audited calendar ledger.** With
an authentic audit sample that observes every forbidden packet with positive
probability and the deposit sized from the base utility and that observation
probability, the compiled raw profile of a source profile is an `ε`-Nash
equilibrium of the audited bounded raw runtime exactly when the source profile
is an `ε`-Nash equilibrium of the source protocol model, for every `ε`. -/
theorem isεNash_compileProfile_iff {Parameter : Type}
    (parameter : State L service.setup.context → Parameter)
    (utility : Parameter × PublicOutcome service.setup.program → Player → ℝ)
    (sample : List (SettledEvidence service.setup) →
      PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (probability : Player → ℝ) (positive : ∀ who, 0 < probability who)
    (coverage : ∀ who actual record, record ∈ actual → record.2.sender = who →
      record.1.permits record.2 = false →
      probability who ≤ ((sample actual).toOuterMeasure {observed | record ∈ observed}).toReal)
    (ε : ℝ) (source : Profile service.sourceModel.behavioralSignature) :
    let base := baseUtility service.setup service.leaks
      (fun state => utility (service.setup.parameterOutcome parameter state))
    let deposit := rosterAuditDeposit service.setup service.leaks service.bounds service.rosters
      service.network base (fun owner => min (probability owner) 1)
    let payoff := TerminalAudit.utility base
      ((runtime service.setup).serviceAuditObservation service.leaks)
      (sourceServiceAudit service.setup service.leaks sample) deposit
    IsεNash ((service.raw.information (initialLaw service.setup) service.planLength
        service.scheduler).toBehavioralGameForm service.fuel)
        (fun history who => payoff history.state who) ε (service.compileProfile source) ↔
      IsεNash (service.sourceModel.toBehavioralGameForm
        (instructionCount service.setup.program + 1))
        (fun final who => (service.setup.protocolReadout final.state).elim 0
          (fun state => utility (service.setup.parameterOutcome parameter state) who))
        ε source :=
  ⟨service.isεNash_of_compileProfile parameter utility sample authentic probability ε source,
    service.isεNash_compileProfile_of_menu_bounds parameter utility sample authentic probability
      positive coverage ε source
      (fun who alternative => service.exists_source_deviation_ge parameter utility source who
        alternative)⟩


end SourceServiceSpec

end Vegas
