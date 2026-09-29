/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceTimedReachability
import Vegas.Game.SourceServiceTimedMixing
import Vegas.Game.SourceServiceDecisionSupport
import Vegas.Game.ServiceRosterLocalEvaluation

/-! # Local continuation comparisons in the full-source service

A native information site of a fully mixed timed approximant reaches the
original source game through four generic steps, proved once here:

* every actual decision has a `DecisionPhase`: its event, roster slot and the
  instructions left in that event's phase;
* a local lottery at the site runs as the lottery over current responses;
* a current response determines the complete typed source terminal law through
  the configuration law at the next event boundary
  (`Vegas.TimedApproximant.response_continuation_law`);
* equal next-boundary configuration laws for all legal responses at every
  history of a site
  give equal prescribed and alternative assessment laws
  (`Vegas.TimedApproximant.comparison_eq_of_phase_invariant`).

The remaining fact is specific to each kind of site: the configuration law at
the next event boundary after each legal response.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The fixed full-source native service: the program setup, passive observation
rule, message bounds, activation rosters and public network policy, together
with the compiler's side conditions on them. -/
structure SourceServiceSpec (Player : Type) [DecidableEq Player] (L : IExpr)
    [IExpr.ResultTypes L] where
  setup : Setup (Player := Player) (L := L)
  leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))
  bounds : MessageBounds (graph setup)
  rosters : (graph setup).EventId → List Player
  network : (runtime setup).NetworkPolicy leaks
  /-- Every binding value the source can choose has a native message form. -/
  values : bounds.CoversBindingValues
  /-- Every supported initial binding table fits the candidate catalogue. -/
  initialValues : ∀ state ∈ (initialLaw setup).support, bounds.CandidateValues state
  /-- The candidate catalogue has a slot for every event. -/
  capacity : (graph setup).order.eventCount ≤ bounds.candidateCount
  /-- Every event actor has an activation at its own event. -/
  opportunities : ActorOpportunities setup rosters

/-- The position of an actual activation of `who`: its event, its slot in that
event's roster, and the service grant in force. -/
structure DecisionPhase (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player) (who : Player)
    (execution : (application setup leaks).Execution) where
  event : (graph setup).EventId
  slot : Nat
  selected : (rosters event)[slot]? = some who
  position : execution.environmentRecall.length =
    (rosterPlanPrefix setup rosters event.val).length + 1 + slot + 1
  granted : execution.application.serviceGrant = some event

namespace DecisionPhase

variable {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {rosters : (graph setup).EventId → List Player} {who : Player}
  {execution : (application setup leaks).Execution}
  (phase : DecisionPhase setup leaks rosters who execution)

/-- The roster visits of the phase that follow the current one. -/
def visits : List Player := (rosters phase.event).drop (phase.slot + 1)

/-- The service plan up to the current activation. -/
def before : List (ServiceInstruction (graph setup)) :=
  rosterPlanPrefix setup rosters phase.event.val ++ [.grant phase.event] ++
    ((rosters phase.event).take phase.slot).map ServiceInstruction.player

/-- The instructions left in the current event's phase. -/
def tail : List (ServiceInstruction (graph setup)) :=
  phase.visits.map ServiceInstruction.player ++ rosterPhaseEnding setup phase.event

/-- The service plan after the current event's phase. -/
def later : List (ServiceInstruction (graph setup)) :=
  rosterPlanSuffix setup rosters (phase.event.val + 1)

theorem roster_split : rosters phase.event =
    (rosters phase.event).take phase.slot ++ who :: phase.visits := by
  have inside := (List.getElem?_eq_some_iff.mp phase.selected).1
  have drop := List.drop_eq_getElem_cons inside
  rw [(List.getElem?_eq_some_iff.mp phase.selected).2] at drop
  simpa only [visits, drop] using ((rosters phase.event).take_append_drop phase.slot).symm

theorem prefix_split :
    rosterPlanPrefix setup rosters (phase.event.val + 1) =
      phase.before ++ .player who :: phase.tail := by
  rw [rosterPlanPrefix_succ, rosterBlock_eq_ending]
  conv_lhs => rw [phase.roster_split]
  simp only [before, tail, List.map_append, List.map_cons, List.append_assoc,
    List.cons_append]

theorem plan_split :
    rosterPlan setup rosters = (phase.before ++ [.player who]) ++ (phase.tail ++ phase.later) := by
  rw [← rosterPlanPrefix_append_suffix setup rosters (phase.event.val + 1), phase.prefix_split]
  simp only [later, List.append_assoc, List.cons_append, List.nil_append]

theorem position_before :
    execution.environmentRecall.length = phase.before.length + 1 := by
  have inside := (List.getElem?_eq_some_iff.mp phase.selected).1
  simp only [before, List.length_append, List.length_singleton, List.length_map,
    List.length_take_of_le inside.le]
  exact phase.position

end DecisionPhase

variable [Fintype Player]

namespace SourceServiceSpec

variable (service : SourceServiceSpec Player L)

abbrev menu := sourceServiceMenu service.setup service.leaks service.bounds service.rosters

abbrev planLength : Nat := (rosterPlan service.setup service.rosters).length

abbrev scheduler := rosterScheduler service.setup service.leaks service.rosters service.network

/-- The source information model of the service's program, with every binding
value admitted. -/
abbrev sourceModel := service.setup.informationModel
  (CommitmentInterface.values service.setup.program)

/-- The native information model of the retained service. -/
abbrev model := service.menu.information (initialLaw service.setup) service.planLength
  service.scheduler

/-- The horizon of the standard native continuation comparisons. -/
abbrev fuel : Nat := 2 * service.planLength + 1

/-- The typed source terminal state read from a native history. -/
abbrev readout (final : (service.menu.protocol (initialLaw service.setup) service.planLength
    service.scheduler).History) :
    Option (State L service.setup.program.terminalCtx) :=
  sourceReadout service.setup service.leaks final.state

/-- Every actual decision in the retained service has a decision phase. -/
theorem exists_decisionPhase (who : Player) (remaining : Nat)
    (execution : (application service.setup service.leaks).Execution)
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩)) :
    Nonempty (DecisionPhase service.setup service.leaks service.rosters who execution) := by
  obtain ⟨event, slot, _, selected, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _,
      grant, _, _, _, _, publicEq, _, position, _⟩ :=
    sourceService_decision_boundary service.setup service.leaks service.bounds service.values
      service.capacity service.rosters service.opportunities.binding service.network
      (failureProfile service.setup.program) who ⟨remaining, some who, execution⟩ trace rfl
  exact ⟨⟨event, slot, selected, position,
    (congrArg PublicView.serviceGrant publicEq).trans grant⟩⟩

/-- The native information of the acting player at an actual decision is its
recall and current view. -/
theorem infoOf_decision {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (history : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).History)
    (current : history.state = some ⟨remaining, some who, execution⟩) :
    service.model.infoOf who history.trace =
      some (execution.recall who,
        execution.observe (application service.setup service.leaks) who) := by
  change (service.menu.signals (initialLaw service.setup) service.planLength
    service.scheduler).infoOf who history.trace = _
  rw [service.menu.info, current]
  simp only [ReactiveApplication.observe, ↓reduceIte]

/-- Every choice available at an actual decision is a legal current response. -/
theorem choice_allowed {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (history : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).History)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    {info : service.model.InfoState who}
    (observed : service.model.infoOf who history.trace = info)
    (choice : service.model.Choice who info) :
    choice.1.getD ⟨none⟩ ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who) := by
  subst info
  have allowed := Eq.mp (congrArg (fun input => choice.1 ∈ service.model.menu who input)
    (service.infoOf_decision history current)) choice.2
  obtain ⟨response, allowed, same⟩ := allowed
  simpa only [same, Option.getD_some] using allowed

end SourceServiceSpec

/-- One fully mixed timed approximant: a source profile compiled with a common
timing law, its admissibility, and a fully mixed native assessment whose
strategy is exactly that compilation. -/
structure TimedApproximant (service : SourceServiceSpec Player L) where
  timing : TimingLaw service.setup service.rosters
  timingFull : ∀ event who owned, FullSupport (timing event who owned)
  profile : BehavioralProfile service.setup.program
  admitted : ∀ who, (profile who).Admitted service.setup.program
    (CommitmentInterface.values service.setup.program)
  covered : ∀ who, service.menu.Admissible (initialLaw service.setup) service.planLength
    service.scheduler who
      (sourceServiceTimedPolicy service.setup service.leaks service.rosters timing profile who)
  effective : ∀ who, (profile who).EffectiveDisclosures service.setup.program []
    (Revelations.initial service.setup.context)
  supports : ∀ who, (profile who).SupportsEffectiveChoices service.setup.program
    (CommitmentInterface.values service.setup.program) []
      (Revelations.initial service.setup.context)
  assessment : service.model.BehavioralAssessment
  strategy : assessment.strategy = fun who =>
    service.menu.restrictPolicy (initialLaw service.setup) service.planLength service.scheduler
      who (sourceServiceTimedPolicy service.setup service.leaks service.rosters timing profile who)
  mixed : assessment.IsFullyMixed

namespace TimedApproximant

variable {service : SourceServiceSpec Player L}

/-- The actual native Bayes assessment of a fully supported source strategy
compiled with a full-support timing law. The sequential-equilibrium theorem
takes these assessments along one fully supported Bayes sequence of the source
equilibrium
(`Vegas.sourceService_consistent_supported_sequence`). -/
def ofSource (service : SourceServiceSpec Player L)
    (timing : TimingLaw service.setup service.rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (source : Profile service.sourceModel.behavioralSignature)
    (full : ∀ who info, FullSupport (source who info)) : TimedApproximant service :=
  let admission := CommitmentInterface.values service.setup.program
  let original := service.setup.decodeBehavioralProfile admission source
  let normalized := normalizeDisclosureProfile service.setup.program []
    (Revelations.initial service.setup.context) original
  have permitted (who : Player) : (original who).Admitted service.setup.program admission :=
    ((service.setup.behavioralPolicyEquiv admission who).symm (source who)).2
  let native := InformationModel.BehavioralAssessment.ofStrategy
    (sourceServiceTimedProfile service.setup service.leaks service.bounds service.rosters
      service.network timing original)
  have nativeMixed : native.IsFullyMixed :=
    sourceServiceTimedProfile_fullyMixed service.setup service.leaks service.bounds
      service.values service.initialValues service.capacity service.rosters
      service.opportunities.binding service.network timing timingFull source full
  { timing := timing
    timingFull := timingFull
    profile := normalized
    admitted := normalized_sourceService_admitted service.setup original permitted
    covered := sourceServiceTimedPolicy_admissible service.setup service.leaks service.bounds
      service.values service.initialValues service.capacity service.rosters
      service.opportunities.binding service.network timing timingFull normalized
      (normalized_sourceService_admitted service.setup original permitted)
    effective := fun who => (original who).normalizeDisclosureFrom_effective
      service.setup.program [] (Revelations.initial service.setup.context)
        (fun view => PMF.pure view.2)
    supports := sourceService_normalized_support service.setup source full
    assessment := native.bayes nativeMixed
      (service.menu.decisionInformationAntichain (initialLaw service.setup) service.planLength
        service.scheduler)
    strategy := rfl
    mixed := native.bayes_isFullyMixed nativeMixed _ }

theorem ofSource_strategy (service : SourceServiceSpec Player L)
    (timing : TimingLaw service.setup service.rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (source : Profile service.sourceModel.behavioralSignature)
    (full : ∀ who info, FullSupport (source who info)) :
    (ofSource service timing timingFull source full).assessment.strategy =
      sourceServiceTimedProfile service.setup service.leaks service.bounds service.rosters
        service.network timing (service.setup.decodeBehavioralProfile
          (CommitmentInterface.values service.setup.program) source) :=
  rfl

theorem ofSource_bayes (service : SourceServiceSpec Player L)
    (timing : TimingLaw service.setup service.rosters)
    (timingFull : ∀ event who owned, FullSupport (timing event who owned))
    (source : Profile service.sourceModel.behavioralSignature)
    (full : ∀ who info, FullSupport (source who info)) :
    InformationModel.BehavioralAssessment.IsBayesConsistent service.model
      (ofSource service timing timingFull source full).assessment
      (service.menu.decisionInformationAntichain (initialLaw service.setup) service.planLength
        service.scheduler) :=
  InformationModel.BehavioralAssessment.bayes_isBayesConsistent _
    (sourceServiceTimedProfile_fullyMixed service.setup service.leaks service.bounds
      service.values service.initialValues service.capacity service.rosters
      service.opportunities.binding service.network timing timingFull source full) _

end TimedApproximant

namespace TimedApproximant

variable {service : SourceServiceSpec Player L} (approx : TimedApproximant service)

/-- The native timed compilation of the approximant's source profile. -/
abbrev players : Player → (application service.setup service.leaks).Policy :=
  sourceServiceTimedPolicy service.setup service.leaks service.rosters approx.timing
    approx.profile

/-- The actual execution of the current phase after one current response. -/
def phaseLaw {who : Player} {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action) :
    PMF (application service.setup service.leaks).Execution :=
  (runtime service.setup).runInteractionPlan service.leaks approx.players service.network
    phase.tail (execution.respond (application service.setup service.leaks) who response)

/-- The configuration law at the next event boundary after one current
response. Only this configuration determines the later source continuation. -/
def phaseConfigLaw {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action) :
    PMF (graph service.setup).Config :=
  (approx.phaseLaw phase response).map (fun final => final.application.config)

/-- The complete typed source terminal law after one current response. -/
def responseReadout {who : Player}
    {execution : (application service.setup service.leaks).Execution}
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action) :
    PMF (Option (State L service.setup.program.terminalCtx)) :=
  ((runtime service.setup).runInteractionPlan service.leaks approx.players service.network
    (phase.tail ++ phase.later)
    (execution.respond (application service.setup service.leaks) who response)).map
      (fun final => sourceReadout service.setup service.leaks
        ((application service.setup service.leaks).finished final))

/-- The source continuation from the event boundary after a phase. -/
def boundaryContinuation (count : Nat) (config : (graph service.setup).Config) :
    PMF (Option (State L service.setup.program.terminalCtx)) :=
  (service.setup.continuationLaw approx.profile
    (sourceServicePrefix? service.setup count config)).map some

/-- The single continuation bridge: after any legal response at an actual
decision, the complete typed source terminal law is the source continuation
from the next event boundary, averaged over the actual configuration law at
that boundary. The suffix reachability is derived from native full mixing, so
responses used as deviations are included. -/
theorem response_continuation_law {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (response : (application service.setup service.leaks).Action)
    (allowed : response ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who)) :
    approx.responseReadout phase response =
      (approx.phaseConfigLaw phase response).bind
        (approx.boundaryContinuation (phase.event.val + 1)) := by
  unfold responseReadout phaseConfigLaw phaseLaw
  rw [runInteractionPlan_append, PMF.map_bind, PMF.bind_map]
  apply bind_congr_on_support _
  intro final reached
  have supported := roster_fullyMixed_response_prefix_support service.setup service.leaks
    service.rosters service.network service.menu approx.players approx.covered approx.assessment
    approx.strategy approx.mixed who remaining execution trace (phase.event.val + 1) phase.before
    phase.tail phase.prefix_split phase.position_before response allowed final reached
  exact sourceServiceTimedPolicy_continuation_law service.setup service.leaks service.bounds
    service.values service.capacity service.rosters service.opportunities.binding approx.timing
    service.network approx.profile approx.covered approx.effective who (phase.event.val + 1)
    phase.event.isLt final supported

/-- Two legal responses with the same next-boundary configuration law have the
same complete typed source terminal law. -/
theorem responseReadout_congr {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩))
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    (first second : (application service.setup service.leaks).Action)
    (firstAllowed : first ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (secondAllowed : second ∈ service.menu.actions who (execution.recall who)
      (execution.observe (application service.setup service.leaks) who))
    (same : approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second) :
    approx.responseReadout phase first = approx.responseReadout phase second := by
  rw [approx.response_continuation_law trace phase first firstAllowed,
    approx.response_continuation_law trace phase second secondAllowed, same]

open Classical in
/-- A local lottery at an actual history runs as the same lottery over current
responses, each followed by its complete continuation. -/
theorem local_law_readout {who : Player} {remaining : Nat}
    {execution : (application service.setup service.leaks).Execution}
    (history : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).History)
    (current : history.state = some ⟨remaining, some who, execution⟩)
    (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
    {info : service.model.InfoState who}
    (observed : service.model.infoOf who history.trace = info)
    (law : PMF (service.model.Choice who info)) :
    (service.model.runBehavioralFrom (Profile.update (sig := service.model.behavioralSignature)
      approx.assessment.strategy who ((approx.assessment.strategy who).withLaw info law))
        service.fuel history).map
        service.readout =
      (law.map (fun choice => choice.1.getD ⟨none⟩)).bind (approx.responseReadout phase) := by
  have physical := roster_local_law_complete_state service.setup service.leaks service.rosters
    service.network service.menu approx.players approx.covered history who remaining execution
    current (phase.before ++ [.player who]) (phase.tail ++ phase.later) phase.plan_split
    (by simpa only [List.length_append, List.length_singleton] using phase.position_before)
    observed law
  have mapped := congrArg (PMF.map (sourceReadout service.setup service.leaks)) physical
  simp only [PMF.map_comp, Function.comp_def, PMF.map_bind] at mapped
  rw [approx.strategy]
  exact mapped

open Classical in
/-- At a site where every legal response leaves the same configuration law at
the next event boundary, every local lottery has the prescribed complete
continuation law, for every belief over the site. -/
theorem comparison_eq_of_phase_invariant (who : Player)
    (site : service.model.InformationSite who)
    (invariant : ∀ (history : (service.menu.protocol (initialLaw service.setup)
        service.planLength service.scheduler).History) remaining execution,
      history.state = some ⟨remaining, some who, execution⟩ →
      service.model.infoOf who history.trace = site.1 →
      ∀ (phase : DecisionPhase service.setup service.leaks service.rosters who execution)
        (first second : (application service.setup service.leaks).Action),
        first ∈ service.menu.actions who (execution.recall who)
          (execution.observe (application service.setup service.leaks) who) →
        second ∈ service.menu.actions who (execution.recall who)
          (execution.observe (application service.setup service.leaks) who) →
        approx.phaseConfigLaw phase first = approx.phaseConfigLaw phase second)
    (law : PMF (service.model.Choice who site.1)) :
    let comparison := service.model.assessmentComparison service.readout service.fuel
      approx.assessment who (site, (approx.assessment.strategy who).withLaw site.1 law)
    comparison.alternative = comparison.prescribed := by
  intro comparison
  simp only [comparison, InformationModel.assessmentComparison,
    InformationModel.BehavioralAssessment.continuationContext, PMF.map_bind]
  apply bind_congr_on_support _
  intro history _
  have active := InformationModel.InformationSite.active service.model site history
  obtain ⟨control, current⟩ : ∃ control, history.1.state = some control := by
    cases state : history.1.state with
    | none => rw [state] at active; cases active
    | some control => exact ⟨control, rfl⟩
  have actor : control.actor = some who := by rw [current] at active; exact active
  obtain ⟨remaining, actorValue, execution⟩ := control
  change actorValue = some who at actor
  subst actorValue
  have trace : (service.menu.protocol (initialLaw service.setup) service.planLength
      service.scheduler).Trace (some ⟨remaining, some who, execution⟩) :=
    current ▸ history.1.trace
  obtain ⟨phase⟩ := service.exists_decisionPhase who remaining execution trace
  let reference := (approx.assessment.strategy who site.1).support_nonempty.choose
  have referenceAllowed := service.choice_allowed history.1 current history.2 reference
  have constant (choiceLaw : PMF (service.model.Choice who site.1)) :
      (service.model.runBehavioralFrom (Profile.update (sig := service.model.behavioralSignature)
        approx.assessment.strategy who ((approx.assessment.strategy who).withLaw site.1 choiceLaw))
          service.fuel history.1).map service.readout =
        approx.responseReadout phase (reference.1.getD ⟨none⟩) := by
    rw [approx.local_law_readout history.1 current phase history.2 choiceLaw, PMF.bind_map]
    calc
      _ = choiceLaw.bind (fun _ =>
          approx.responseReadout phase (reference.1.getD ⟨none⟩)) := by
        apply bind_congr_on_support _
        intro choice _
        have allowed := service.choice_allowed history.1 current history.2 choice
        exact approx.responseReadout_congr trace phase _ _ allowed referenceAllowed
          (invariant history.1 remaining execution current history.2 phase _ _ allowed
            referenceAllowed)
      _ = _ := PMF.bind_const _ _
  have prescribed := constant (approx.assessment.strategy who site.1)
  rw [InformationModel.BehavioralPolicy.withLaw_eq_self] at prescribed
  exact (constant law).trans prescribed.symm

end TimedApproximant

end Vegas
