/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import VegasTests.SelectiveAssociationOpeningIncentives
import Vegas.Pending.ReactiveObservedState

/-! # Explicit withholding is sequentially suboptimal

Withholding remains an ordinary legal raw response. At a granted publication
whose own binding succeeded, its fresh envelope is included and records failure;
the legal ordinary opening instead guarantees at least three more payoff units.
-/

noncomputable section

namespace VegasTests.SelectiveAssociation

open Vegas Vegas.EventGraphRuntime Interaction GameTheory.Math.Probability
open GameTheory GameTheory.Protocol

def nativeWithholdSubmission (who : Player) : WitnessedSubmission nativeGraph :=
  disclosureSubmission (.withhold (nativePublicationEvent who))

def nativeWithholdAction (who : Player) : nativeApp.Action :=
  ⟨some (.submit (nativeWithholdSubmission who))⟩

theorem native_withhold_available (who : Player) (past : List nativeApp.PlayerEntry)
    (view : nativeApp.PlayerView) :
    nativeWithholdAction who ∈ nativeMenu.actions who past view := by
  change nativeWithholdAction who ∈
    (nativeBounds.rawMenu nativeRuntime nativeLeaks).actions who past view
  rw [MessageBounds.rawMenu, ReactiveApplication.ResponseMenu.fromSubmissions_mem]
  change nativeWithholdSubmission who ∈ nativeBounds.submissions _
  rw [MessageBounds.submissions_mem]
  exact ⟨⟨trivial, trivial⟩, trivial⟩

theorem native_withhold_accepted (state : State nativeGraph) (who : Player)
    (ready : state.config.cut.Ready (nativePublicationEvent who))
    (timely : state.WithinDeadline nativeRuntime (nativePublicationEvent who))
    (remembered : state.remembered (nativePublicationEvent who) = none) (serial : Nat) :
    ∃ next, handle nativeRuntime state
        ⟨(who, serial), .withhold (nativePublicationEvent who)⟩ = some next ∧
      (nativePublicationRef who).get? next.config.store = some .failure := by
  obtain ⟨checks, codeEq, node, _⟩ := native_publication_rule who
  refine ⟨_, handle_withhold_unremembered_eq nativeRuntime state (who, serial)
    (nativePublicationEvent who) who .bool (nativeBindingRef who) checks
    (native_publication_output who) codeEq node ready timely rfl remembered, ?_⟩
  fin_cases who <;> simp [nativePublicationRef, nativePublicationEvent, State.complete,
    EventGraph.Config.store, EventGraph.FieldRef.get?]

theorem native_withhold_realizes (players : Player → nativeApp.Policy)
    (execution : nativeApp.Execution) (who : Player)
    (serials : execution.network.SerialsBeforeNext)
    (ready : execution.application.config.cut.Ready (nativePublicationEvent who))
    (timely : execution.application.WithinDeadline nativeRuntime (nativePublicationEvent who))
    (remembered : execution.application.remembered (nativePublicationEvent who) = none) :
    ∃ next, (nativePublicationRef who).get? next.config.store = some .failure ∧
      (nativeRuntime.interactionStep nativeLeaks players nativeNetwork
        (.includeLatest (nativePublicationEvent who) who)
        (execution.respond nativeApp who (nativeWithholdAction who))).map
          (fun result => result.application) = FinDist.pure next := by
  obtain ⟨next, accepted, failed⟩ := native_withhold_accepted execution.application who ready timely
    remembered (execution.network.nextSerial who)
  refine ⟨next, failed, ?_⟩
  have selected : nativeRuntime.reactiveLatest nativeLeaks (nativePublicationEvent who) who
      ((execution.respond nativeApp who (nativeWithholdAction who)).observeEnvironment nativeApp) =
        .include (who, execution.network.nextSerial who) :=
    nativeRuntime.reactiveLatest_after_submit nativeLeaks who
      (nativePublicationEvent who) execution serials (nativeWithholdSubmission who) rfl
  have lookup : (execution.respond nativeApp who (nativeWithholdAction who)).network.lookup
      (who, execution.network.nextSerial who) =
        some ⟨(who, execution.network.nextSerial who),
          (nativeWithholdSubmission who).emit execution.application who
            (execution.network.known who)⟩ := serials.lookup_submit who _
  simp only [interactionStep, interactionInstruction, selected, FinDist.pure_bind,
    ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    FinDist.map_pure, FinDist.pure_bind, ReactiveApplication.Command.actor?,
    ReactiveApplication.resume, FinDist.map_pure]
  unfold ReactiveApplication.Execution.includePending MessageNetwork.includePending
  rw [lookup]
  change FinDist.pure ((handle nativeRuntime execution.application
    ⟨(who, execution.network.nextSerial who), .withhold (nativePublicationEvent who)⟩).getD
      execution.application) = _
  rw [accepted]
  rfl

theorem native_withhold_finish (players : Player → nativeApp.Policy)
    (control : nativeApp.Control) (trace : nativeArena.Trace (some control))
    (who : Player) (active : control.actor = some who)
    (granted : control.execution.application.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉ control.execution.application.config.cut.completed)
    (withholds : players who (control.execution.recall who)
      (control.execution.observe nativeApp who) = FinDist.pure (nativeWithholdAction who))
    (result : nativeApp.ProtocolState)
    (supported : result ∈ (nativeApp.finish (FinDist.pure nativeInitial) nativeHorizon
      nativeScheduler players (some control)).support) :
    ∃ final, result = some final ∧
      (nativePublicationRef who).get? final.execution.application.config.store = some .failure := by
  have cursor := (native_decision_cursor (nativePublicationEvent who) control trace who active
    granted).2
  have ownerActive : control.actor = some (nativeOwner (nativePublicationEvent who)) := by
    rwa [native_publication_owner]
  obtain ⟨_, service⟩ := native_decision_service (nativePublicationEvent who) control trace
    ownerActive cursor
  obtain ⟨ready, timely⟩ := service.resolve_left unfinished
  have remembered := (nativeRuntime.reactiveRememberedInvariant nativeLeaks
    (fun table => table (nativePublicationEvent who) = none)).history
      (FinDist.pure nativeInitial) nativeHorizon nativeScheduler (by
        intro state member
        cases FinDist.mem_support_pure.mp member
        rfl)
      (nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace)
  obtain ⟨next, failed, law⟩ := native_withhold_realizes players control.execution who
    (native_history_invariants control trace).2.2 ready timely remembered
  apply native_response_finish players control trace who _ .failure active granted withholds
    _ result supported
  intro middle middleMem
  have same : middle.application = next := by
    apply FinDist.mem_support_pure.mp
    rw [← law, FinDist.support_map]
    exact ⟨middle, middleMem, rfl⟩
  simpa only [same] using failed

open Classical in
/-- Explicit withholding has zero probability at every sequentially rational
usable opening site, for each player and every belief over its legal fiber. -/
theorem native_not_supported_withhold
    (assessment : nativeModel.BehavioralAssessment) (who : Player)
    (site : nativeModel.InformationSite who)
    (past : List nativeApp.PlayerEntry) (view : nativeApp.PlayerView)
    (siteEq : site.1 = some (past, view)) (bit : Bool)
    (granted : view.application.publicView.serviceGrant = some (nativePublicationEvent who))
    (unfinished : nativePublicationEvent who ∉
      view.application.publicView.observation.completionOrder)
    (stored : (nativeBindingRef who).get? view.application.observation.store = some (.success bit))
    (rational : assessment.IsSequentiallyRationalAt site
      (assessment.continuationContext site (fun history => nativeUtility who history.state)
        (2 * nativeHorizon + 1)))
    (choice : nativeModel.Choice who site.1)
    (withhold : choice.1 = some (nativeWithholdAction who)) :
    choice ∉ (assessment.strategy who site.1).support := by
  classical
  apply native_not_supported_failing_opening assessment who site past view siteEq bit granted
    unfinished stored rational choice
  intro history final finalMem
  obtain ⟨control, stateEq, active, recall, observed⟩ :=
    native_information_control who past view ⟨history.1, history.2.trans siteEq⟩
  rcases history with ⟨⟨state, trace⟩, information⟩
  change state = some control at stateEq
  subst state
  let profile := Profile.update (sig := nativeModel.behavioralSignature) assessment.strategy who
    ((assessment.strategy who).commit site.1 choice)
  let players := nativeMenu.decodeProfile (FinDist.pure nativeInitial) nativeHorizon
    nativeScheduler profile
  have grant : control.execution.application.serviceGrant = some (nativePublicationEvent who) := by
    rw [← observed] at granted
    exact granted
  have incomplete : nativePublicationEvent who ∉
      control.execution.application.config.cut.completed := by
    rw [← observed] at unfinished
    change nativePublicationEvent who ∉
      control.execution.application.config.history.map EventGraph.Completion.event at unfinished
    exact fun completed => unfinished
      ((control.execution.application.config.history_exact _).mpr completed)
  have chooses : players who (control.execution.recall who)
      (control.execution.observe nativeApp who) = FinDist.pure (nativeWithholdAction who) := by
    have infoEq : some (control.execution.recall who,
        control.execution.observe nativeApp who) = site.1 :=
      (congrArg some (Prod.ext recall observed)).trans siteEq.symm
    simp only [players, ReactiveApplication.ResponseMenu.decodeProfile,
      ReactiveApplication.decodePolicy, ReactiveApplication.ResponseMenu.embedPolicy,
      profile, Profile.update_same]
    rw [infoEq]
    simp only [InformationModel.BehavioralPolicy.commit_self, FinDist.map_pure]
    change FinDist.pure (choice.1.getD ⟨none⟩) = _
    rw [withhold]
    rfl
  have law := nativeMenu.run_eq_finish (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
    profile (2 * nativeHorizon + 1) ⟨some control, trace⟩ (by
      change nativeApp.rank nativeHorizon (some control) ≤ 2 * nativeHorizon + 1
      have bound := nativeApp.trace_bound (FinDist.pure nativeInitial) nativeHorizon nativeScheduler
        (nativeMenu.toRawTrace (FinDist.pure nativeInitial) nativeHorizon nativeScheduler trace)
      omega)
  apply native_withhold_finish players control trace who active grant incomplete chooses final.state
  rw [← law, FinDist.support_map]
  exact ⟨final, finalMem, rfl⟩

end VegasTests.SelectiveAssociation
