/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.SequentialPhaseStoppedLaw
import Vegas.Game.SequentialPhaseTraceProjection
import Vegas.Pending.ExclusionInvariant
import Interaction.ReactiveInvariantPrefix
import GameTheoryExtensions.Analysis.Protocol.StoppedBayes

/-! # Actual clear-site Bayes beliefs on physical recovery states -/

noncomputable section

namespace Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy

open SourceProgram EventGraph Interaction GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {Γ : SourceCtx Player L} {O : Finset VarId}
  (program : SourceProgram Player L Γ O)
  (runtime : EventGraphRuntime ((toEventGraph program).withMode .sequential))
  (leaks : MessageNetwork.ObservationRule Player
    (CommitAttemptPacket ((toEventGraph program).withMode .sequential)))
  (menu : (phaseApplication runtime leaks).ResponseMenu)
  (bounds : MessageBounds ((toEventGraph program).withMode .sequential))
  (included : menu.IncludedIn (PhaseCount.onePacketMenu runtime leaks bounds))
  (inputs : PMF ((toEventGraph program).withMode .sequential).Inputs) (horizon : Nat)
  (scheduler : (phaseApplication runtime leaks).Scheduler)

local notation "plan" => sequentialRuntimePhasePlan program
local notation "recoveryLeaks" => PhaseNativeProjection.nativeLeaks leaks plan
local notation "P" => phaseApplication runtime leaks
local notation "R" => recoveryApplication runtime recoveryLeaks
local notation "phaseInitial" => inputs.map (PhaseRuntimeState.initial plan)
local notation "recoveryInitial" =>
  inputs.map (fun input => RecoveryState.mk (State.initial input) ∅)
local notation "recoveryScheduler" =>
  SequentialPhaseSchedulerInformation.scheduler program runtime leaks recoveryLeaks scheduler
local notation "M" =>
  ReactiveApplication.ResponseMenu.information (menu) phaseInitial horizon scheduler
local notation "N" =>
  ReactiveApplication.information (R) recoveryInitial horizon recoveryScheduler
local notation "projection" => PhaseRecoveryProjection.protocolState runtime leaks recoveryLeaks
local notation "projectInfo" => PhaseRecoveryProjection.information runtime leaks recoveryLeaks
local notation "decode" =>
  SequentialPhasePlayerInformation.information program runtime leaks recoveryLeaks
local notation "phaseClear" => ReactiveApplication.stateInvariant (app := P)
  (fun state => RecoveryState.excluded (PhaseRuntimeState.current state) = ∅)
local notation "recoveryClear" => ReactiveApplication.stateInvariant (app := R)
  (fun state => RecoveryState.excluded state = ∅)

omit [Fintype Player] in
private theorem phase_clear_of_observe_eq (who : Player) (state : (P).ProtocolState)
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (observed : (P).observe who state = some (past, view))
    (clear : view.application.2.excluded = ∅) : phaseClear state := by
  cases state with
  | none => cases observed
  | some current =>
      by_cases active : current.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        have flags := congrArg (fun pair => pair.2.application.2.excluded)
          (Option.some.inj observed)
        exact flags.trans clear
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        cases observed

omit [Fintype Player] in
private theorem recovery_clear_of_observe_eq (who : Player) (state : (R).ProtocolState)
    (past : List (R).PlayerEntry) (view : (R).PlayerView)
    (observed : (R).observe who state = some (past, view))
    (clear : view.application.2 = ∅) : recoveryClear state := by
  cases state with
  | none => cases observed
  | some current =>
      by_cases active : current.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        have flags := congrArg (fun pair => pair.2.application.2) (Option.some.inj observed)
        exact flags.trans clear
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at observed
        cases observed

include included in
private theorem clear_information_history
    (history : ((menu).protocol phaseInitial horizon scheduler).History)
    (clear : phaseClear history.state) (who : Player) :
    decode (projectInfo ((P).observe who history.state)) = (P).observe who history.state := by
  cases stateEq : history.state with
  | none => rfl
  | some current =>
      have trace : ((menu).protocol phaseInitial horizon scheduler).Trace (some current) :=
        stateEq ▸ history.trace
      rw [stateEq] at clear
      exact SequentialPhasePlayerInformation.information_history program runtime leaks recoveryLeaks
        bounds inputs horizon scheduler
          (included.trace phaseInitial horizon scheduler trace) clear who

include included in
/-- A clear phase decision input and its old projection have exactly the same
actual counted-history fiber, including arbitrary histories outside equilibrium support. -/
theorem clear_site_fiber_projected (who : Player) (site : (M).InformationSite who)
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (siteInput : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (history : ((menu).protocol phaseInitial horizon scheduler).History) :
    (M).infoOf who history.trace = site.1 ↔
      (R).observe who (projection history.state) = projectInfo site.1 := by
  have observed (current : ((menu).protocol phaseInitial horizon scheduler).History) :
      (M).infoOf who current.trace = (P).observe who current.state :=
    (menu).info phaseInitial horizon scheduler who current.trace
  have decodedSite : decode (projectInfo site.1) = site.1 := by
    obtain ⟨witness, _running, _response, _allowed⟩ := site.2
    have input : (P).observe who witness.1.state = some (past, view) :=
      (observed witness.1).symm.trans (witness.2.trans siteInput)
    have restored := clear_information_history program runtime leaks menu bounds included inputs
      horizon scheduler
      witness.1 (phase_clear_of_observe_eq program runtime leaks who witness.1.state past view
        input clear) who
    rw [← observed witness.1, witness.2] at restored
    exact restored
  have projectedObserve : (R).observe who (projection history.state) =
      projectInfo ((P).observe who history.state) :=
    PhaseRecoveryProjection.observe_state runtime leaks recoveryLeaks who history.state
  rw [observed]
  constructor
  · intro equal
    rw [projectedObserve, equal]
  · intro equal
    have oldInput : (R).observe who (projection history.state) =
        some ((past.map (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks)),
          PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks view) := by
      simpa only [siteInput, PhaseRecoveryProjection.information, Option.map_some] using equal
    have currentClear : phaseClear history.state := by
      have retained := recovery_clear_of_observe_eq program runtime leaks who
        (projection history.state) _ _ oldInput clear
      cases stateEq : history.state with
      | none => trivial
      | some current =>
          rw [stateEq] at retained
          exact retained
    have restored := clear_information_history program runtime leaks menu bounds included inputs
      horizon scheduler
      history currentClear who
    rw [projectedObserve] at equal
    exact restored.symm.trans ((congrArg decode equal).trans decodedSite)

omit [Fintype Player] in
private theorem clear_before_of_monotone {app : ReactiveApplication Player}
    (flags : app.State → Finset Player)
    (grows : app.StepRelation (fun before after => flags before ⊆ flags after))
    (initial : PMF app.State) (turns : Nat) (choose : app.Scheduler)
    (first last : (app.protocol initial turns choose).History)
    (path : (app.protocol initial turns choose).HistoryReaches first last)
    (after : app.Control) (lastEq : last.state = some after)
    (clear : flags after.execution.application = ∅) :
    ReactiveApplication.stateInvariant (fun state => flags state = ∅) first.state := by
  cases firstEq : first.state with
  | none => trivial
  | some before =>
      have invariant (lower : Finset Player) : app.Invariant (fun state => lower ⊆ flags state) := {
        submit := fun state who material bound => bound.trans (grows.submit state who material)
        handle := fun state message next bound accepted =>
          bound.trans (grows.handle state message next accepted)
        environment := fun state command next bound reached =>
          bound.trans (grows.environment state command next reached) }
      have bound := (invariant (flags before.execution.application)).reaches initial turns choose
        path.choose_spec before after firstEq lastEq (Finset.Subset.refl _)
      exact Finset.subset_empty.mp (by simpa only [clear] using bound)

omit [Fintype Player] in
private theorem phase_site_avoids_exclusion
    (who : Player) (site : (M).InformationSite who)
    (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (siteInput : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (prior : ((menu).protocol phaseInitial horizon scheduler).History)
    (atSite : (M).InformationHistory who site.1)
    (path : ((menu).protocol phaseInitial horizon scheduler).HistoryReaches prior atSite.1) :
      ¬ ¬ phaseClear prior.state := by
    have input : (P).observe who atSite.1.state = some (past, view) :=
      ((menu).info phaseInitial horizon scheduler who atSite.1.trace).symm.trans
        (atSite.2.trans siteInput)
    have atSiteClear := phase_clear_of_observe_eq program runtime leaks who atSite.1.state past view
      input clear
    obtain ⟨after, endpoint⟩ : ∃ after, atSite.1.state = some after := by
      cases stateEq : atSite.1.state with
      | none => rw [stateEq] at input; cases input
      | some after => exact ⟨after, rfl⟩
    rw [endpoint] at atSiteClear
    have rawPath := (menu).reaches_raw phaseInitial horizon scheduler path.choose_spec
    have previous := clear_before_of_monotone
      (fun state : (P).State => state.current.excluded)
      (phaseApplication_exclusion_monotone runtime leaks) phaseInitial horizon scheduler
      ((menu).toRawHistory phaseInitial horizon scheduler prior)
      ((menu).toRawHistory phaseInitial horizon scheduler atSite.1) ⟨_, rawPath⟩
      after endpoint atSiteClear
    exact not_not.mpr previous

omit [Fintype Player] in
private theorem recovery_site_avoids_exclusion
    (who : Player) (site : (N).InformationSite who)
    (past : List (R).PlayerEntry) (view : (R).PlayerView)
    (siteInput : site.1 = some (past, view)) (clear : view.application.2 = ∅)
    (prior : ((R).protocol recoveryInitial horizon recoveryScheduler).History)
    (atSite : (N).InformationHistory who site.1)
    (path : ((R).protocol recoveryInitial horizon recoveryScheduler).HistoryReaches
        prior atSite.1) : ¬ ¬ recoveryClear prior.state := by
  have observed (history : ((R).protocol recoveryInitial horizon recoveryScheduler).History) :
      (N).infoOf who history.trace = (R).observe who history.state :=
    (R).info recoveryInitial horizon recoveryScheduler who history.trace
  have input : (R).observe who atSite.1.state = some (past, view) :=
    (observed atSite.1).symm.trans (atSite.2.trans siteInput)
  have atSiteClear := recovery_clear_of_observe_eq program runtime leaks who atSite.1.state
    past view input clear
  obtain ⟨after, endpoint⟩ : ∃ after, atSite.1.state = some after := by
    cases stateEq : atSite.1.state with
    | none => rw [stateEq] at input; cases input
    | some after => exact ⟨after, rfl⟩
  rw [endpoint] at atSiteClear
  have previous := clear_before_of_monotone
    (fun state : (R).State => state.excluded)
    (recoveryApplication_exclusion_monotone runtime recoveryLeaks) recoveryInitial horizon
    recoveryScheduler prior atSite.1 path after endpoint atSiteClear
  exact not_not.mpr previous

include included in
/-- Conditioning the actual phase first-hit law on a clear old input yields
its true Bayes belief on the complete projected physical recovery state. -/
theorem phase_bayesBelief_eq_stopped_recovery_state
    (profile : ∀ who, (M).BehavioralPolicy who) (who : Player)
    (site : (M).InformationSite who) (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (siteInput : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (positive : 0 < (M).informationMass profile who site) :
    let certificate := ((menu).bounded phaseInitial horizon scheduler).wellFoundedHistories
    let stopped := (M).runBehavioralUntil certificate profile
      (fun history => ¬ phaseClear history.state ∨
        (R).observe who (projection history.state) = projectInfo site.1)
      ((menu).protocol phaseInitial horizon scheduler).initHistory
    fiberPosterior (stopped.map (fun history => projection history.state)) ((R).observe who)
      (projectInfo site.1) =
      ((M).bayesBelief profile who site
        ((menu).decisionInformationAntichain phaseInitial horizon scheduler who site) positive).map
          (fun history => projection history.1.state) := by
  classical
  dsimp only
  have avoids := phase_site_avoids_exclusion program runtime leaks menu inputs
    horizon scheduler who site past view siteInput clear
  have result := (M).bayesBelief_eq_stopped_fiber_map
    ((menu).bounded phaseInitial horizon scheduler).wellFoundedHistories
    ((menu).bounded phaseInitial horizon scheduler) profile who site
    ((menu).decisionInformationAntichain phaseInitial horizon scheduler who site) positive
    (fun history => ¬ phaseClear history.state) avoids (fun history => projection history.state)
    ((R).observe who) (projectInfo site.1) (fun history _supported =>
      clear_site_fiber_projected program runtime leaks menu bounds included inputs horizon scheduler
        who site
        past view siteInput clear history)
  dsimp only at result
  have stopping : (fun history : ((menu).protocol phaseInitial horizon scheduler).History =>
      ¬ phaseClear history.state ∨ (M).infoOf who history.trace = site.1) =
      fun history => ¬ phaseClear history.state ∨
        (R).observe who (projection history.state) = projectInfo site.1 := by
    funext history
    exact propext (or_congr Iff.rfl (clear_site_fiber_projected program runtime leaks menu bounds
      included inputs horizon scheduler who site past view siteInput clear history))
  rw [stopping] at result
  exact result

/-- At an actual clear old decision site, the stopped state posterior is the
original raw recovery Bayes belief on the whole physical protocol state. -/
theorem recovery_bayesBelief_eq_stopped_state
    (profile : ∀ who, (N).BehavioralPolicy who) (who : Player)
    (site : (N).InformationSite who) (past : List (R).PlayerEntry) (view : (R).PlayerView)
    (siteInput : site.1 = some (past, view)) (clear : view.application.2 = ∅)
    (positive : 0 < (N).informationMass profile who site) :
    let certificate := ((R).bounded recoveryInitial horizon recoveryScheduler).wellFoundedHistories
    let stopped := (N).runBehavioralUntil certificate profile
      (fun history => ¬ recoveryClear history.state ∨ (R).observe who history.state = site.1)
      ((R).protocol recoveryInitial horizon recoveryScheduler).initHistory
    fiberPosterior (stopped.map History.state) ((R).observe who) site.1 =
      ((N).bayesBelief profile who site
        ((R).decisionInformationAntichain recoveryInitial horizon recoveryScheduler who site)
        positive).map (fun history => history.1.state) := by
  classical
  dsimp only
  have observed (history : ((R).protocol recoveryInitial horizon recoveryScheduler).History) :
      (N).infoOf who history.trace = (R).observe who history.state :=
    (R).info recoveryInitial horizon recoveryScheduler who history.trace
  have avoids := recovery_site_avoids_exclusion program runtime leaks inputs horizon scheduler
    who site past view siteInput clear
  have result := (N).bayesBelief_eq_stopped_fiber_map
    ((R).bounded recoveryInitial horizon recoveryScheduler).wellFoundedHistories
    ((R).bounded recoveryInitial horizon recoveryScheduler) profile who site
    ((R).decisionInformationAntichain recoveryInitial horizon recoveryScheduler who site) positive
    (fun history => ¬ recoveryClear history.state) avoids History.state ((R).observe who) site.1
    (fun history _supported => by rw [observed history])
  dsimp only at result
  have stopping : (fun history : ((R).protocol recoveryInitial horizon recoveryScheduler).History =>
      ¬ recoveryClear history.state ∨ (N).infoOf who history.trace = site.1) =
      fun history => ¬ recoveryClear history.state ∨ (R).observe who history.state = site.1 := by
    funext history
    rw [observed history]
  rw [stopping] at result
  exact result

include included in
/-- A positive clear phase site has an actual old raw decision site with the
same information mass and the same Bayes belief on the full physical recovery
state. Old-site positivity is derived from the given phase-site positivity. -/
theorem exists_recovery_site_bayes_state_eq
    (profile : ∀ who, (M).BehavioralPolicy who) (who : Player)
    (site : (M).InformationSite who) (past : List (P).PlayerEntry) (view : (P).PlayerView)
    (siteInput : site.1 = some (past, view)) (clear : view.application.2.excluded = ∅)
    (positive : 0 < (M).informationMass profile who site) :
    let oldProfile := fun player => behavioralPolicy program runtime leaks menu inputs horizon
      scheduler player (profile player)
    ∃ (oldSite : (N).InformationSite who)
      (oldPositive : 0 < (N).informationMass oldProfile who oldSite),
      oldSite.1 = projectInfo site.1 ∧
      (N).informationMass oldProfile who oldSite = (M).informationMass profile who site ∧
      (((M).bayesBelief profile who site
        ((menu).decisionInformationAntichain phaseInitial horizon scheduler who site) positive).map
          (fun history => projection history.1.state)) =
      (((N).bayesBelief oldProfile who oldSite
        ((R).decisionInformationAntichain recoveryInitial horizon recoveryScheduler who oldSite)
        oldPositive).map (fun history => history.1.state)) := by
  classical
  dsimp only
  let oldProfile := fun player => behavioralPolicy program runtime leaks menu inputs horizon
    scheduler player (profile player)
  let oldPast := past.map (PhaseRecoveryProjection.playerEntry runtime leaks recoveryLeaks)
  let oldView := PhaseRecoveryProjection.playerView runtime leaks recoveryLeaks view
  have oldInput : projectInfo site.1 = some (oldPast, oldView) := by
    simp only [siteInput, PhaseRecoveryProjection.information, Option.map_some, oldPast, oldView]
  have oldClear : oldView.application.2 = ∅ := clear
  have oldDecision : (N).IsDecisionInfo who (projectInfo site.1) := by
    obtain ⟨witness, running, _action, _allowed⟩ := site.2
    have witnessInput : (P).observe who witness.1.state = some (past, view) :=
      ((menu).info phaseInitial horizon scheduler who witness.1.trace).symm.trans
        (witness.2.trans siteInput)
    have witnessClear := phase_clear_of_observe_eq program runtime leaks who witness.1.state
      past view witnessInput clear
    obtain ⟨trace, _length⟩ := PhaseRecoveryProjection.trace_projected_clear program runtime leaks
      bounds inputs horizon scheduler
      (included.trace phaseInitial horizon scheduler witness.1.trace) witnessClear
    let history : ((R).protocol recoveryInitial horizon recoveryScheduler).History :=
      ⟨projection witness.1.state, trace⟩
    have projectedObserve : (R).observe who (projection witness.1.state) =
        projectInfo ((P).observe who witness.1.state) :=
      PhaseRecoveryProjection.observe_state runtime leaks recoveryLeaks who witness.1.state
    refine ⟨⟨history, ?_⟩, ?_, ⟨none⟩, ?_⟩
    · exact ((R).info recoveryInitial horizon recoveryScheduler who history.trace).trans
        (projectedObserve.trans (congrArg projectInfo (witnessInput.trans siteInput.symm)))
    · change ¬ (R).terminal (projection witness.1.state)
      have terminal : (R).terminal (projection witness.1.state) ↔
          (P).terminal witness.1.state := by cases witness.1.state <;> rfl
      exact fun ended => running (terminal.mp ended)
    · change (some (⟨none⟩ : (R).Action)).isSome = (projectInfo site.1).isSome
      rw [oldInput]
      rfl
  let oldSite : (N).InformationSite who := ⟨projectInfo site.1, oldDecision⟩
  let phaseCertificate := ((menu).bounded phaseInitial horizon scheduler).wellFoundedHistories
  let oldCertificate := ((R).bounded recoveryInitial horizon recoveryScheduler).wellFoundedHistories
  let phaseStopped := (M).runBehavioralUntil phaseCertificate profile
    (fun history => ¬ phaseClear history.state ∨
      (R).observe who (projection history.state) = projectInfo site.1)
    ((menu).protocol phaseInitial horizon scheduler).initHistory
  let oldStopped := (N).runBehavioralUntil oldCertificate oldProfile
    (fun history => ¬ recoveryClear history.state ∨
      (R).observe who history.state = projectInfo site.1)
    ((R).protocol recoveryInitial horizon recoveryScheduler).initHistory
  have laws : phaseStopped.map (fun history => projection history.state) =
      oldStopped.map History.state :=
    run_until_exclusion_or_guard_initial_map_state program runtime leaks menu bounds included inputs
      horizon scheduler (fun state => (R).observe who state = projectInfo site.1) profile
  have phaseAvoids := phase_site_avoids_exclusion program runtime leaks menu inputs horizon
    scheduler
    who site past view siteInput clear
  have phaseStopping : (fun history : ((menu).protocol phaseInitial horizon scheduler).History =>
      ¬ phaseClear history.state ∨ (M).infoOf who history.trace = site.1) =
      fun history => ¬ phaseClear history.state ∨
        (R).observe who (projection history.state) = projectInfo site.1 := by
    funext history
    exact propext (or_congr Iff.rfl (clear_site_fiber_projected program runtime leaks menu bounds
      included inputs horizon scheduler who site past view siteInput clear history))
  have phaseMass := (M).informationMass_eq_stopped_observation phaseCertificate
    ((menu).bounded phaseInitial horizon scheduler) profile who site
    ((menu).decisionInformationAntichain phaseInitial horizon scheduler who site)
    (fun history => ¬ phaseClear history.state) phaseAvoids
    (fun history => (R).observe who (projection history.state)) (projectInfo site.1)
    (fun history _supported => clear_site_fiber_projected program runtime leaks menu bounds included
      inputs horizon scheduler who site past view siteInput clear history)
  rw [phaseStopping] at phaseMass
  have oldAvoids := recovery_site_avoids_exclusion program runtime leaks inputs horizon scheduler
    who oldSite oldPast oldView oldInput oldClear
  have oldObserved (history : ((R).protocol recoveryInitial horizon recoveryScheduler).History) :
      (N).infoOf who history.trace = (R).observe who history.state :=
    (R).info recoveryInitial horizon recoveryScheduler who history.trace
  have oldStopping : (fun history :
      ((R).protocol recoveryInitial horizon recoveryScheduler).History =>
      ¬ recoveryClear history.state ∨ (N).infoOf who history.trace = oldSite.1) =
      fun history => ¬ recoveryClear history.state ∨
        (R).observe who history.state = projectInfo site.1 := by
    funext history
    rw [oldObserved history]
  have oldMass := (N).informationMass_eq_stopped_observation oldCertificate
    ((R).bounded recoveryInitial horizon recoveryScheduler) oldProfile who oldSite
    ((R).decisionInformationAntichain recoveryInitial horizon recoveryScheduler who oldSite)
    (fun history => ¬ recoveryClear history.state) oldAvoids
    (fun history => (R).observe who history.state) oldSite.1
    (fun history _supported => by rw [oldObserved history])
  rw [oldStopping] at oldMass
  have massEq : (N).informationMass oldProfile who oldSite =
      (M).informationMass profile who site := by
    have observedLaws := congrArg (fun law => (law.map ((R).observe who)) (projectInfo site.1)) laws
    rw [PMF.map_comp, PMF.map_comp] at observedLaws
    exact oldMass.symm.trans (observedLaws.symm.trans phaseMass)
  have oldPositive : 0 < (N).informationMass oldProfile who oldSite := by
    rw [massEq]
    exact positive
  refine ⟨oldSite, oldPositive, rfl, massEq, ?_⟩
  have phasePosterior := phase_bayesBelief_eq_stopped_recovery_state program runtime leaks menu
    bounds
    included inputs horizon scheduler profile who site past view siteInput clear positive
  have oldPosterior := recovery_bayesBelief_eq_stopped_state program runtime leaks inputs horizon
    scheduler oldProfile who oldSite oldPast oldView oldInput oldClear oldPositive
  dsimp only at phasePosterior oldPosterior
  change fiberPosterior (phaseStopped.map (fun history => projection history.state))
    ((R).observe who) (projectInfo site.1) = _ at phasePosterior
  change fiberPosterior (oldStopped.map History.state) ((R).observe who)
    (projectInfo site.1) = _ at oldPosterior
  rw [laws] at phasePosterior
  exact phasePosterior.symm.trans oldPosterior

end Vegas.EventGraphRuntime.SequentialPhaseRecoveryPolicy
