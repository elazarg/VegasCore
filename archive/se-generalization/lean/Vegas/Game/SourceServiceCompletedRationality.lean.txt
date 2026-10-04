/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceCompletedContinuation
import Vegas.Game.SourceServiceImmediatePolicy
import Interaction.ReactiveRecallEntries
import GameTheory.Analysis.Protocol.SequentialOneShot

/-! # Rational completed compatible decisions in an actual native completion

At a completed compatible input the prescribed response is silence. Future
free policies need not be silent: consistency and their genuine single-site
optimality suffice, by backward induction over the owner's decision recall.
The result concerns completed sites only; it makes no posterior-rate estimate
and supplies no rationality at an unfinished source decision.
-/

noncomputable section

namespace Vegas.AsyncServiceSpec

open SourceProgram GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability GameTheory.Enforcement Interaction EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] (service : AsyncServiceSpec Player L)

local notation "app" => application service.setup service.leaks

private def completedInput (info : (app).Info) : Prop :=
  ∃ past view, info = some (past, view) ∧
    ∀ event, event ∈ view.application.publicView.observation.completionOrder

private def inputLength (info : (app).Info) : Nat :=
  match info with
  | none => 0
  | some (past, _) => past.length

private abbrev completedModel
    (responseMenu : (application service.setup service.leaks).ResponseMenu) :=
  responseMenu.information (initialLaw service.setup) service.horizon service.scheduler

omit [Fintype Player] in
private theorem site_some
    (responseMenu : (application service.setup service.leaks).ResponseMenu) (who : Player) (site
      : (completedModel service responseMenu).InformationSite who) :
    ∃ (past : List (app).PlayerEntry) (view : (app).PlayerView),
      site.1 = some (past, view) := by
  cases observed : site.1 with
  | none =>
      obtain ⟨_, _, action, member⟩ := site.2
      rw [observed] at member
      change some action = none at member
      cases member
  | some data => exact ⟨data.1, data.2, rfl⟩

omit [Fintype Player] in
/-- A remembered completed input forces every hidden history of a later own
site to remain complete. Its actual recall is strictly longer. -/
private theorem completed_descendant
    (responseMenu : (application service.setup service.leaks).ResponseMenu)
    (who : Player) (site later : (completedModel service responseMenu).InformationSite who)
    (complete : service.completedInput site.1)
    (remembered : site.1 ∈ ((completedModel service responseMenu).recordAt who later.1).map
        Prod.fst) :
    service.completedInput later.1 ∧
      service.inputLength site.1 < service.inputLength later.1 := by
  obtain ⟨past, view, observed⟩ := service.site_some responseMenu who later
  obtain ⟨history, _running, _action, _member⟩ := later.2
  have recorded := (responseMenu.decisionRecall (initialLaw service.setup) service.horizon
    service.scheduler).recordAt_eq_ownPlay who later history
  rw [recorded, responseMenu.ownPlay_of_info_some (initialLaw service.setup) service.horizon
    service.scheduler who history.1 past view (history.2.trans observed)] at remembered
  obtain ⟨pair, member, named⟩ := List.mem_map.mp remembered
  obtain ⟨index, entry, atIndex, atInput⟩ := (app).ownPlayFrom_recorded_input [] past pair.1
    pair.2 member
  simp only [List.nil_append] at atInput
  have rootInput : site.1 = some (past.take index, entry.beforeView) := named.symm.trans atInput
  obtain ⟨rootPast, rootView, rootSeen, rootComplete⟩ := complete
  have rootEq := Option.some.inj (rootSeen.symm.trans rootInput)
  have entryComplete : ∀ event,
      event ∈ entry.beforeView.application.publicView.observation.completionOrder := by
    have viewEq : rootView = entry.beforeView := congrArg Prod.snd rootEq
    exact viewEq ▸ rootComplete
  have indexBound : index < past.length := by
    exact (List.getElem?_eq_some_iff.mp atIndex).1
  have longer : service.inputLength site.1 < service.inputLength later.1 := by
    rw [rootInput, observed]
    simp only [inputLength]
    exact (List.length_take_le index past).trans_lt indexBound
  have actualObserved := history.2.trans observed
  rcases history with ⟨⟨state, trace⟩, same⟩
  change (responseMenu.signals (initialLaw service.setup) service.horizon
    service.scheduler).infoOf who trace = some (past, view) at actualObserved
  rw [responseMenu.info (initialLaw service.setup) service.horizon service.scheduler who trace]
    at actualObserved
  cases state with
  | none => cases actualObserved
  | some control =>
      by_cases active : control.actor = some who
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at actualObserved
        have inputEq := Option.some.inj actualObserved
        have entryMember : entry ∈ control.execution.recall who := by
          have pastEq : control.execution.recall who = past := congrArg Prod.fst inputEq
          exact pastEq.symm ▸ List.mem_of_getElem? atIndex
        have monotone := (runtime service.setup).submissionView_completed_subset service.leaks
          (initialLaw service.setup) service.horizon service.scheduler control
          (responseMenu.toRawTrace (initialLaw service.setup) service.horizon
            service.scheduler trace) who entry entryMember
        refine ⟨⟨past, view, observed, ?_⟩, longer⟩
        intro event
        have actualComplete : event ∈ control.execution.application.config.cut.completed :=
          monotone (List.mem_toFinset.mpr (entryComplete event))
        have inOrder := (control.execution.application.config.history_exact event).mpr
          actualComplete
        have orderEq := congrArg
          (fun pair => pair.2.application.publicView.observation.completionOrder) inputEq
        change control.execution.application.config.history.map EventGraph.Completion.event =
          view.application.publicView.observation.completionOrder at orderEq
        exact orderEq ▸ inOrder
      · simp only [ReactiveApplication.observe, active, ↓reduceIte] at actualObserved
        cases actualObserved

open Classical in
/-- Single-site optimality at free sites and the actual silent pins suffice
for whole-policy rationality at completed compatible sites. No global silent
continuation is required of the assessment. -/
theorem sourceCompatibleInfo_completed_optimal
    (responseMenu : (application service.setup service.leaks).ResponseMenu)
    (silence : ∀ (player : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView),
      (⟨none⟩ : (app).Action) ∈ responseMenu.actions player past view)
    (assessment : (completedModel service responseMenu).BehavioralAssessment)
    (consistent : assessment.IsSequentiallyConsistent
      (responseMenu.decisionInformationAntichain (initialLaw service.setup) service.horizon
        service.scheduler))
    (utility : State L service.setup.program.terminalCtx → Player → ℝ)
    (sample : List (SettledEvidence service.setup) → PMF (List (SettledEvidence service.setup)))
    (authentic : ∀ actual observed, observed ∈ (sample actual).support → observed ⊆ actual)
    (deposit : Player → ℝ)
    (silentPins : ∀ who (site : (completedModel service responseMenu).InformationSite who),
      service.sourceCompatibleInfo who site.1 →
      ∀ (past : List (app).PlayerEntry) (view : (app).PlayerView), site.1 = some (past, view) →
        (∀ event, event ∈ view.application.publicView.observation.completionOrder) →
        assessment.strategy who site.1 =
          (responseMenu.restrictPolicy (initialLaw service.setup) service.horizon
            service.scheduler who (app).silentPolicy) site.1)
    (freeOptimal : ∀ who (site : (completedModel service responseMenu).InformationSite who),
      ¬ service.sourceCompatibleInfo who site.1 → ∀ law : PMF ((completedModel service
        responseMenu).Choice who site.1),
        (assessment.continuationContext
          (responseMenu.bounded (initialLaw service.setup) service.horizon
            service.scheduler).wellFoundedHistories site
          (fun final : (responseMenu.protocol (initialLaw service.setup) service.horizon
            service.scheduler).History => TerminalAudit.utility (baseUtility service.setup
              service.leaks utility)
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample) deposit final.state who)).value
          ((assessment.strategy who).withLaw site.1 law) ≤
        (assessment.continuationContext
          (responseMenu.bounded (initialLaw service.setup) service.horizon
            service.scheduler).wellFoundedHistories site
          (fun final : (responseMenu.protocol (initialLaw service.setup) service.horizon
            service.scheduler).History => TerminalAudit.utility (baseUtility service.setup
              service.leaks utility)
            ((runtime service.setup).serviceAuditObservation service.leaks)
            (sourceServiceAudit service.setup service.leaks sample) deposit final.state who)).value
          (assessment.strategy who))
    (who : Player) (site : (completedModel service responseMenu).InformationSite who)
    (nonnegative : 0 ≤ deposit who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (completed : ∀ event, event ∈ view.application.publicView.observation.completionOrder) :
    (assessment.continuationContext
      (responseMenu.bounded (initialLaw service.setup) service.horizon
        service.scheduler).wellFoundedHistories site
      (fun final : (responseMenu.protocol (initialLaw service.setup) service.horizon
            service.scheduler).History => TerminalAudit.utility (baseUtility service.setup
              service.leaks utility)
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) deposit final.state
          who)).IsLocallyOptimal
      Set.univ (assessment.strategy who) := by
  classical
  let certificate := (responseMenu.bounded (initialLaw service.setup) service.horizon
    service.scheduler).wellFoundedHistories
  let payoff := fun player (final : (responseMenu.protocol (initialLaw service.setup)
    service.horizon service.scheduler).History) =>
      TerminalAudit.utility (baseUtility service.setup service.leaks utility)
        ((runtime service.setup).serviceAuditObservation service.leaks)
        (sourceServiceAudit service.setup service.leaks sample) deposit final.state player
  let _ := Fintype.ofFinite ((completedModel service responseMenu).InformationSite who)
  let bound := Finset.univ.sup fun later : (completedModel service responseMenu).InformationSite
    who =>
    service.inputLength later.1
  have bounded (later : (completedModel service responseMenu).InformationSite who) :
        service.inputLength later.1 ≤ bound :=
    Finset.le_sup (f := fun later : (completedModel service responseMenu).InformationSite who =>
      service.inputLength later.1) (Finset.mem_univ later)
  have optimal : ∀ n (current : (completedModel service responseMenu).InformationSite who),
      bound - service.inputLength current.1 = n →
        service.sourceCompatibleInfo who current.1 → service.completedInput current.1 →
          (assessment.continuationContext certificate current (payoff who)).IsLocallyOptimal
            Set.univ (assessment.strategy who) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro current ranked currentCompatible currentComplete
        let silent := responseMenu.restrictPolicy (initialLaw service.setup) service.horizon
          service.scheduler who (app).silentPolicy
        let replacement := (assessment.strategy who).spliceAfter (completedModel service
          responseMenu) silent current.1
        have each (player : Player) (later : (completedModel service
          responseMenu).InformationSite player)
            (law : PMF ((completedModel service responseMenu).Choice player later.1))
            (allowed : law =
              (Profile.update (sig := (completedModel service responseMenu).behavioralSignature)
        assessment.strategy who
                replacement) player later.1) :
            (assessment.continuationContext certificate later (payoff player)).value
                ((assessment.strategy player).withLaw later.1 law) ≤
              (assessment.continuationContext certificate later (payoff player)).value
                (assessment.strategy player) := by
          by_cases same : player = who
          · subst player
            simp only [Profile.update_same] at allowed
            subst law
            by_cases atCurrent : later.1 = current.1
            · obtain ⟨currentPast, currentView, currentSeen, currentDone⟩ := currentComplete
              have equal := silentPins who current currentCompatible currentPast currentView
                currentSeen currentDone
              have atReplacement : replacement later.1 = assessment.strategy who later.1 := by
                rw [atCurrent]
                unfold replacement InformationModel.BehavioralPolicy.spliceAfter
                simp only [true_or, ↓reduceIte]
                exact equal.symm
              rw [atReplacement, InformationModel.BehavioralPolicy.withLaw_eq_self]
            · by_cases follows : current.1 ∈
                  ((completedModel service responseMenu).recordAt who later.1).map Prod.fst
              · obtain ⟨laterComplete, longer⟩ := service.completed_descendant responseMenu who
                  current later currentComplete follows
                by_cases laterCompatible : service.sourceCompatibleInfo who later.1
                · have smaller : bound - service.inputLength later.1 < n := by
                    have laterBound := bounded later
                    rw [← ranked]
                    omega
                  have laterOptimal := ih _ smaller later rfl laterCompatible laterComplete
                  have integrable (alternative : (completedModel service
                    responseMenu).BehavioralPolicy who) :
                      (assessment.continuationContext certificate later (payoff who)).IntegrableAt
                        alternative := payoffIntegrable_of_finite _ _
                  have comparison :=
                    (Context.isLocallyOptimal_iff_of_integrable
                      (integrable (assessment.strategy who))
                      (fun alternative _ => integrable alternative)).mp laterOptimal
                  exact comparison _ (Set.mem_univ _)
                · exact freeOptimal who later laterCompatible _
              · have unchanged : replacement later.1 = assessment.strategy who later.1 := by
                  simp only [replacement, InformationModel.BehavioralPolicy.spliceAfter,
                    atCurrent, follows,
                    false_or, ↓reduceIte]
                rw [unchanged, InformationModel.BehavioralPolicy.withLaw_eq_self]
          · rw [Profile.update_of_ne _ _ same] at allowed
            rw [allowed, InformationModel.BehavioralPolicy.withLaw_eq_self]
        have silentLower := consistent.continuation_value_le_of_locallyOptimal
          (completedModel service responseMenu)
          (responseMenu.decisionRecall (initialLaw service.setup) service.horizon
            service.scheduler)
          (fun player info law => law =
            (Profile.update (sig := (completedModel service responseMenu).behavioralSignature)
        assessment.strategy who
              replacement) player info)
          payoff certificate each who current replacement (by
            intro later
            simp only [Profile.update_same])
        have splicedValue :
            (assessment.continuationContext certificate current (payoff who)).value replacement =
              (assessment.continuationContext certificate current (payoff who)).value silent := by
          have contexts := assessment.continuationContext_eq_truncated_of_bounded certificate
            (responseMenu.bounded (initialLaw service.setup) service.horizon service.scheduler)
            current (payoff who)
          rw [contexts]
          have integrable (alternative : (completedModel service responseMenu).BehavioralPolicy
            who) :
              (assessment.truncatedContinuationContext current (payoff who)
                (2 * service.horizon + 1)).IntegrableAt alternative :=
            payoffIntegrable_of_finite _ _
          have firstTower := assessment.continuationContextWith_value_tower
            ((completedModel service responseMenu).truncatedRunner (2 * service.horizon + 1))
              current
              (payoff who) replacement (integrable replacement)
          have secondTower := assessment.continuationContextWith_value_tower
            ((completedModel service responseMenu).truncatedRunner (2 * service.horizon + 1))
              current
              (payoff who) silent (integrable silent)
          refine firstTower.trans ((congrArg (expect (assessment.belief who current)) ?_).trans
            secondTower.symm)
          funext history
          exact congrArg (fun law => expect law (payoff who))
            ((completedModel service responseMenu).runBehavioralFrom_spliceAfter_eq
              (responseMenu.decisionRecall (initialLaw service.setup) service.horizon
                service.scheduler) assessment.strategy who current silent history
                (2 * service.horizon + 1))
        rw [splicedValue] at silentLower
        obtain ⟨past, view, observed, allComplete⟩ := currentComplete
        have silentBest := service.sourceCompatibleInfo_completed_silent_optimal responseMenu
          silence who current currentCompatible past view observed allComplete assessment utility
          sample authentic deposit nonnegative
        have contexts := assessment.continuationContext_eq_truncated_of_bounded certificate
          (responseMenu.bounded (initialLaw service.setup) service.horizon service.scheduler)
          current (payoff who)
        rw [← contexts] at silentBest
        have integrable (alternative : (completedModel service responseMenu).BehavioralPolicy who) :
            (assessment.continuationContext certificate current (payoff who)).IntegrableAt
              alternative := payoffIntegrable_of_finite _ _
        apply Context.isLocallyOptimal_iff_of_integrable (integrable (assessment.strategy who))
          (fun alternative _ => integrable alternative) |>.mpr
        intro alternative _
        exact ((Context.isLocallyOptimal_iff_of_integrable (integrable silent)
          (fun other _ => integrable other)).mp silentBest alternative (Set.mem_univ _)).trans
            silentLower
  exact optimal _ site rfl compatible ⟨past, view, observed, completed⟩

omit [Fintype Player] in
/-- Fully completed public information makes the actual immediate policy
silent, independently of the source kernel and private candidate material. -/
theorem sourceServiceImmediatePolicy_completed_profile
    (responseMenu : (application service.setup service.leaks).ResponseMenu)
    (silence : ∀ (player : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView),
      (⟨none⟩ : (app).Action) ∈ responseMenu.actions player past view)
    (profile : BehavioralProfile service.setup.program) (who : Player)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (completed : ∀ event, event ∈ view.application.publicView.observation.completionOrder) :
    (responseMenu.restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
      (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who))
        (some (past, view)) =
      (responseMenu.restrictPolicy (initialLaw service.setup) service.horizon service.scheduler who
        (app).silentPolicy) (some (past, view)) := by
  classical
  have idle : view.application.publicView.ownTurn? who = none := by
    cases selected : view.application.publicView.ownTurn? who with
    | none => rfl
    | some event =>
        have ready := (view.application.publicView.ownTurn?_spec who event selected).1
        exact (ready.1 (completed event)).elim
  have physical : sourceServiceImmediatePolicy service.setup service.leaks service.bound
      profile who past view = (app).silentPolicy past view := by
    unfold sourceServiceImmediatePolicy
    split
    · rw [idle]
    · rfl
  have silentCovered response (chosen : response ∈ ((app).silentPolicy past view).support) :
      response ∈ responseMenu.actions who past view := by
    obtain rfl := (app).silentPolicy_cases past view response chosen
    exact silence who past view
  have immediateCovered response (chosen : response ∈
      (sourceServiceImmediatePolicy service.setup service.leaks service.bound profile who
        past view).support) : response ∈ responseMenu.actions who past view := by
    exact silentCovered response (physical ▸ chosen)
  apply pmf_map_injective (f := Subtype.val) Subtype.val_injective
  exact (responseMenu.restrictPolicy_map_val (initialLaw service.setup) service.horizon
    service.scheduler who _ past view immediateCovered).trans
      ((congrArg (fun law => law.map some) physical).trans
        (responseMenu.restrictPolicy_map_val (initialLaw service.setup) service.horizon
          service.scheduler who (app).silentPolicy past view silentCovered).symm)

open Classical in
/-- At completed compatible sites, the actual uniform/WAIT/immediate pins
converge to silence even when normalized source policies have arbitrary
zero-probability transcript limits. No waiting-rate comparison is used. -/
theorem sourceCompatibleInfo_completed_pin_limit
    (responseMenu : (application service.setup service.leaks).ResponseMenu)
    (silence : ∀ (player : Player) (past : List (app).PlayerEntry) (view : (app).PlayerView),
      (⟨none⟩ : (app).Action) ∈ responseMenu.actions player past view)
    (profile : Nat → BehavioralProfile service.setup.program)
    (weight : Nat → Player → (app).Info → ℝ)
    (weightNonnegative : ∀ n who info, 0 ≤ weight n who info)
    (weightSmall : ∀ n who info, weight n who info ≤ 1)
    (delta : Nat → ℝ) (deltaNonnegative : ∀ n, 0 ≤ delta n)
    (deltaSmall : ∀ n, delta n ≤ 1) (deltaVanishes : Tendsto delta atTop (nhds 0))
    (sequence : Nat → (completedModel service responseMenu).BehavioralAssessment)
    (assessment : (completedModel service responseMenu).BehavioralAssessment)
    (index : Nat → Nat) (increasing : StrictMono index)
    (converges : InformationModel.BehavioralAssessmentConvergesPointwise
      (fun n => sequence (index n)) assessment)
    (pinned : ∀ n who (site : (responseMenu.information (initialLaw service.setup)
      service.horizon service.scheduler).InformationSite who),
      service.sourceCompatibleInfo who site.1 →
        (sequence n).strategy who site.1 =
          mix (delta n) (deltaNonnegative n) (deltaSmall n)
            (responseMenu.uniformPolicy (initialLaw service.setup) service.horizon
              service.scheduler who site.1)
            (mix (weight n who site.1) (weightNonnegative n who site.1) (weightSmall n who site.1)
              ((responseMenu.restrictPolicy (initialLaw service.setup) service.horizon
                service.scheduler who (app).silentPolicy) site.1)
              ((responseMenu.restrictPolicy (initialLaw service.setup) service.horizon
                service.scheduler who (sourceServiceImmediatePolicy service.setup service.leaks
                  service.bound (profile n) who)) site.1)))
    (who : Player)
    (site : (completedModel service responseMenu).InformationSite who)
    (compatible : service.sourceCompatibleInfo who site.1)
    (past : List (app).PlayerEntry) (view : (app).PlayerView)
    (observed : site.1 = some (past, view))
    (completed : ∀ event, event ∈ view.application.publicView.observation.completionOrder) :
    assessment.strategy who site.1 =
      (responseMenu.restrictPolicy (initialLaw service.setup) service.horizon
        service.scheduler who (app).silentPolicy) site.1 := by
  let silent := responseMenu.restrictPolicy (initialLaw service.setup) service.horizon
    service.scheduler who (app).silentPolicy
  have laws (n : Nat) : (sequence n).strategy who site.1 =
      mix (delta n) (deltaNonnegative n) (deltaSmall n)
        (responseMenu.uniformPolicy (initialLaw service.setup) service.horizon
          service.scheduler who site.1) (silent site.1) := by
    have immediate :
        (responseMenu.restrictPolicy (initialLaw service.setup) service.horizon service.scheduler
          who (sourceServiceImmediatePolicy service.setup service.leaks service.bound
            (profile n) who)) site.1 = silent site.1 := by
      rw [observed]
      exact service.sourceServiceImmediatePolicy_completed_profile responseMenu silence
        (profile n) who past view completed
    rw [pinned n who site compatible, immediate, mix_self]
  have actual : PMFConvergesPointwise
      (fun n => mix (delta (index n)) (deltaNonnegative (index n)) (deltaSmall (index n))
        (responseMenu.uniformPolicy (initialLaw service.setup) service.horizon
          service.scheduler who site.1) (silent site.1)) (assessment.strategy who site.1) := by
    simpa only [laws] using converges.strategy who site
  exact actual.unique (pmfConvergesPointwise_mix_zero (fun n => delta (index n))
    (fun n => deltaNonnegative (index n)) (fun n => deltaSmall (index n))
    (deltaVanishes.comp increasing.tendsto_atTop) _ _)

end Vegas.AsyncServiceSpec
