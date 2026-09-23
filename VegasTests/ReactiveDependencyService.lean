/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.ReactiveDependencyService
import VegasTests.ReactiveAuthorization
import VegasTests.ReactiveEarlyOpeningIncentives

/-! # The early-opening race under submission-authorized inclusion

The same raw histories and compiler responses are evaluated with a fixed
calendar whose inclusion steps use the dependency-authorized selector. Premature
envelopes stay pending but cannot compete for later disclosure. The checked
comparison concerns the exhibited deviation, not all deviations or all subgames.
-/

noncomputable section

namespace VegasTests.ReactiveEarlyOpening

open GameTheory.Math.Probability Interaction Vegas Vegas.EventGraphRuntime

theorem dependencyCondition_iff (view : PublicView graph) (message : Message Unit (Payload graph)) :
    dependencyCondition view message ↔
      (message.payload.event? graph = some 1 → 0 ∈ view.observation.completionOrder) := by
  constructor
  · intro allowed address
    exact allowed 1 address 0 (by decide)
  · intro allowed event address predecessor member
    fin_cases event
    · exact False.elim (Finset.notMem_empty _ member)
    · have same : predecessor = 0 := Finset.mem_singleton.mp member
      subst predecessor
      exact allowed address

def authorizedSelect (event : graph.EventId) (execution : app.Execution) : FinDist app.Command :=
  app.uniformInstruction dependencyCondition execution.environmentRecall
    (execution.observeEnvironment app) (.select (eventProposal event ()))

def authorizedCalendar : Nat → app.UniformInstruction
  | 0 | 1 | 2 => .activate ()
  | 3 => .select (eventProposal 0 ())
  | 4 => .application (.grant 1)
  | 5 => .activate ()
  | 6 => .select (eventProposal 1 ())
  | _ => .wait

def authorizedScheduler : app.Scheduler :=
  runtime.dependencyUniformScheduler leaks authorizedCalendar

theorem authorized_service :
    runtime.DependencyAuthorized leaks (FinDist.pure initialState) 7 authorizedScheduler :=
  runtime.dependencyUniformScheduler_authorized leaks _ _ authorizedCalendar

theorem authorized_service_once : app.AtMostOnce authorizedScheduler :=
  runtime.dependencyUniformScheduler_atMostOnce leaks authorizedCalendar

def authorizedResponsePrefix : app.TwoResponsePrefix where
  initialState := initialState
  remaining := 5
  scheduler := authorizedScheduler
  schedules history view early := by
    have casesLength : history.length = 0 ∨ history.length = 1 := by omega
    change app.uniformInstruction dependencyCondition history view
      (authorizedCalendar history.length) = _
    rcases casesLength with zero | one
    · rw [zero]; rfl
    · rw [one]; rfl
  activation := activation

theorem authorized_contested_isSubgameRoot :
    (app.information (FinDist.pure initialState) 7 authorizedScheduler).IsSubgameRoot
      (authorizedResponsePrefix.secondHistory first second) :=
  authorizedResponsePrefix.secondHistory_isSubgameRoot first second

theorem authorized_contested_state :
    (authorizedResponsePrefix.secondHistory first second).state =
      some ⟨5, none, contested⟩ := rfl

theorem withheld_submission_observation (repair fresh : Bool) :
    app.submissionObservation? (disclosed repair fresh).environmentRecall withholdingEnvelope.id =
      some initialState.publicView := by
  cases repair <;> cases fresh <;> rfl

theorem early_submission_observation :
    app.submissionObservation? (disclosed false false).environmentRecall
      prematureOpeningEnvelope.id = some initialState.publicView := rfl

theorem later_submission_observation (repair fresh : Bool) :
    app.submissionObservation? (disclosed repair fresh).environmentRecall ((), 3) =
      some (granted repair fresh).application.publicView := by
  cases repair <;> cases fresh <;> rfl

theorem withheld_permission_denied (repair fresh : Bool) :
    ¬ app.SubmissionPermitted dependencyCondition (disclosed repair fresh).environmentRecall
      withholdingEnvelope := by
  simp only [ReactiveApplication.SubmissionPermitted, withheld_submission_observation,
    Option.some.injEq, dependencyCondition_iff]
  rintro ⟨view, rfl, permitted⟩
  exact List.not_mem_nil (permitted rfl)

theorem early_permission_denied :
    ¬ app.SubmissionPermitted dependencyCondition (disclosed false false).environmentRecall
      prematureOpeningEnvelope := by
  simp only [ReactiveApplication.SubmissionPermitted, early_submission_observation,
    Option.some.injEq, dependencyCondition_iff]
  rintro ⟨view, rfl, permitted⟩
  exact List.not_mem_nil (permitted rfl)

theorem later_permission_granted (repair fresh : Bool) (possible : fresh = true → repair = true) :
    app.SubmissionPermitted dependencyCondition (disclosed repair fresh).environmentRecall
      ⟨((), 3), .opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩⟩ := by
  refine ⟨(granted repair fresh).application.publicView,
    later_submission_observation repair fresh, ?_⟩
  rw [dependencyCondition_iff]
  intro _
  change 0 ∈ (disclosed repair fresh).application.publicView.observation.completionOrder
  rw [disclosed_state repair fresh possible]
  cases repair <;> cases fresh <;> decide

theorem authorized_disclosure_selection (repair fresh : Bool)
    (possible : fresh = true → repair = true) :
    authorizedSelect 1 (disclosed repair fresh) = FinDist.pure (.include ((), 3)) := by
  have denied := withheld_permission_denied repair fresh
  have allowed := later_permission_granted repair fresh possible
  let keep := fun message => app.authorizedEligibility dependencyCondition
        (disclosed repair fresh).environmentRecall (eventProposal 1 ()) message &&
        !((disclosed repair fresh).observeEnvironment app).network.ledger.any
          (fun prior => prior.id = message.id)
  have noWithhold : keep withholdingEnvelope = false := by
    simp [keep, ReactiveApplication.authorizedEligibility, denied]
  have noCommit (id : MessageId Unit) (handle : Handle graph) :
      keep ⟨id, .commitment 0 handle⟩ = false := rfl
  have accepted :
      keep ⟨((), 3), .opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩⟩ = true := by
    have address : eventProposal 1 ()
        ⟨((), 3), .opening 1 (candidate fresh) ⟨.int, selectedValue fresh⟩⟩ = true := rfl
    simp only [keep, ReactiveApplication.authorizedEligibility, allowed, decide_true, address,
      Bool.and_self, Bool.true_and]
    cases repair <;> cases fresh <;> rfl
  have candidates : MessageNetwork.eligibleIds keep (disclosed repair fresh).network.pending =
        {((), 3)} := by
    cases repair <;> cases fresh
    · change MessageNetwork.eligibleIds _ [withholdingEnvelope, prematureOpeningEnvelope,
        ⟨((), 3), .opening 1 (candidate false) ⟨.int, selectedValue false⟩⟩] = _
      have noEarly : keep prematureOpeningEnvelope = false := by
        simp [keep, ReactiveApplication.authorizedEligibility, early_permission_denied]
      simp only [MessageNetwork.eligibleIds, List.filter_cons, noWithhold, noEarly, accepted,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    · simp at possible
    · change MessageNetwork.eligibleIds _ [withholdingEnvelope,
        ⟨((), 2), .commitment 0 ((), .prepared 1)⟩,
        ⟨((), 3), .opening 1 (candidate false) ⟨.int, selectedValue false⟩⟩] = _
      simp only [MessageNetwork.eligibleIds, List.filter_cons, noWithhold, noCommit, accepted,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    · change MessageNetwork.eligibleIds _ [⟨((), 0), .commitment 0 ((), .prepared 0)⟩,
        withholdingEnvelope, ⟨((), 3), .opening 1 (candidate true) ⟨.int, selectedValue true⟩⟩] = _
      simp only [MessageNetwork.eligibleIds, List.filter_cons, noCommit, noWithhold, accepted,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  change (MessageNetwork.chooseUniform
    (MessageNetwork.eligibleIds keep (disclosed repair fresh).network.pending)).map _ = _
  rw [candidates, MessageNetwork.chooseUniform_singleton, FinDist.map_pure]
  rfl

theorem authorized_binding_selection (repair : Bool) :
    authorizedSelect 0 (afterResponse repair) =
      if repair then half (FinDist.pure (.include ((), 0)))
        (FinDist.pure (.include ((), 2))) else FinDist.pure (.include ((), 0)) := by
  have oldAllowed : app.SubmissionPermitted dependencyCondition
      (afterResponse repair).environmentRecall ⟨((), 0), .commitment 0 ((), .prepared 0)⟩ := by
    refine ⟨initialState.publicView, ?_, ?_⟩
    · cases repair <;> rfl
    · rw [dependencyCondition_iff]
      intro impossible
      cases impossible
  have newAllowed : app.SubmissionPermitted dependencyCondition
      (afterResponse true).environmentRecall ⟨((), 2), .commitment 0 ((), .prepared 1)⟩ := by
    refine ⟨initialState.publicView, rfl, ?_⟩
    rw [dependencyCondition_iff]
    intro impossible
    cases impossible
  let keep := fun message => app.authorizedEligibility dependencyCondition
    (afterResponse repair).environmentRecall (eventProposal 0 ()) message
  have keepOld : keep ⟨((), 0), .commitment 0 ((), .prepared 0)⟩ = true := by
    simpa only [keep, ReactiveApplication.authorizedEligibility, oldAllowed,
      decide_true, Bool.and_true] using (rfl : eventProposal 0 ()
        ⟨((), 0), .commitment 0 ((), .prepared 0)⟩ = true)
  have noWithhold : keep withholdingEnvelope = false := rfl
  have noOpening : keep prematureOpeningEnvelope = false := rfl
  have menu : MessageNetwork.eligibleIds keep (afterResponse repair).network.pending =
      if repair then {((), 0), ((), 2)} else {((), 0)} := by
    cases repair
    · change MessageNetwork.eligibleIds keep [⟨((), 0), .commitment 0 ((), .prepared 0)⟩,
        withholdingEnvelope, prematureOpeningEnvelope] = _
      simp only [MessageNetwork.eligibleIds, List.filter_cons, keepOld, noWithhold, noOpening,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
    · have keepNew : keep ⟨((), 2), .commitment 0 ((), .prepared 1)⟩ = true := by
        simpa only [keep, ReactiveApplication.authorizedEligibility, newAllowed,
          decide_true, Bool.and_true] using (rfl : eventProposal 0 ()
            ⟨((), 2), .commitment 0 ((), .prepared 1)⟩ = true)
      change MessageNetwork.eligibleIds keep [⟨((), 0), .commitment 0 ((), .prepared 0)⟩,
        withholdingEnvelope, ⟨((), 2), .commitment 0 ((), .prepared 1)⟩] = _
      simp only [MessageNetwork.eligibleIds, List.filter_cons, keepOld, noWithhold, keepNew,
        Bool.false_eq_true, ↓reduceIte, List.filter_nil, List.map_cons, List.map_nil,
        List.toFinset_cons, List.toFinset_nil, Finset.insert_empty]
  have selection : authorizedSelect 0 (afterResponse repair) =
      (MessageNetwork.chooseUniform (MessageNetwork.eligibleIds keep
        (afterResponse repair).network.pending)).map
          (fun selected => selected.elim .wait .include) := by
    change (MessageNetwork.uniformPending _ _).map _ = _
    congr 2
    funext message
    cases repair <;> exact Bool.and_true _
  rw [selection, menu]
  cases repair <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · rw [MessageNetwork.chooseUniform_singleton, FinDist.map_pure]
    rfl
  · rw [selection_pair _ _ (by decide)]
    simp only [half, FinDist.map_mix, FinDist.map_pure]
    rfl

theorem authorized_binding_round (policy : app.Policy) (repair : Bool) :
    app.round authorizedScheduler (fun _ => policy) (afterResponse repair) =
      if repair then half (FinDist.pure (included true false))
        (FinDist.pure (included true true)) else FinDist.pure (included false false) := by
  have choice : authorizedScheduler (afterResponse repair).environmentRecall
      ((afterResponse repair).observeEnvironment app) =
        authorizedSelect 0 (afterResponse repair) := by cases repair <;> rfl
  rw [ReactiveApplication.round, choice, authorized_binding_selection]
  cases repair <;> simp only [Bool.false_eq_true, ↓reduceIte, half, FinDist.mix_bind,
    FinDist.pure_bind, ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    FinDist.map_pure, ReactiveApplication.Command.actor?, ReactiveApplication.resume]
  all_goals rfl

theorem authorized_grant_round (policy : app.Policy) (repair fresh : Bool) :
    app.round authorizedScheduler (fun _ => policy) (included repair fresh) =
      FinDist.pure (granted repair fresh) := by
  have same : app.round authorizedScheduler (fun _ => policy) (included repair fresh) =
      app.round scheduler (fun _ => policy) (included repair fresh) := by
    cases repair <;> cases fresh <;> rfl
  rw [same, grant_round]

theorem authorized_disclosure_round (policy : app.Policy) (repair fresh : Bool)
    (responds : policy ((activated (granted repair fresh)).recall ())
      ((activated (granted repair fresh)).observe app ()) = FinDist.pure (finalOpening fresh)) :
    app.round authorizedScheduler (fun _ => policy) (granted repair fresh) =
      FinDist.pure (disclosed repair fresh) := by
  have same : app.round authorizedScheduler (fun _ => policy) (granted repair fresh) =
      app.round scheduler (fun _ => policy) (granted repair fresh) := by
    cases repair <;> cases fresh <;> rfl
  rw [same, disclosure_round policy repair fresh responds]

theorem authorized_publication_round (policy : app.Policy) (repair fresh : Bool)
    (possible : fresh = true → repair = true) :
    app.round authorizedScheduler (fun _ => policy) (disclosed repair fresh) =
      FinDist.pure (finished repair fresh 3) := by
  have choice : authorizedScheduler (disclosed repair fresh).environmentRecall
      ((disclosed repair fresh).observeEnvironment app) =
        authorizedSelect 1 (disclosed repair fresh) := by cases repair <;> cases fresh <;> rfl
  rw [ReactiveApplication.round, choice, authorized_disclosure_selection repair fresh possible,
    FinDist.pure_bind]
  simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
    FinDist.map_pure, ReactiveApplication.Command.actor?, FinDist.pure_bind,
    ReactiveApplication.resume]
  rfl

theorem authorized_compiled_rounds :
    app.runRounds authorizedScheduler (fun _ => compiled) 5 contested =
      half (FinDist.pure (finished true false 3)) (FinDist.pure (finished true true 3)) := by
  have firstRound : app.round authorizedScheduler (fun _ => compiled) contested =
      FinDist.pure (afterResponse true) := compiled_first_round
  simp only [ReactiveApplication.runRounds, firstRound, FinDist.pure_bind,
    authorized_binding_round, ↓reduceIte, half, FinDist.mix_bind, authorized_grant_round,
    authorized_disclosure_round compiled true false (compiled_later true false (by simp)),
    authorized_disclosure_round compiled true true (compiled_later true true (by simp)),
    authorized_publication_round compiled true false (by simp),
    authorized_publication_round compiled true true (by simp), FinDist.bind_pure]

theorem authorized_early_rounds :
    app.runRounds authorizedScheduler (fun _ => earlyPolicy) 5 contested =
      FinDist.pure (finished false false 3) := by
  have firstRound : app.round authorizedScheduler (fun _ => earlyPolicy) contested =
      FinDist.pure (afterResponse false) := early_first_round
  simp only [ReactiveApplication.runRounds, firstRound, FinDist.pure_bind,
    authorized_binding_round, Bool.false_eq_true, ↓reduceIte, authorized_grant_round,
    authorized_disclosure_round earlyPolicy false false earlyPolicy_later,
    authorized_publication_round earlyPolicy false false (by simp), FinDist.bind_pure]

theorem authorized_compiled_value :
    (app.runRounds authorizedScheduler (fun _ => compiled) 5 contested).expect
      (fun final => PendingMenus.publicUtility true (final.application.config.outputs 1)) =
        5 / 2 := by
  rw [authorized_compiled_rounds]
  simp only [half, FinDist.expect_mix, FinDist.expect_pure, repaired_opening]
  norm_num [PendingMenus.publicUtility]

theorem authorized_early_value :
    (app.runRounds authorizedScheduler (fun _ => earlyPolicy) 5 contested).expect
      (fun final => PendingMenus.publicUtility true (final.application.config.outputs 1)) = 2 := by
  rw [authorized_early_rounds, FinDist.expect_pure, later_opening]
  norm_num [PendingMenus.publicUtility]

theorem authorized_compiled_publication :
    (app.runRounds authorizedScheduler (fun _ => compiled) 5 contested).map
        (fun final => final.application.config.outputs 1) =
      half (FinDist.pure (some (.success 1))) (FinDist.pure (some (.success 0))) := by
  rw [authorized_compiled_rounds]
  simp only [half, FinDist.map_mix, FinDist.map_pure, repaired_opening,
    Bool.false_eq_true, ↓reduceIte]

theorem authorized_early_publication :
    (app.runRounds authorizedScheduler (fun _ => earlyPolicy) 5 contested).map
        (fun final => final.application.config.outputs 1) =
      FinDist.pure (some (.success 1)) := by
  rw [authorized_early_rounds, FinDist.map_pure, later_opening]

end VegasTests.ReactiveEarlyOpening
