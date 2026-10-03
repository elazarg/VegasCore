/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceServiceFirstActivationFactorization
import Vegas.Game.SourceServiceFirstActivationResources
import Vegas.Game.SourceServiceFirstTurnCompletes
import Vegas.Game.SourceServiceFirstTurnPrefix
import Vegas.Game.SourceServiceResidualSites
import Vegas.Game.SourceServiceRecordedBindingCompletion
import Vegas.Pending.ReactiveBindingSchedule

/-! # A latent binding draw through its actual asynchronous phase

The current typed draw is carried unchanged through the first protected owner
response and its completion. Before that response, foreign clients are silent
and the configuration is unchanged. The traffic law retains the same passive
samples, public scheduler recall, pending messages and receipts throughout.
-/

noncomputable section

namespace Vegas

open SourceProgram Interaction EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))
  (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))

private theorem decided_recorded_silent
    (bound : (graph setup).EventId → Nat) (owner : Player) (event : (graph setup).EventId)
    (action : (graph setup).Action event) (execution : (application setup leaks).Execution)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (who : Player) :
    decidedProfile (leaks := leaks) bound owner event action who (execution.recall who)
        (execution.observe (application setup leaks) who) =
      (application setup leaks).silentPolicy (execution.recall who)
        (execution.observe (application setup leaks) who) := by
  by_cases own : who = owner
  · subst who
    simp only [decidedProfile, Function.update_self, decidedTurnPolicy,
      ReactiveApplication.turnScheduledPolicy]
    split
    · simp only [decidedOpportunity, recorded, ↓reduceIte]
    · rfl
  · simp only [decidedProfile, Function.update_of_ne own]

private theorem decided_recorded_runUntil
    (scheduler : (application setup leaks).Scheduler)
    (bound : (graph setup).EventId → Nat) (owner : Player) (event : (graph setup).EventId)
    (action : (graph setup).Action event) (execution : (application setup leaks).Execution)
    (ready : execution.application.config.cut.Ready event)
    (recorded : (runtime setup).eventRecorded leaks (execution.recall owner) event = true)
    (count : Nat) :
    (application setup leaks).runUntil scheduler
        (decidedProfile (leaks := leaks) bound owner event action)
        (fun final => event ∈ final.application.config.cut.completed) count execution =
      (application setup leaks).runUntil scheduler
        (fun _ => (application setup leaks).silentPolicy)
        (fun final => event ∈ final.application.config.cut.completed) count execution := by
  exact sourceServicePolicy_runUntil_of_recorded setup leaks scheduler _ count execution owner
    event ready recorded (fun current _ currentRecorded who =>
      decided_recorded_silent setup leaks bound owner event action current currentRecorded who)

private theorem decided_first_binding_activation
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (execution middle : (application setup leaks).Execution)
    (within : execution.environmentRecall.length < horizon)
    (initialized : execution ∈ ((application setup leaks).roundsFrom (initialLaw setup)
      scheduler (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
        profile) execution.environmentRecall.length).support)
    (ready : execution.application.config.cut.Ready event)
    (absent : sourceServiceTurnInput? setup leaks owner event (execution.recall owner) = none)
    (selected : .activate owner ∈ (scheduler execution.environmentRecall
      (execution.observeEnvironment (application setup leaks))).support)
    (observed : middle ∈ (execution.environmentStep (application setup leaks)
      (.activate owner)).support)
    (value : PublicationResult (L.Val payload)) :
    decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) value) owner
        (middle.recall owner) (middle.observe (application setup leaks) owner) =
      PMF.pure ((runtime setup).reactiveBinding leaks owner event payload value
        (middle.application.publicView.bindingCount owner)) := by
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  have owned := binding_actor setup event owner payload outputEq
  obtain ⟨⟨middleTrace⟩, turn, first, middleFits, middleAtTurn, middleSlots, unrecorded,
    fresh, _conform⟩ := sourceServiceFirstActivation_resources setup leaks contract timely
      turns profile owner event owned execution middle within initialized ready absent selected
        observed
  have slot := canonicalFreshSlot_canonical owner (middle.observe app owner).application fresh
  have responseEq := (runtime setup).canonicalServiceDecision_binding leaks owner
    (middle.recall owner) (middle.observe app owner) event payload outputEq codeEq node _ slot value
  have fitsView : (middle.observe app owner).application.publicView.InclusionFitsDeadline
      (runtime setup) bound event := middleFits
  dsimp only [app] at first responseEq fitsView
  simp only [decidedProfile, Function.update_self, decidedTurnPolicy]
  rw [app.turnScheduledPolicy_selected _ (0 : Fin 1) _ _ _ _ first]
  simp only [decidedOpportunity, unrecorded, Bool.false_eq_true, ↓reduceIte, fitsView,
    responseEq]
  change (if ((runtime setup).reactiveBinding leaks owner event payload value
    (middle.application.publicView.bindingCount owner)).transmission = none then _ else _) = _
  have transmitted : ((runtime setup).reactiveBinding leaks owner event payload value
      (middle.application.publicView.bindingCount owner)).transmission ≠ none := by
    cases value <;> exact Option.some_ne_none _
  rw [ite_eq_right transmitted]
  rfl

/-- A fixed latent binding value has the same whole asynchronous phase traffic
at equal initial traffic. An owner observes the same value on both sides;
foreign observers may compare different values. All first-turn and packet
premises are derived from actual initialized clear-before-first-turn prefixes. -/
theorem sourceServiceFirstBinding_decided_traffic_runUntil
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner focal : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (first second : PublicationResult (L.Val payload))
    (visible : focal = owner → first = second)
    (count : Nat) (left right : (application setup leaks).Execution)
    (within : left.environmentRecall.length + count ≤ horizon)
    (leftInitialized : left ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      left.environmentRecall.length).support)
    (rightInitialized : right ∈ ((application setup leaks).roundsFrom (initialLaw setup) scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      right.environmentRecall.length).support)
    (ready : left.application.config.cut.Ready event)
    (leftAbsent : sourceServiceTurnInput? setup leaks owner event (left.recall owner) = none)
    (rightAbsent : sourceServiceTurnInput? setup leaks owner event (right.recall owner) = none)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    ((application setup leaks).runUntil scheduler
        (decidedProfile (leaks := leaks) bound owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) first))
        (fun final => event ∈ final.application.config.cut.completed) count left).map
          ((runtime setup).bindingTraffic leaks focal) =
      ((application setup leaks).runUntil scheduler
        (decidedProfile (leaks := leaks) bound owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) second))
        (fun final => event ∈ final.application.config.cut.completed) count right).map
          ((runtime setup).bindingTraffic leaks focal) := by
  classical
  let app := application setup leaks
  let players := sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns)
    profile
  let fixedFirst := decidedProfile (leaks := leaks) bound owner event
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) first)
  let fixedSecond := decidedProfile (leaks := leaks) bound owner event
    (cast (congrArg EventGraph.EventField.Action outputEq.symm) second)
  let stop := fun final : app.Execution => event ∈ final.application.config.cut.completed
  have owned := binding_actor setup event owner payload outputEq
  induction count generalizing left right with
  | zero =>
      simpa only [ReactiveApplication.runUntil, PMF.pure_map] using congrArg PMF.pure same
  | succ count ih =>
      have networks := congrArg Prod.fst same
      have receipts := congrArg (fun traffic => traffic.2.1) same
      have environments := congrArg (fun traffic => traffic.2.2.1) same
      have publics := congrArg (fun traffic => traffic.2.2.2.2.2) same
      dsimp only [bindingTraffic] at networks receipts environments publics
      have environment : left.observeEnvironment app = right.observeEnvironment app := by
        change ReactiveApplication.EnvironmentView.mk left.network.publicView
          left.application.publicView left.receipts = _
        rw [networks, publics, receipts]
        rfl
      have rightReady : right.application.config.cut.Ready event := by
        apply (right.application.publicView_eventReady event).mp
        rw [← publics]
        exact (left.application.publicView_eventReady event).mpr ready
      have leftRunning := ready.1
      have rightRunning := rightReady.1
      simp only [ReactiveApplication.runUntil, leftRunning, rightRunning, ↓reduceIte,
        PMF.map_bind, ReactiveApplication.round, PMF.bind_bind]
      rw [← environments, ← environment]
      apply bind_congr_on_support _
      intro command selected
      by_cases current : command = .activate owner
      · subst command
        have rightSelected : .activate owner ∈
            (scheduler right.environmentRecall (right.observeEnvironment app)).support := by
          rw [← environments, ← environment]
          exact selected
        simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.activation_samples,
          PMF.bind_map, PMF.bind_bind, Function.comp_def]
        rw [← networks]
        apply bind_congr_on_support _
        intro sample sampled
        let firstMiddle := left.sampledActivation app owner sample
        let secondMiddle := right.sampledActivation app owner sample
        have leftObserved : firstMiddle ∈ (left.environmentStep app (.activate owner)).support :=
          by rw [ReactiveApplication.Execution.activation_samples, PMF.support_map]
             exact ⟨sample, sampled, rfl⟩
        have rightObserved : secondMiddle ∈
            (right.environmentStep app (.activate owner)).support := by
          rw [ReactiveApplication.Execution.activation_samples, PMF.support_map, ← networks]
          exact ⟨sample, sampled, rfl⟩
        have leftPolicy := decided_first_binding_activation setup leaks contract timely turns
          profile owner event payload outputEq codeEq node left firstMiddle (by omega)
            leftInitialized ready leftAbsent selected leftObserved first
        have rightPolicy := decided_first_binding_activation setup leaks contract timely turns
          profile owner event payload outputEq codeEq node right secondMiddle
            (by rw [← environments]; omega) rightInitialized rightReady rightAbsent rightSelected
              rightObserved second
        dsimp only [firstMiddle, secondMiddle, app] at leftPolicy rightPolicy
        have middleTraffic := (runtime setup).bindingTraffic_activation leaks left right focal
          owner same sample
        have serialEq := congrArg
          (fun traffic => traffic.2.2.2.2.2.bindingCount owner) middleTraffic
        dsimp only [bindingTraffic] at serialEq
        simp only [ReactiveApplication.Command.actor?, ReactiveApplication.resume,
          ReactiveApplication.invoke, leftPolicy, rightPolicy, PMF.pure_map, PMF.pure_bind]
        let firstNext := firstMiddle.respond app owner ((runtime setup).reactiveBinding leaks
          owner event payload first (firstMiddle.application.publicView.bindingCount owner))
        let secondNext := secondMiddle.respond app owner ((runtime setup).reactiveBinding leaks
          owner event payload second (secondMiddle.application.publicView.bindingCount owner))
        have firstReady : firstNext.application.config.cut.Ready event := by
          rw [((runtime setup).reactive_respond_application leaks firstMiddle owner _).1,
            activation_application setup leaks left firstMiddle owner leftObserved]
          exact ready
        have secondReady : secondNext.application.config.cut.Ready event := by
          rw [((runtime setup).reactive_respond_application leaks secondMiddle owner _).1,
            activation_application setup leaks right secondMiddle owner rightObserved]
          exact rightReady
        have firstRecorded : (runtime setup).eventRecorded leaks (firstNext.recall owner) event =
            true := (runtime setup).eventRecorded_respond leaks firstMiddle owner _ event rfl
        have secondRecorded : (runtime setup).eventRecorded leaks (secondNext.recall owner)
            event = true :=
          (runtime setup).eventRecorded_respond leaks secondMiddle owner _ event rfl
        rw [decided_recorded_runUntil setup leaks scheduler bound owner event _ firstNext
          firstReady firstRecorded count,
          decided_recorded_runUntil setup leaks scheduler bound owner event _ secondNext
            secondReady secondRecorded count]
        have submittedTraffic : (runtime setup).bindingTraffic leaks focal firstNext =
            (runtime setup).bindingTraffic leaks focal secondNext := by
          dsimp only [firstNext, secondNext]
          rw [← serialEq]
          exact (runtime setup).bindingTraffic_binding_response leaks firstMiddle secondMiddle
            owner focal event payload first second visible _ middleTraffic
        exact source_binding_silent_runUntil setup leaks scheduler firstReady owner payload
          outputEq codeEq node focal submittedTraffic count
      · have leftSilent := sourceServiceFirstTurn_nonowner_dispatch setup leaks bound turns
          profile owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) first) left ready owned
          command current
        have rightSilent := sourceServiceFirstTurn_nonowner_dispatch setup leaks bound turns
          profile owner event
          (cast (congrArg EventGraph.EventField.Action outputEq.symm) second) right rightReady
            owned command current
        rw [leftSilent.2, rightSilent.2]
        have rounds := (runtime setup).bindingTraffic_silent_round leaks
          (fun _ _ => PMF.pure command) focal left right same event owner payload outputEq codeEq
          node (soleReady_of_ready setup _ ready)
        simp only [ReactiveApplication.round, PMF.pure_bind] at rounds
        apply bind_eq_of_map_eq _ _ _ _ rounds
        intro nextLeft leftMoved nextRight rightMoved nextSame
        have leftDispatch : nextLeft ∈ (app.dispatch players command left).support := by
          rw [← leftSilent.1, leftSilent.2]
          exact leftMoved
        have rightDispatch : nextRight ∈ (app.dispatch players command right).support := by
          rw [← rightSilent.1, rightSilent.2]
          exact rightMoved
        have leftActual : nextLeft ∈ (app.round scheduler players left).support := by
          rw [ReactiveApplication.round, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨command, selected, leftDispatch⟩
        have rightSelected : command ∈
            (scheduler right.environmentRecall (right.observeEnvironment app)).support := by
          rw [← environments, ← environment]
          exact selected
        have rightActual : nextRight ∈ (app.round scheduler players right).support := by
          rw [ReactiveApplication.round, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨command, rightSelected, rightDispatch⟩
        have leftLength := app.round_environmentRecall_length scheduler players left nextLeft
          leftActual
        have rightLength := app.round_environmentRecall_length scheduler players right nextRight
          rightActual
        have leftNextInitialized : nextLeft ∈ (app.roundsFrom (initialLaw setup) scheduler players
            nextLeft.environmentRecall.length).support := by
          rw [leftLength, app.roundsFrom_succ, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨left, leftInitialized, leftActual⟩
        have rightNextInitialized : nextRight ∈ (app.roundsFrom (initialLaw setup) scheduler players
            nextRight.environmentRecall.length).support := by
          rw [rightLength, app.roundsFrom_succ, PMF.support_bind]
          exact Set.mem_iUnion₂.mpr ⟨right, rightInitialized, rightActual⟩
        have leftNextAbsent := sourceServiceTurnInput_nonowner_dispatch setup leaks players
          owner event
          left nextLeft command current leftAbsent leftDispatch
        have rightNextAbsent := sourceServiceTurnInput_nonowner_dispatch setup leaks players
          owner event
          right nextRight command current rightAbsent rightDispatch
        have nextReady : nextLeft.application.config.cut.Ready event := by
          rcases round_configStep setup leaks scheduler players left nextLeft leftActual with
            sameConfig | ⟨target, targetReady, action, completed⟩
          · rw [sameConfig]
            exact ready
          · have targetEq := setup.eventGraph.sequentialize_ready_unique
              left.application.config.cut targetReady ready
            subst target
            have finished : event ∈ nextLeft.application.config.cut.completed := by
              rw [left.application.config.step_cut event ready action nextLeft.application.config
                completed, EventOrder.Cut.mem_complete]
              exact Or.inl rfl
            exact (sourceServiceFirstTurn_completed_input contract timely players owner turns
              profile rfl _ (by omega) nextLeft leftNextInitialized event owned finished
                leftNextAbsent).elim
        exact ih nextLeft nextRight (by omega) leftNextInitialized rightNextInitialized nextReady
          leftNextAbsent rightNextAbsent nextSame

/-- The untouched boundary supplies the absence of an earlier owner input.
The full traffic channel retains the fixed binding draw through the entire
first-response and completion phase. -/
theorem sourceServiceFirstBinding_decided_traffic
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (owner focal : Player) (event : (graph setup).EventId) (payload : L.Ty)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (first second : PublicationResult (L.Val payload))
    (visible : focal = owner → first = second)
    (left right : (application setup leaks).Execution)
    (leftBoundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      event.val left)
    (rightBoundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      event.val right)
    (within : left.environmentRecall.length ≤ horizon)
    (same : (runtime setup).bindingTraffic leaks focal left =
      (runtime setup).bindingTraffic leaks focal right) :
    ((application setup leaks).runUntilHorizon scheduler
      (decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) first))
      (fun final => event ∈ final.application.config.cut.completed) horizon left).map
        ((runtime setup).bindingTraffic leaks focal) =
    ((application setup leaks).runUntilHorizon scheduler
      (decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) second))
      (fun final => event ∈ final.application.config.cut.completed) horizon right).map
        ((runtime setup).bindingTraffic leaks focal) := by
  have environments := congrArg (fun traffic => traffic.2.2.1) same
  dsimp only [bindingTraffic] at environments
  unfold ReactiveApplication.runUntilHorizon
  rw [← environments]
  apply sourceServiceFirstBinding_decided_traffic_runUntil setup leaks contract timely turns
    profile owner focal event payload outputEq codeEq node first second visible _ left right
    (by omega) leftBoundary.supported rightBoundary.supported
    ((ready_iff_rank setup _ event.val leftBoundary.ordered event).mpr rfl)
  · apply (sourceServiceTurnInput?_eq_none_iff owner event _).mpr
    intro entry member turn
    exact leftBoundary.untouched event rfl owner entry member
      ((PublicView.ownTurn?_spec _ owner event turn).1)
  · apply (sourceServiceTurnInput?_eq_none_iff owner event _).mpr
    intro entry member turn
    exact rightBoundary.untouched event rfl owner entry member
      ((PublicView.ownTurn?_spec _ owner event turn).1)
  · exact same

/-- A fixed binding draw and the same actual stopped traffic remain jointly
conditioned by the effective source successor's view. The original typed
configuration and an unchanged parameter are retained in the carrier. The premise
is a prior traffic
factorization, not a source marginal or posterior assumption. -/
theorem sourceServiceFirstBinding_decided_factorization
    {Seed Parameter : Type*} {Γ : SourceCtx Player L} {owner : Player} {payload : L.Ty}
    (name : VarId) (guard : SourceGuard L Γ owner name payload)
    {horizon : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (turns : Nat) (profile : BehavioralProfile setup.program)
    (focal : Player) (event : (graph setup).EventId)
    (outputEq : (graph setup).outputLayout event = .binding owner payload)
    (codeEq : cast (congrArg (EventGraph.EventCode (graph setup).layout) outputEq)
      ((graph setup).nodes event) = .bind owner payload)
    (node : nodeView (graph setup) event = .bind owner payload outputEq codeEq)
    (prior : PMF Seed) (parameter : Seed → Parameter) (source original : Seed → Config Player L Γ)
    (execution : Seed → (application setup leaks).Execution)
    (boundary : ∀ seed ∈ prior.support,
      CompletionBoundary setup leaks scheduler
        (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
        event.val (execution seed))
    (within : ∀ seed ∈ prior.support, (execution seed).environmentRecall.length ≤ horizon)
    (choice : (Config Player L Γ × Config Player L Γ × Parameter) →
      PMF (PublicationResult (L.Val payload)))
    (noise : DecisionView focal Γ → PMF _)
    (factor : prior.map (fun seed => ((source seed, original seed, parameter seed),
        (runtime setup).bindingTraffic leaks focal (execution seed))) =
      (prior.map (fun seed => (source seed, original seed, parameter seed))).bind fun pair =>
        (noise (pair.1.view focal)).map fun extra => (pair, extra)) :
    ∃ nextNoise : DecisionView focal ((name, .commitment owner payload) :: Γ) → PMF _,
      (prior.bind fun seed =>
        (choice (source seed, original seed, parameter seed)).bind fun value =>
        ((application setup leaks).runUntilHorizon scheduler
          (decidedProfile (leaks := leaks) bound owner event
            (cast (congrArg EventGraph.EventField.Action outputEq.symm) value))
          (fun final => event ∈ final.application.config.cut.completed) horizon
          (execution seed)).map fun final =>
            ((commitSuccessor name guard (source seed) value,
              commitSuccessor name guard (original seed) value, parameter seed),
                (runtime setup).bindingTraffic leaks focal final)) =
      ((prior.map (fun seed => (source seed, original seed, parameter seed))).bind fun pair =>
        (choice pair).map fun value =>
          (commitSuccessor name guard pair.1 value,
            commitSuccessor name guard pair.2.1 value, pair.2.2)).bind fun next =>
              (nextNoise (next.1.view focal)).map fun extra => (next, extra) := by
  obtain ⟨nextNoise, law⟩ := exists_updated_observation_kernel_of_readout prior
    (fun seed => (source seed, original seed, parameter seed))
    (fun seed => (runtime setup).bindingTraffic leaks focal (execution seed))
    (fun pair => pair.1.view focal) noise factor choice
    (fun pair value => (commitSuccessor name guard pair.1 value,
      commitSuccessor name guard pair.2.1 value, pair.2.2)) (fun pair => pair.1.view focal)
    (fun seed value => ((application setup leaks).runUntilHorizon scheduler
      (decidedProfile (leaks := leaks) bound owner event
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) value))
      (fun final => event ∈ final.application.config.cut.completed) horizon
      (execution seed)).map ((runtime setup).bindingTraffic leaks focal))
    (by
      intro left _ first _ right _ second _ same
      have earlier := congrArg (DecisionView.back (decide (owner = focal))) same
      simpa only [back_commit_view] using earlier)
    (by
      intro left leftSupport first _ right rightSupport second _ same traffic
      have visible : focal = owner → first = second := by
        intro equal
        subst focal
        have cell := congrArg
          (fun view : DecisionView owner ((name, .commitment owner payload) :: Γ) =>
            view.1.cells.get .here) same
        simp only [Config.view, commitSuccessor, sourceObserve, Env.get, Env.cons,
          ite_true] at cell
        exact Option.some.inj cell
      exact sourceServiceFirstBinding_decided_traffic setup leaks contract timely turns
        profile owner focal event payload outputEq codeEq node first second visible
        (execution left) (execution right) (boundary left leftSupport)
        (boundary right rightSupport) (within left leftSupport) traffic)
  refine ⟨nextNoise, ?_⟩
  simpa only [PMF.map_comp, Function.comp_def] using law

/-- The actual first-turn phase draws the aligned source commitment before
waiting, then carries that same typed successor and the same stopped traffic.
The alignment and whole-program decoder are derived from the initialized
boundary. No source draw, next-prefix law or endpoint agreement is assumed. -/
theorem sourceServiceFirstBinding_prefix_probability [Fintype Player]
    {horizon turns : Nat} {scheduler : (application setup leaks).Scheduler}
    {delay bound : (graph setup).EventId → Nat}
    (contract : AsyncContract (runtime setup) leaks (initialLaw setup) horizon scheduler
      delay bound)
    (timely : AsyncTimely (runtime setup) delay bound)
    (profile : BehavioralProfile setup.program)
    (event : (graph setup).EventId) (owner : Player) (payload : L.Ty)
    (binding : (graph setup).outputLayout event = .binding owner payload)
    (start : (application setup leaks).Execution)
    (boundary : CompletionBoundary setup leaks scheduler
      (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
      event.val start)
    (within : start.environmentRecall.length ≤ horizon) (focal : Player) :
    ∃ (before : ProtocolState setup.program)
      (site : BindingSource setup profile event start.application.config)
      (embed : Config Player L ((site.name, .commitment site.owner site.payload) :: site.Γ) →
        ProtocolState setup.program),
      sourceServicePrefix? setup event.val start.application.config = some before ∧
      ProtocolState.behavioralStateStep setup.program profile before =
        (commitKernel site.residual (site.source.view site.owner)).map
          (fun value => embed (commitSuccessor site.name site.guard site.source value)) ∧
      ((application setup leaks).runUntilHorizon scheduler
          (sourceServiceTurnPolicy setup leaks bound turns (firstTurnTiming setup turns) profile)
          (fun final => event ∈ final.application.config.cut.completed) horizon start).map
            (fun final => (sourceServicePrefix? setup (event.val + 1) final.application.config,
              (runtime setup).bindingTraffic leaks focal final)) =
        (commitKernel site.residual (site.source.view site.owner)).bind fun value =>
          ((application setup leaks).runUntilHorizon scheduler
            (decidedProfile (leaks := leaks) bound site.owner event
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value))
            (fun final => event ∈ final.application.config.cut.completed) horizon start).map
              (fun final =>
                (some (embed (commitSuccessor site.name site.guard site.source value)),
                  (runtime setup).bindingTraffic leaks focal final)) := by
  let app := application setup leaks
  have ready : start.application.config.cut.Ready event :=
    (ready_iff_rank setup _ event.val boundary.ordered event).mpr rfl
  obtain ⟨residual⟩ := boundary.sourceResidual (profile := profile)
  have beforeRead := residual.decode
  obtain ⟨Γ, names, program, residualProfile, source, refs, embedding, refsBefore, aligned,
    _admitted, _effective, _supports, lift, _liftView, _observeLift, _recoverView, _viewRecovered,
    commutes, _steps,
    _injective, transport, checkpoint⟩ := residual
  cases program with
  | ret payoffs =>
      have count := aligned.graphSuffix.countEq
      simp only [eventCount, Nat.add_zero] at count
      have inside := event.isLt
      change event.val < eventCount setup.program at inside
      omega
  | sample name fresh distribution next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have actor := aligned.actorEq ⟨0, by simp [eventCount]⟩
      rw [head] at actor
      change (graph setup).actor? event = none at actor
      rw [binding_actor setup event owner payload binding] at actor
      cases actor
  | @reveal Γ names published owner name payload fresh selected unresolved next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      have output : (graph setup).outputLayout event = .publication payload := by
        rw [← head]
        change outputLayout setup.program (embedding.event _) = _
        simpa [outputLayout, eventCount] using embedding.layout_eq ⟨0, by simp [eventCount]⟩
      cases output.symm.trans binding
  | @commit Γ names name owner payload fresh guard next =>
      have head : embedding.event ⟨0, by simp [eventCount]⟩ = event := by
        apply Fin.ext
        simpa only [Nat.add_zero] using aligned.graphSuffix.rankEq ⟨0, by simp [eventCount]⟩
      let site : BindingSource setup profile event start.application.config :=
        ⟨Γ, names, name, owner, payload, fresh, guard, next, residualProfile, refs, source,
          embedding, refsBefore, aligned, checkpoint.agrees, checkpoint.history, head⟩
      let embed := fun state : Config Player L ((name, .commitment owner payload) :: Γ) =>
        lift (Sum.inr (ProtocolState.entry next state))
      have step := commutes (ProtocolState.entry (.commit name owner fresh guard next) source)
      simp only [ProtocolState.entry] at step
      rw [ProtocolState.behavioralStateStep_commit_entry, PMF.map_comp] at step
      have policy (current : app.Execution)
          (same : current.application.config = start.application.config) :
          sourceServiceCanonicalPolicy setup leaks profile owner (current.recall owner)
              (current.observe app owner) =
            ((commitKernel residualProfile (source.view owner)).map
              (fun value => cast (congrArg EventGraph.EventField.Action site.outputEq.symm)
                value)).map (fun action => (runtime setup).canonicalServiceDecision leaks owner
                  (current.recall owner) (current.observe app owner) event action) := by
        let currentSite : BindingSource setup profile event current.application.config :=
          ⟨Γ, names, name, owner, payload, fresh, guard, next, residualProfile, refs, source,
            embedding, refsBefore, aligned, (by rw [same]; exact checkpoint.agrees),
            (by rw [same]; exact checkpoint.history), head⟩
        have currentReady : current.application.config.cut.Ready event := by
          rw [same]
          exact ready
        rw [sourceServiceCanonicalPolicy_at_event setup leaks profile owner current event
          (ownTurn?_of_ready setup current.application currentReady site.owned) site.owned]
        exact congrArg
          (PMF.map ((runtime setup).canonicalServiceDecision leaks owner (current.recall owner)
            (current.observe app owner) event)) (currentSite.compiled_choice current)
      have endpoint (value : PublicationResult (L.Val payload)) (stopped : app.Execution)
          (supported : stopped ∈ (app.runUntilHorizon scheduler
            (decidedProfile (leaks := leaks) bound owner event
              (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value))
            (fun final => event ∈ final.application.config.cut.completed) horizon start).support) :
          sourceServicePrefix? setup (event.val + 1) stopped.application.config =
            some (embed (commitSuccessor name guard source value)) := by
        have native := decided_completion contract timely event start boundary within ready
          site.owned (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value)
          (by unfold EffectiveAction; rw [nodeView_eq_bind site.outputEq site.code]; trivial)
          stopped supported
        rw [commit_step start.application.config event ready site.outputEq site.code value,
          PMF.mem_support_pure_iff] at native
        rw [native]
        unfold sourceServicePrefix?
        rw [transport 1]
        have rank : event.val = event.val := rfl
        have decoded := (checkpoint.commit (native := configState start.application.config)
          name guard event rank ready site.outputEq
          (fun ref => by
            have before := refsBefore ref ⟨0, by simp [eventCount]⟩
            rw [head] at before
            exact before) value (site.action value)).decode next
              (fun tail => embedding.ref tail.succ)
        let headOutput : EventGraph.FieldRef (graphLayout setup.program)
            (.binding owner payload) := by
          simpa [outputLayout, eventCount] using embedding.ref ⟨0, by simp [eventCount]⟩
        have headRef : headOutput = ⟨.inr event, site.outputEq⟩ := by
          simpa [headOutput, OutputEmbedding.ref, outputLayout, eventCount] using head
        have localDecode := decodeSourcePrefix?_commit fresh guard next refs source.registry
          source.revelations embedding.ref 0
          (start.application.config.complete event ready
            (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value)
            (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) value)).store
          (decodeHistory setup.program ((start.application.config.complete event ready
            (cast (congrArg EventGraph.EventField.Action site.outputEq.symm) value)
            (cast (congrArg EventGraph.EventField.Value site.outputEq.symm) value)).history.map
              (setup.eventGraph.fromModeCompletion .sequential)))
        change decodeSourcePrefix? (.commit name owner fresh guard next) refs source.registry
          source.revelations embedding.ref 1 _ _ =
            (decodeSourcePrefix? next (refs.cons (name := name) headOutput)
              (commitSuccessor name guard source value).registry
              (commitSuccessor name guard source value).revelations
              (fun tail => embedding.ref tail.succ) 0 _ _).map Sum.inr at localDecode
        rw [headRef] at localDecode
        have actualDecode := localDecode.trans (congrArg (Option.map Sum.inr) decoded)
        change (decodeSourcePrefix? (.commit name owner fresh guard next) refs source.registry
          source.revelations embedding.ref 1 _ _).map lift = _
        rw [actualDecode]
        rfl
      refine ⟨lift (ProtocolState.entry (.commit name owner fresh guard next) source), site,
        embed, beforeRead, step, ?_⟩
      rw [sourceServiceTurnPolicy_firstTurn_phase event start boundary]
      unfold ReactiveApplication.runUntilHorizon
      rw [firstTurn_runUntil_mixture event start boundary owner site.owned bound turns profile
        _ policy _, PMF.map_bind, PMF.bind_map]
      apply bind_congr_on_support _
      intro value _
      apply map_congr_on_support _
      intro stopped supported
      exact Prod.ext (endpoint value stopped supported) rfl

end Vegas
