/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperOriginalCommands

/-! # The original native prefix with a sent helper's responses forced silent -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

private theorem response_clear (execution : app.Execution) (owner : Player)
    (action : app.Action) (clear : execution.application.current.excluded = ∅) :
    (execution.respond app owner action).application.current.excluded = ∅ := by
  rcases action with ⟨transmission⟩
  cases transmission <;> exact clear

private theorem advance_clear (execution : app.Execution)
    (clear : execution.application.current.excluded = ∅) :
    (advance execution).application.current.excluded = ∅ := by
  let raw := (PhaseBindingRepair.rawClock runtime leaks execution).application
  change raw.normalize.current.excluded = ∅
  exact (PhaseRuntimeState.settle_physical raw.phases raw.generation raw.entry raw.current
    raw.retired).1.trans clear

private theorem external_input (hidden owner : Player) (different : owner ≠ hidden)
    (left right : app.Execution)
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right) :
    (left.recall owner, left.observe app owner) =
      (right.recall owner, right.observe app owner) := by
  have visible := congrFun (congrArg (fun data => data.2.2.2.2) same) owner
  change (if owner = hidden then none else some (left.recall owner, left.observe app owner)) =
    (if owner = hidden then none else some (right.recall owner, right.observe app owner)) at visible
  exact Option.some.inj (by simpa only [different, ite_false] using visible)

open Classical in
/-- The actual original run, through its last eligible inclusion, is independent
of a sent helper's hidden preparation when that helper's later callbacks WAIT.
Every other player's entire raw policy is unchanged. The observation stops at
actual original admission and retains that complete boundary observation,
before publication could expose the hidden value. -/
theorem original_helper_stopped_observation (seed : Seeds) (players : Player → app.Policy)
    (hidden : Player)
    (waited : ∀ past view, players hidden past view = PMF.pure ⟨none⟩)
    (count remaining : Nat) (left right : app.Execution)
    (leftTrace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining + count, none, left⟩))
    (rightTrace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining + count, none, right⟩))
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right)
    (leftOriginal : left.application.attempt = originalAttempt)
    (rightOriginal : right.application.attempt = originalAttempt)
    (leftClear : left.application.current.excluded = ∅)
    (rightClear : right.application.current.excluded = ∅)
    (lower : 5 ≤ left.environmentRecall.length)
    (upper : left.environmentRecall.length + count ≤ 24) :
    (app.runUntil (family seed) players
      (fun current => current.application.attempt ≠ originalAttempt) count left).map
        (phaseExternalObservation runtime leaks hidden) =
      (app.runUntil (family seed) players
        (fun current => current.application.attempt ≠ originalAttempt) count right).map
          (phaseExternalObservation runtime leaks hidden) := by
  classical
  induction count generalizing remaining left right with
  | zero =>
      simp only [ReactiveApplication.runUntil, PMF.pure_map]
      exact congrArg PMF.pure same
  | succ count ih =>
      have fuel : remaining + (count + 1) = (remaining + count) + 1 := by omega
      rw [fuel] at leftTrace rightTrace
      have network : left.network = right.network := congrArg Prod.fst same
      have receipts : left.receipts = right.receipts := congrArg (fun data => data.2.1) same
      have service : left.environmentRecall = right.environmentRecall :=
        congrArg (fun data => data.2.2.1) same
      have environment : left.observeEnvironment app = right.observeEnvironment app :=
        congrArg (fun data => data.2.2.2.1) same
      have publicView : left.application.publicView = right.application.publicView :=
        congrArg (fun data => data.2.2.2.1.application) same
      have nativePublic := congrArg PhasePublicView.native publicView
      have nativeViews (who : Player) (different : who ≠ hidden) :
          left.application.current.native.playerView who =
            right.application.current.native.playerView who :=
        congrArg (fun input => input.2.application.1)
          (external_input hidden who different left right same)
      have recalled (who : Player) (different : who ≠ hidden) :
          left.recall who = right.recall who :=
        congrArg Prod.fst (external_input hidden who different left right same)
      obtain ⟨phases, generation, retired, commitment⟩ := original_helper_metadata seed
        ((remaining + count) + 1) left right leftTrace rightTrace hidden same
          leftOriginal rightOriginal
      have opaqueRight : ∀ phase ∈ right.application.phases.head?, phase.kind = .commitment := by
        rwa [← phases]
      have continuation (first second : app.Execution)
          (firstTrace : (app.protocol initial horizon (family seed)).Trace
            (some ⟨remaining + count, none, first⟩))
          (secondTrace : (app.protocol initial horizon (family seed)).Trace
            (some ⟨remaining + count, none, second⟩))
          (observed : phaseExternalObservation runtime leaks hidden first =
            phaseExternalObservation runtime leaks hidden second)
          (firstClear : first.application.current.excluded = ∅)
          (secondClear : second.application.current.excluded = ∅)
          (length : first.environmentRecall.length = left.environmentRecall.length + 1) :
          (app.runUntil (family seed) players
            (fun current => current.application.attempt ≠ originalAttempt) count first).map
              (phaseExternalObservation runtime leaks hidden) =
            (app.runUntil (family seed) players
              (fun current => current.application.attempt ≠ originalAttempt) count second).map
                (phaseExternalObservation runtime leaks hidden) := by
        have attempts : first.application.attempt = second.application.attempt :=
          congrArg (fun data => data.2.2.2.1.application.attempt) observed
        by_cases original : first.application.attempt = originalAttempt
        · exact ih remaining first second firstTrace secondTrace observed original
            (attempts.symm.trans original) firstClear secondClear (by omega) (by omega)
        · have other : second.application.attempt ≠ originalAttempt :=
            fun equal => original (attempts.trans equal)
          rw [app.runUntil_of_stop (family seed) players _ count first original,
            app.runUntil_of_stop (family seed) players _ count second other,
            PMF.pure_map, PMF.pure_map]
          exact congrArg PMF.pure observed
      generalize commandEq : choose seed left.environmentRecall (left.observeEnvironment app) =
        command
      have rightCommand : choose seed right.environmentRecall (right.observeEnvironment app) =
          command := by rw [← service, ← environment]; exact commandEq
      have selectedLeft : command ∈
          (family seed left.environmentRecall (left.observeEnvironment app)).support := by
        simp only [family, commandEq, PMF.mem_support_pure_iff]
      have selectedRight : command ∈
          (family seed right.environmentRecall (right.observeEnvironment app)).support := by
        simp only [family, rightCommand, PMF.mem_support_pure_iff]
      have firstRound : app.round (family seed) players left =
          app.dispatch players command left := by
        simp only [ReactiveApplication.round, family, commandEq, PMF.pure_bind]
      have secondRound : app.round (family seed) players right =
          app.dispatch players command right := by
        simp only [ReactiveApplication.round, family, rightCommand, PMF.pure_bind]
      rw [ReactiveApplication.runUntil, ReactiveApplication.runUntil]
      rw [ite_eq_right (not_not_intro leftOriginal),
        ite_eq_right (not_not_intro rightOriginal)]
      rw [firstRound, secondRound,
        PMF.map_bind, PMF.map_bind]
      cases command with
      | wait =>
          let first : app.Execution := { left with environmentRecall :=
            left.environmentRecall ++ [⟨left.observeEnvironment app, .wait⟩] }
          let second : app.Execution := { right with environmentRecall :=
            right.environmentRecall ++ [⟨right.observeEnvironment app, .wait⟩] }
          have firstMoved : first ∈ (left.environmentStep app .wait).support := by
            simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
              PMF.mem_support_pure_iff, first]
          have secondMoved : second ∈ (right.environmentStep app .wait).support := by
            simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
              PMF.mem_support_pure_iff, second]
          obtain ⟨firstTrace⟩ := app.raw_trace_environment initial horizon (family seed)
            (remaining + count) left first .wait leftTrace selectedLeft firstMoved
          obtain ⟨secondTrace⟩ := app.raw_trace_environment initial horizon (family seed)
            (remaining + count) right second .wait rightTrace selectedRight secondMoved
          have observed := helper_external_append hidden left right same
            first.environmentRecall second.environmentRecall (by
              dsimp [first, second]
              rw [service, environment])
          simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
            PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
            ReactiveApplication.resume]
          exact continuation first second firstTrace secondTrace observed leftClear rightClear (by
            simp only [first, List.length_append, List.length_singleton])
      | activate actor =>
          let first := completeActivation left actor
          let second := completeActivation right actor
          have observed := helper_preparation_activation hidden actor left right same
          have firstMoved : first ∈ (left.environmentStep app (.activate actor)).support := by
            rw [completeActivation_law]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl
          have secondMoved : second ∈ (right.environmentStep app (.activate actor)).support := by
            rw [completeActivation_law]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl
          obtain ⟨firstTrace⟩ := app.raw_trace_environment initial horizon (family seed)
            (remaining + count) left first (.activate actor) leftTrace selectedLeft firstMoved
          obtain ⟨secondTrace⟩ := app.raw_trace_environment initial horizon (family seed)
            (remaining + count) right second (.activate actor) rightTrace selectedRight secondMoved
          have kernel : players actor (first.recall actor) (first.observe app actor) =
              players actor (second.recall actor) (second.observe app actor) := by
            by_cases own : actor = hidden
            · subst actor
              exact (waited _ _).trans (waited _ _).symm
            · exact congrArg (fun input => players actor input.1 input.2)
                (external_input hidden actor own first second observed)
          simp only [ReactiveApplication.dispatch, completeActivation_law, PMF.pure_bind,
            ReactiveApplication.Command.actor?, ReactiveApplication.resume,
            ReactiveApplication.invoke, PMF.bind_map]
          change (players actor (first.recall actor) (first.observe app actor)).bind _ =
            (players actor (second.recall actor) (second.observe app actor)).bind _
          rw [kernel]
          apply bind_congr_on_support
          intro action chosen
          have sameResponse : phaseExternalObservation runtime leaks hidden
              (first.respond app actor action) =
            phaseExternalObservation runtime leaks hidden (second.respond app actor action) := by
            by_cases own : actor = hidden
            · subst actor
              rw [waited] at chosen
              cases (PMF.mem_support_pure_iff _ _).mp chosen
              exact helper_preparation_silent hidden first second observed
            · exact helper_preparation_response hidden actor own first second observed action
          obtain ⟨firstAfter⟩ := app.raw_trace_respond initial horizon (family seed)
            (remaining + count) first actor action firstTrace
          obtain ⟨secondAfter⟩ := app.raw_trace_respond initial horizon (family seed)
            (remaining + count) second actor action secondTrace
          exact continuation _ _ firstAfter secondAfter sameResponse
            (response_clear first actor action leftClear)
            (response_clear second actor action rightClear) (by
              rw [app.respond_environmentRecall]
              change (left.environmentRecall ++ [_]).length = _
              simp only [List.length_append, List.length_singleton])
      | «include» identifier =>
          let first : app.Execution := { left.includePending app identifier with
            environmentRecall :=
            left.environmentRecall ++ [⟨left.observeEnvironment app, .«include» identifier⟩] }
          let second : app.Execution := { right.includePending app identifier with
            environmentRecall :=
            right.environmentRecall ++ [⟨right.observeEnvironment app, .«include» identifier⟩] }
          have included := phase_include_external_congr runtime leaks left right hidden phases
            generation retired nativePublic nativeViews network receipts service recalled
              leftClear rightClear commitment identifier
          have observed := helper_external_append hidden _ _ included
            first.environmentRecall second.environmentRecall (by
              dsimp [first, second]
              rw [service, environment])
          have firstMoved : first ∈ (left.environmentStep app (.«include» identifier)).support := by
            simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
              PMF.mem_support_pure_iff, first]
          have secondMoved : second ∈
              (right.environmentStep app (.«include» identifier)).support := by
            simp only [ReactiveApplication.Execution.environmentStep, PMF.pure_map,
              PMF.mem_support_pure_iff, second]
          obtain ⟨firstTrace⟩ := app.raw_trace_environment initial horizon (family seed)
            (remaining + count) left first (.«include» identifier) leftTrace selectedLeft firstMoved
          obtain ⟨secondTrace⟩ := app.raw_trace_environment initial horizon (family seed)
            (remaining + count) right second (.«include» identifier)
              rightTrace selectedRight secondMoved
          have firstClear := BindingShadow.include_commitmentPhase_clear runtime leaks left
            leftClear commitment identifier
          have secondClear := BindingShadow.include_commitmentPhase_clear runtime leaks right
            rightClear opaqueRight identifier
          simp only [ReactiveApplication.dispatch, ReactiveApplication.Execution.environmentStep,
            PMF.pure_map, PMF.pure_bind, ReactiveApplication.Command.actor?,
            ReactiveApplication.resume]
          exact continuation first second firstTrace secondTrace observed firstClear secondClear (by
            simp only [first, List.length_append, List.length_singleton])
      | application operation =>
          have literal : originalCommand seed left.environmentRecall.length
              left.environmentRecall (left.observeEnvironment app) = .application operation :=
            (choose_original seed _ _ leftOriginal).symm.trans commandEq
          have operationEq := original_helper_application_command seed left.environmentRecall.length
            left.environmentRecall (left.observeEnvironment app) operation lower (by omega) literal
          subst operation
          have observed : phaseExternalObservation runtime leaks hidden (advance left) =
              phaseExternalObservation runtime leaks hidden (advance right) :=
            phase_clock_external_congr runtime leaks left right hidden phases generation retired
              nativePublic nativeViews network receipts service recalled leftClear rightClear
          have firstMoved : advance left ∈
              (left.environmentStep app (.application .advanceClock)).support := by
            rw [advance_law]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl
          have secondMoved : advance right ∈
              (right.environmentStep app (.application .advanceClock)).support := by
            rw [advance_law]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl
          obtain ⟨firstTrace⟩ := app.raw_trace_environment initial horizon (family seed)
            (remaining + count) left (advance left) (.application .advanceClock)
              leftTrace selectedLeft firstMoved
          obtain ⟨secondTrace⟩ := app.raw_trace_environment initial horizon (family seed)
            (remaining + count) right (advance right) (.application .advanceClock)
              rightTrace selectedRight secondMoved
          simp only [ReactiveApplication.dispatch, advance_law, PMF.pure_bind,
            ReactiveApplication.Command.actor?, ReactiveApplication.resume]
          exact continuation _ _ firstTrace secondTrace observed
            (advance_clear left leftClear) (advance_clear right rightClear) (by
              change (left.environmentRecall ++ [_]).length = _
              simp only [List.length_append, List.length_singleton])

/-- Discarding the boundary data only after actual original retirement gives
the original stopped channel of the full native round evaluator. -/
theorem original_helper_run_observation (seed : Seeds) (players : Player → app.Policy)
    (hidden : Player)
    (waited : ∀ past view, players hidden past view = PMF.pure ⟨none⟩)
    (count remaining : Nat) (left right : app.Execution)
    (leftTrace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining + count, none, left⟩))
    (rightTrace : (app.protocol initial horizon (family seed)).Trace
      (some ⟨remaining + count, none, right⟩))
    (same : phaseExternalObservation runtime leaks hidden left =
      phaseExternalObservation runtime leaks hidden right)
    (leftOriginal : left.application.attempt = originalAttempt)
    (rightOriginal : right.application.attempt = originalAttempt)
    (leftClear : left.application.current.excluded = ∅)
    (rightClear : right.application.current.excluded = ∅)
    (lower : 5 ≤ left.environmentRecall.length)
    (upper : left.environmentRecall.length + count ≤ 24) :
    (app.runRounds (family seed) players count left).map (originalHelperObservation hidden) =
      (app.runRounds (family seed) players count right).map (originalHelperObservation hidden) := by
  classical
  rw [original_observation_rounds_stopped (family seed) players hidden count remaining left
    leftTrace, original_observation_rounds_stopped (family seed) players hidden count remaining
      right rightTrace]
  have stopped := original_helper_stopped_observation seed players hidden waited count remaining
    left right leftTrace rightTrace same leftOriginal rightOriginal leftClear rightClear lower upper
  have projected := congrArg (fun law => law.map fun external =>
    if external.2.2.2.1.application.attempt = originalAttempt then some external else none) stopped
  have reading : (fun execution : app.Execution =>
      if (phaseExternalObservation runtime leaks hidden execution).2.2.2.1.application.attempt =
          originalAttempt then some (phaseExternalObservation runtime leaks hidden execution)
        else none) = originalHelperObservation hidden := by
    funext execution
    change (if execution.application.attempt = originalAttempt then
      some (phaseExternalObservation runtime leaks hidden execution) else none) = _
    by_cases original : execution.application.attempt = originalAttempt <;>
      simp only [originalHelperObservation, original, ite_true, ite_false]
  simpa only [PMF.map_comp, Function.comp_def, reading] using projected

end Vegas.Examples.CommitSeedBroadcast
