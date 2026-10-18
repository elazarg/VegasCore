/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.CommitSeedBroadcastHelperConditionalOriginalLaw

/-! # The actual next original decision input in the helper observation channel -/

noncomputable section

namespace Vegas.Examples.CommitSeedBroadcast

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory.Protocol GameTheory.Math.Probability

open Classical in
/-- The literal input at the next scheduled original callback of this owner.
The original service command is read from the existing controller. -/
def originalHelperNextInput (seed : Seeds) (owner : Player) (execution : app.Execution) :
    Option (List app.PlayerEntry × app.PlayerView) :=
  if execution.application.attempt = originalAttempt ∧
      choose seed execution.environmentRecall (execution.observeEnvironment app) = .activate owner
  then some ((completeActivation execution owner).recall owner,
    (completeActivation execution owner).observe app owner)
  else none

/-- For an unsent owner, the actual upcoming full decision input factors
through the original external channel, including its entire recalled word. -/
theorem original_helper_next_input_factors (seed : Seeds) (hidden owner : Player)
    (different : owner ≠ hidden) :
    (originalHelperNextInput seed owner).FactorsThrough (originalHelperObservation hidden) := by
  classical
  intro left right same
  by_cases original : left.application.attempt = originalAttempt
  · have rightOriginal : right.application.attempt = originalAttempt := by
      by_contra retired
      simp only [originalHelperObservation, original, retired, ite_true, ite_false] at same
      cases same
    have external : phaseExternalObservation runtime leaks hidden left =
        phaseExternalObservation runtime leaks hidden right := by
      exact Option.some.inj (by simpa only [originalHelperObservation, original,
        rightOriginal, ite_true] using same)
    have service : left.environmentRecall = right.environmentRecall :=
      congrArg (fun data => data.2.2.1) external
    have environment : left.observeEnvironment app = right.observeEnvironment app :=
      congrArg (fun data => data.2.2.2.1) external
    have activation := helper_preparation_activation hidden owner left right external
    have visible := congrFun (congrArg (fun data => data.2.2.2.2) activation) owner
    change (if owner = hidden then none else
      some ((completeActivation left owner).recall owner,
        (completeActivation left owner).observe app owner)) =
      (if owner = hidden then none else
        some ((completeActivation right owner).recall owner,
          (completeActivation right owner).observe app owner)) at visible
    simp only [different, ite_false] at visible
    simp only [originalHelperNextInput, original, rightOriginal, true_and, service, environment]
    split
    · exact visible
    · rfl
  · have rightRetired : right.application.attempt ≠ originalAttempt := by
      intro rightOriginal
      simp only [originalHelperObservation, original, rightOriginal, ite_true, ite_false] at same
      cases same
    simp only [originalHelperNextInput, original, rightRetired, false_and, ite_false]

/-- The original initialized same-packet reference experiments give equal
laws of actual scheduled full inputs, not merely equal public state laws. -/
theorem initial_helper_original_next_input_law (seed : Seeds)
    (players : Player → app.Policy) (hidden owner : Player) (different : owner ≠ hidden)
    (waited : ∀ past view, players hidden past view = PMF.pure ⟨none⟩)
    (count : Nat) (bounded : count ≤ 19) (first second : WitnessedSubmission graph)
    (packet : app.packet (app.submit (initialCallback hidden).application hidden first) hidden
        ((initialCallback hidden).network.known hidden) first =
      app.packet (app.submit (initialCallback hidden).application hidden second) hidden
        ((initialCallback hidden).network.known hidden) second) :
    (app.runRounds (family seed) players count (initialHelperFrame hidden first)).map
        (originalHelperNextInput seed owner) =
      (app.runRounds (family seed) players count (initialHelperFrame hidden second)).map
        (originalHelperNextInput seed owner) := by
  let extension := Function.extend (originalHelperObservation hidden)
    (originalHelperNextInput seed owner) (fun _ => none)
  have factor (law : PMF app.Execution) : law.map (originalHelperNextInput seed owner) =
      (law.map (originalHelperObservation hidden)).map extension := by
    rw [PMF.map_comp]
    congr 1
    funext execution
    exact ((original_helper_next_input_factors seed hidden owner different).extend_apply
      (fun _ => none) execution).symm
  rw [factor, factor, initial_helper_original_run_law seed players hidden waited count bounded
    first second packet]

open Classical in
/-- Read the original owner's literal information from an actual actor control. -/
def originalHelperDecisionInput (owner : Player) : app.ProtocolState →
    Option (List app.PlayerEntry × app.PlayerView)
  | none => none
  | some current =>
      if current.actor = some owner ∧ current.execution.application.attempt = originalAttempt
      then some (current.execution.recall owner, current.execution.observe app owner)
      else none

/-- The scheduled-input readout is exactly the actual next-command kernel.
No hypothetical activation or equality with a desired input is assumed. -/
theorem original_helper_next_input_command (seed : Seeds) (owner : Player)
    (remaining : Nat) (execution : app.Execution) :
    (family seed execution.environmentRecall (execution.observeEnvironment app)).bind
      (fun command => (execution.environmentStep app command).map fun active =>
        originalHelperDecisionInput owner (some ⟨remaining, command.actor? app, active⟩)) =
      PMF.pure (originalHelperNextInput seed owner execution) := by
  classical
  change (PMF.pure (choose seed _ _)).bind _ = _
  rw [PMF.pure_bind]
  generalize commandEq : choose seed execution.environmentRecall
    (execution.observeEnvironment app) = command
  cases command with
  | wait =>
      simp only [ReactiveApplication.Command.actor?, originalHelperDecisionInput,
        reduceCtorEq, false_and, ite_false]
      simp only [originalHelperNextInput, commandEq,
        reduceCtorEq, and_false, ite_false]
      exact PMF.map_const _ _
  | «include» identifier =>
      simp only [ReactiveApplication.Command.actor?, originalHelperDecisionInput,
        reduceCtorEq, false_and, ite_false]
      simp only [originalHelperNextInput, commandEq, reduceCtorEq, and_false, ite_false]
      exact PMF.map_const _ _
  | application operation =>
      simp only [ReactiveApplication.Command.actor?, originalHelperDecisionInput,
        reduceCtorEq, false_and, ite_false]
      simp only [originalHelperNextInput, commandEq, reduceCtorEq, and_false, ite_false]
      exact PMF.map_const _ _
  | activate actor =>
      rw [completeActivation_law]
      simp only [PMF.pure_map, ReactiveApplication.Command.actor?, originalHelperDecisionInput,
        Option.some.injEq, originalHelperNextInput, commandEq,
        ReactiveApplication.Command.activate.injEq]
      by_cases own : actor = owner
      · subst actor
        have application : (completeActivation execution owner).application =
            execution.application := rfl
        simp only [application, and_comm]
      · simp only [own, false_and, and_false, ite_false]

/-- The actual original scheduled full-input joint retains the entire original
preparation posterior after conditioning on the public initial packet word.
The seed remains an explicit original coordinate in both laws. -/
theorem single_helper_conditional_next_input_joint (players : Player → app.Policy)
    (reference : Seeds) (packets : Finset (Message Player app.Payload))
    (present : packets ∈ ((app.runRounds (family reference) players 5 initialExecution).map
      initialPublicPackets).support)
    (hidden owner : Player) (different : owner ≠ hidden) (nonempty : packets.Nonempty)
    (owned : ∀ message ∈ packets, message.sender = hidden)
    (count : Nat) (bounded : count ≤ 19) :
    ∃ material : WitnessedSubmission graph,
      initialPublicPackets (initialHelperFrame hidden material) = packets ∧
      (fiberPosterior (nativeSeedLaw.bind fun seed =>
        (app.runRounds (family seed) players 5 initialExecution).map fun frame => (frame, seed))
        (fun outcome => initialPublicPackets outcome.1) packets).bind
        (fun original =>
          (app.runRounds (family original.2)
            (Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩)) count original.1).map
            fun next => (original.1, (original.2, originalHelperNextInput original.2 owner next))) =
      bindPairLaw (fiberPosterior (app.runRounds (family reference) players 5 initialExecution)
        initialPublicPackets packets) (fun _ => nativeSeedLaw.bind fun seed =>
          (app.runRounds (family seed)
            (Function.update players hidden (fun _ _ => PMF.pure ⟨none⟩)) count
            (initialHelperFrame hidden material)).map fun next =>
              (seed, originalHelperNextInput seed owner next)) := by
  obtain ⟨material, materialPackets, joint⟩ := single_helper_conditional_original_joint players
    reference packets present hidden nonempty owned count bounded
  refine ⟨material, materialPackets, ?_⟩
  let read := fun seed => Function.extend (originalHelperObservation hidden)
    (originalHelperNextInput seed owner) (fun _ => none)
  have factor (seed : Seeds) (execution : app.Execution) :
      read seed (originalHelperObservation hidden execution) =
        originalHelperNextInput seed owner execution :=
    (original_helper_next_input_factors seed hidden owner different).extend_apply
      (fun _ => none) execution
  have mapped := congrArg (fun law => law.map fun outcome =>
    (outcome.1, (outcome.2.1, read outcome.2.1 outcome.2.2))) joint
  simpa only [bindPairLaw, PMF.map_bind, PMF.map_comp, Function.comp_def, factor] using mapped

end Vegas.Examples.CommitSeedBroadcast
