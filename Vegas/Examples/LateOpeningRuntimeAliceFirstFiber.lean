/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Examples.LateOpeningRuntimeAliceFirstWitness
import Vegas.Examples.LateOpeningRuntimeAliceFirstResponse
import Vegas.Examples.LateOpeningRuntimeInitializedPrefix
import Interaction.ReactiveRoundReachability
import Vegas.EventGraph.PrivateInputs

/-! # Exact native histories at the first late sender callback

Before this callback only the protected sender response and two passive
commands have occurred. Full own recall certifies that response was silent.
The actual initialized bit and private label are both visible to their owner,
so every hidden history in this information class has the same execution.
-/

noncomputable section

namespace Vegas.Examples.LateOpeningRuntimeAliceFirstFiber

open SourceProgram EventGraph EventGraphRuntime Interaction
open GameTheory GameTheory.Protocol GameTheory.Math.Probability
open LateOpeningRuntimeSource LateOpeningRuntimeService LateOpeningRuntimeLatePrefix
  LateOpeningRuntimeAliceFirstDecision LateOpeningRuntimeInitializedPrefix

variable (weight : ℝ) (nonnegative : 0 ≤ weight)

private def beforeFirst (bit : Bool) (label : Fin 3) : app.Execution :=
  let silent := protectedSilent bit label
  let waited := recorded silent .wait silent.application
  recorded waited (.application .advanceClock)
    { waited.application with clock := waited.application.clock + 1 }

private theorem passive_round_recall (players : Player → app.Policy)
    (before after : app.Execution)
    (passive : ∀ command ∈ (LateOpeningRuntimeService.scheduler weight nonnegative
      before.environmentRecall (before.observeEnvironment app)).support,
        command.actor? app = none)
    (reached : after ∈ (app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players before).support) : after.recall = before.recall := by
  obtain ⟨command, selected, dispatched⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  obtain ⟨observed, sampled, resumed⟩ := (PMF.mem_support_bind_iff _ _ _).mp dispatched
  change after ∈ (app.resume players (command.actor? app) observed).support at resumed
  rw [passive command selected] at resumed
  change after ∈ (PMF.pure observed).support at resumed
  cases (PMF.mem_support_pure_iff _ _).mp resumed
  exact app.environmentStep_recall before after command sampled

private theorem silence_two_rounds (players : Player → app.Policy) (bit : Bool)
    (label : Fin 3) :
    app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative) players 2
      (protectedSilent bit label) = PMF.pure (beforeFirst bit label) := by
  let silent := protectedSilent bit label
  let waited := recorded silent .wait silent.application
  have first : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players silent = PMF.pure waited := by
    rw [fixed_round weight nonnegative players silent waited 1 .wait rfl rfl
      (recorded_wait silent)]
    rfl
  have second : app.round (LateOpeningRuntimeService.scheduler weight nonnegative)
      players waited = PMF.pure (beforeFirst bit label) := by
    rw [fixed_round weight nonnegative players waited (beforeFirst bit label) 2
      (.application .advanceClock) rfl rfl (recorded_clock waited)]
    rfl
  rw [ReactiveApplication.runRounds, first, PMF.pure_bind,
    ReactiveApplication.runRounds, second, PMF.pure_bind,
    ReactiveApplication.runRounds]

private theorem quiet_three_rounds (players : Player → app.Policy)
    (execution : app.Execution)
    (reached : execution ∈ (app.roundsFrom initial
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 3).support)
    (quiet : app.outputs (execution.recall alice) = []) :
    ∃ bit label, execution = beforeFirst bit label := by
  obtain ⟨state, initialized, continued⟩ := (PMF.mem_support_bind_iff _ _ _).mp reached
  change state ∈ (setup.initialLaw.map fun source =>
    State.initial (graph := nativeGraph) (setup.eventInputs source)).support at initialized
  obtain ⟨source, sourceSupported, rfl⟩ := PMF.support_map .. ▸ initialized
  obtain ⟨bit, label, rfl⟩ := (initialLaw_support source).mp sourceSupported
  change execution ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 3 (initialExecution bit label)).support at continued
  rw [ReactiveApplication.runRounds, protected_round weight nonnegative,
    ReactiveApplication.invoke, PMF.bind_map] at continued
  obtain ⟨response, _, tail⟩ := (PMF.mem_support_bind_iff _ _ _).mp continued
  let sent := (protectedDecision bit label).respond app alice response
  change execution ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 2 sent).support at tail
  obtain ⟨middle, first, second⟩ := (PMF.mem_support_bind_iff _ _ _).mp tail
  have sentCursor : sent.environmentRecall.length = 1 := rfl
  have middleCursor : middle.environmentRecall.length = 2 := by
    have cursor := app.runRounds_environmentRecall_length
      (LateOpeningRuntimeService.scheduler weight nonnegative) players 1 sent middle
        (by simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using first)
    simpa only [sentCursor] using cursor
  have firstRecall : middle.recall = sent.recall := by
    apply passive_round_recall weight nonnegative players sent middle _ first
    intro command selected
    change command ∈ (stageChoice weight nonnegative sent.environmentRecall.length
      (sent.observeEnvironment app)).support at selected
    rw [sentCursor] at selected
    have chosen := (PMF.mem_support_pure_iff _ _).mp selected
    rw [chosen]
    exact (latestAuthor_passive alice _).1
  have secondRound : execution ∈ (app.round
      (LateOpeningRuntimeService.scheduler weight nonnegative) players middle).support := by
    simpa only [ReactiveApplication.runRounds, PMF.bind_pure] using second
  have secondRecall : execution.recall = middle.recall := by
    apply passive_round_recall weight nonnegative players middle execution _ secondRound
    intro command selected
    change command ∈ (stageChoice weight nonnegative middle.environmentRecall.length
      (middle.observeEnvironment app)).support at selected
    rw [middleCursor] at selected
    have chosen := (PMF.mem_support_pure_iff _ _).mp selected
    rw [chosen]
    rfl
  have noPacket : app.outputs (sent.recall alice) = [] := by
    rw [← firstRecall, ← secondRecall]
    exact quiet
  have silent : response = (⟨none⟩ : app.Action) := by
    rcases response with ⟨transmission⟩
    cases transmission with
    | none => rfl
    | some submission =>
        have count := congrArg List.length noPacket
        change 1 = 0 at count
        omega
  subst response
  change execution ∈ (app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
    players 2 (protectedSilent bit label)).support at tail
  rw [silence_two_rounds weight nonnegative players bit label] at tail
  exact ⟨bit, label, (PMF.mem_support_pure_iff _ _).mp tail⟩

/-- Every legal bounded first late history with no sender packet is one of
the initialized, silent-prefix executions. -/
theorem first_late_normal_form (execution : app.Execution)
    (trace : (rawMenu.protocol initial LateOpeningRuntimeService.horizon
      (LateOpeningRuntimeService.scheduler weight nonnegative)).Trace
        (some ⟨22, some alice, execution⟩))
    (quiet : app.outputs (execution.recall alice) = []) :
    ∃ bit label, execution = firstLateDecision bit label := by
  have reachable := rawMenu.roundSupported_uniform initial LateOpeningRuntimeService.horizon
    (LateOpeningRuntimeService.scheduler weight nonnegative) trace
  obtain ⟨accounted, count, prior, command, cursor, reached, selected, _, moved⟩ := reachable
  change execution.environmentRecall.length + 22 = 26 at accounted
  change execution.environmentRecall.length = count + 1 at cursor
  have countEq : count = 3 := by omega
  subst count
  have priorQuiet : app.outputs (prior.recall alice) = [] := by
    rw [← app.environmentStep_recall prior execution command moved]
    exact quiet
  obtain ⟨bit, label, rfl⟩ := quiet_three_rounds weight nonnegative
    rawMenu.uniformResponses prior reached priorQuiet
  change command ∈ (stageChoice weight nonnegative
    (beforeFirst bit label).environmentRecall.length
      ((beforeFirst bit label).observeEnvironment app)).support at selected
  change command ∈ (PMF.pure (.activate alice : app.Command)).support at selected
  cases (PMF.mem_support_pure_iff _ _).mp selected
  rw [recorded_activation (beforeFirst bit label) alice (by rfl)] at moved
  exact ⟨bit, label, (PMF.mem_support_pure_iff _ _).mp moved⟩

/-- Both private setup parameters are visible in the sender's actual view. -/
theorem first_view_injective : Function.Injective
    (fun parameter : Parameter =>
      (firstLateDecision parameter.1 parameter.2).observe app alice) := by
  rintro ⟨bit, label⟩ ⟨otherBit, otherLabel⟩ same
  have bits := congrArg (fun view : app.PlayerView =>
    view.application.candidates (.initial LateOpeningRuntimeReadout.aliceInput)) same
  have sameBit : bit = otherBit := by
    change CommitmentCandidate.openable (⟨.bool, bit⟩ : Raw simpleExpr) =
      .openable ⟨.bool, otherBit⟩ at bits
    have raw := CommitmentCandidate.openable.inj bits
    have decoded := congrArg (fun value : Raw simpleExpr => value.as? .bool) raw
    simpa only [Raw.as?_mk, Option.some.injEq] using decoded
  have labels := congrArg (fun view : app.PlayerView =>
    view.application.observation.store (.inl LateOpeningRuntimeReadout.labelInput)) same
  have sameLabel : label = otherLabel := by
    change some (labelValue label) = some (labelValue otherLabel) at labels
    have values := congrArg (fun value : Label => value.val) (Option.some.inj labels)
    apply Fin.ext
    change (label.val : Int) = (otherLabel.val : Int) at values
    exact_mod_cast values
  exact Prod.ext sameBit sameLabel

/-- Every actual hidden history of this sender information class has exactly
the initialized silent-prefix state, including all physical and private recall. -/
theorem information_history_state
    (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
    (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
      alice site.1) (bit : Bool) (label : Fin 3)
    (current : representative.1.state = some ⟨22, some alice, firstLateDecision bit label⟩)
    (history : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory alice site.1) :
    history.1.state = some ⟨22, some alice, firstLateDecision bit label⟩ := by
  let decision := LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label
  obtain ⟨other, stateEq, _, sameView, _⟩ := decision_of_information weight nonnegative
    site representative decision current history
  have trace := stateEq ▸ history.1.trace
  obtain ⟨otherBit, otherLabel, normal⟩ := first_late_normal_form weight nonnegative
    other.execution trace other.quiet
  change (firstLateDecision bit label).observe app alice =
    other.execution.observe app alice at sameView
  rw [normal] at sameView
  have parameters := @first_view_injective (bit, label) (otherBit, otherLabel) sameView
  cases parameters
  exact stateEq.trans (congrArg (fun execution =>
    some (⟨22, some alice, execution⟩ : app.Control)) normal)

variable
  (site : (LateOpeningRuntimeNash.model weight nonnegative).InformationSite alice)
  (representative : (LateOpeningRuntimeNash.model weight nonnegative).InformationHistory
    alice site.1) (bit : Bool) (label : Fin 3)
  (current : representative.1.state = some ⟨22, some alice, firstLateDecision bit label⟩)

include current in
/-- Any current response law has its concrete initialized continuation law;
averaging over this information class adds no hidden state uncertainty. -/
theorem finalLaw_eq_physical
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    LateOpeningRuntimeAliceFirstResponse.finalLaw weight nonnegative site representative
      (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
        current assessment law =
      (LateOpeningRuntimeAliceFirstResponse.responseLaw weight nonnegative site law).bind
        fun response => app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
          22 ((firstLateDecision bit label).respond app alice response) := by
  unfold LateOpeningRuntimeAliceFirstResponse.finalLaw
  calc
    _ = (assessment.belief alice site).bind fun _ =>
        (LateOpeningRuntimeAliceFirstResponse.responseLaw weight nonnegative site law).bind
          fun response => app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
            (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
              (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
            22 ((firstLateDecision bit label).respond app alice response) := by
      apply bind_congr_on_support
      intro history _
      have actual := information_history_state weight nonnegative site representative bit label
        current history
      have recovered := (decisionOfInformation_spec weight nonnegative site representative
        (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
          current history).1
      have same := congrArg ReactiveApplication.Control.execution
        (Option.some.inj (recovered.symm.trans actual))
      apply bind_congr_on_support
      intro response _
      unfold LateOpeningRuntimeAliceFirstPacket.responseLaw
      exact congrArg (fun execution : app.Execution =>
        app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
          22 (execution.respond app alice response)) same
    _ = _ := PMF.bind_const _ _

include current in
open Classical in
theorem context_value_eq_physical (reward forfeit : ℝ) (deposit : Player → ℝ)
    (assessment : (LateOpeningRuntimeNash.model weight nonnegative).BehavioralAssessment)
    (law : PMF ((LateOpeningRuntimeNash.model weight nonnegative).Choice alice site.1)) :
    (LateOpeningRuntimeAliceFirstResponse.context weight nonnegative site reward forfeit deposit
      assessment).value ((assessment.strategy alice).withLaw site.1 law) =
      expect ((LateOpeningRuntimeAliceFirstResponse.responseLaw weight nonnegative site law).bind
        fun response => app.runRounds (LateOpeningRuntimeService.scheduler weight nonnegative)
          (rawMenu.decodeProfile initial LateOpeningRuntimeService.horizon
            (LateOpeningRuntimeService.scheduler weight nonnegative) assessment.strategy)
          22 ((firstLateDecision bit label).respond app alice response))
        (LateOpeningRuntimeAliceContinuation.aliceUtility reward forfeit deposit) := by
  rw [LateOpeningRuntimeAliceFirstResponse.context_value weight nonnegative site representative
    (LateOpeningRuntimeAliceFirstWitness.decisionHistory weight nonnegative bit label)
      current reward forfeit deposit assessment law,
    finalLaw_eq_physical weight nonnegative site representative bit label current assessment law]

end Vegas.Examples.LateOpeningRuntimeAliceFirstFiber
