/-
Copyright (c) 2026 VegasCore contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: VegasCore contributors
-/

import VegasTests.ConditionalResolutionState
import Vegas.Compile.WindowedExpiryStability
import Vegas.Compile.WindowedForwardLaw
import Interaction.MessageApplicationCounters

/-! # A resolving service for the generated binding/disclosure fragment

The service first offers the generated reference invocations, then reserves
two clock/relay/inclusion rounds for the other player. The relay sends actual
public envelopes. Binding nonresponse uses a source-certified public fallback;
conditional nonresponse uses the source's legal declining outcome.
-/

noncomputable section

namespace VegasTests.ConditionalApplicationImage

open Vegas Vegas.EventGraph Vegas.ToEventGraph Interaction
  Interaction.MessageApplication GameTheory GameTheory.Math.Probability

private def Safe (execution : runtime.application.PolicyExecution) : Prop :=
  (∃ cfg : Config compiled.graph, execution.native.application.base.Refines cfg) ∧
    runtime.image.CompletedPrefix execution.native.application.base.memory ∧
    runtime.image.ResolvedBindings execution.native.application.base ∧
    runtime.Consistent execution.native.application ∧
    execution.native.pool.SerialsBeforeNext

private theorem covered_nodes_nodup :
    (runtime.image.instructions.flatMap ApplicationInstruction.coveredNodes).Nodup := by
  rw [runtime_instructions]
  decide

private theorem allocated : ∀ instruction ∈ runtime.image.instructions,
    instruction.AllocatedAt 0 := by
  intro instruction hinstruction
  simp only [runtime_instructions, List.mem_cons, List.not_mem_nil, or_false] at hinstruction
  rcases hinstruction with rfl | rfl <;> unfold ApplicationInstruction.AllocatedAt <;> decide

private theorem initial_safe : Safe initialPolicyExecution :=
  ⟨⟨_, ApplicationImage.State.initial_refines compiled.graph⟩,
    ApplicationImage.CompletedPrefix.initial runtime.image compiled.graph,
    ApplicationImage.ResolvedBindings.initial runtime.image compiled.graph,
    runtime.initial_consistent initialNative, MessagePool.SerialsBeforeNext.empty⟩

private theorem run_safe
    (players : Player → runtime.application.PlayerPolicy)
    (environment : runtime.application.EnvironmentPolicy)
    (schedule : List (@Invocation Player))
    (execution next : runtime.application.PolicyExecution)
    (hsafe : Safe execution)
    (hnext : next ∈
      (runtime.application.runPolicies players environment schedule execution).support) :
    Safe next :=
  ⟨applicationPlan.windowed_runPolicies_refines (fun _ => 0) bindingSelector
      (fun _ => none) (fun _ => 10) source.env checked.legal
      players environment schedule execution next hsafe.1 hnext,
    runtime.runPolicies_completedPrefix covered_nodes_nodup
      players environment schedule execution next hsafe.2.1 hnext,
    runtime.runPolicies_resolvedBindings 0 covered_nodes_nodup allocated
      players environment schedule execution next hsafe.2.2.1 hnext,
    runtime.runPolicies_consistent players environment schedule execution next hsafe.2.2.2.1 hnext,
    runtime.application.runPolicies_serialsBeforeNext players environment schedule
      execution next hsafe.2.2.2.2 hnext⟩

private theorem expiry_cycle_progress
    (players : Player → runtime.application.PlayerPolicy)
    (hrelay : players 1 = runtime.expiryRelay)
    (execution next : runtime.application.PolicyExecution)
    (hsafe : Safe execution)
    (heven : execution.environmentHistory.length % 2 = 0)
    (hnext : next ∈ (runtime.application.runPolicies players (runtime.expiryService 1)
      (WindowedApplication.expiryCycle 1) execution).support) :
    unresolvedCount next.native.application ≤ unresolvedCount execution.native.application - 1 := by
  have hmap : next.native.application ∈
      ((runtime.application.runPolicies players (runtime.expiryService 1)
        (WindowedApplication.expiryCycle 1) execution).map
          (fun out => out.native.application)).support := by
    rw [FinDist.support_map]
    exact ⟨next, hnext, rfl⟩
  cases hactive : execution.native.application.active with
  | none =>
      rw [runtime.expiryCycle_inactive players 1 hrelay execution heven hactive,
        FinDist.mem_support_pure] at hmap
      rw [hmap, (unresolvedCount_zero_iff_finished _ hsafe.2.1).2
        (inactive_finished _ hsafe.2.1 hsafe.2.2.2.1 hactive)]
  | some activation =>
      obtain ⟨cfg, hrefines⟩ := hsafe.1
      let advanced := runtime.expiryAdvance execution.native.application
      have hrefines' : advanced.base.Refines cfg := by
        simpa only [advanced, WindowedApplication.expiryAdvance, hactive] using
          hrefines.advance (activation.since + runtime.windowOf activation.key + 1)
      have hprefix' : runtime.image.CompletedPrefix advanced.base.memory :=
        hsafe.2.1.of_done_eq (by
          simp only [advanced, WindowedApplication.expiryAdvance, hactive,
            ApplicationImage.State.advance])
      have hresolved' : runtime.image.ResolvedBindings advanced.base := by
        simpa only [advanced, WindowedApplication.expiryAdvance, hactive,
          ApplicationImage.State.advance, ApplicationImage.ResolvedBindings] using hsafe.2.2.1
      have hconsistent' := runtime.expiryAdvance_consistent _ hsafe.2.2.2.1
      have hactive' : advanced.active = some activation :=
        (runtime.expiryAdvance_overdue _ activation hactive).1
      have hoverdue : ∀ current, advanced.active = some current →
          current.since + runtime.windowOf current.key < advanced.base.memory.clock := by
        intro current hcurrent
        have heq := Option.some.inj (hactive'.symm.trans hcurrent)
        subst current
        exact (runtime.expiryAdvance_overdue _ activation hactive).2
      have hrank : unresolvedCount advanced = unresolvedCount execution.native.application := by
        simp only [advanced, WindowedApplication.expiryAdvance, hactive,
          unresolvedCount, ApplicationImage.State.advance]
      rcases overdue_expiry_resolves advanced cfg hrefines' hprefix' hresolved' hconsistent'
          hoverdue (1, execution.native.pool.nextSerial 1) with hfinished | ⟨payload, resolved,
            hdue, hhandle, hprogress⟩
      · have hinactive := finished_active_none advanced hprefix' hconsistent' hfinished
        rw [hactive'] at hinactive
        contradiction
      · have hcycle := runtime.expiryCycle_accepts players 1 hrelay execution heven
          activation hactive payload resolved (by simpa only [hactive'] using hdue)
          (hsafe.2.2.2.2.lookup_nextSerial_eq_none 1) hhandle
        rw [hcycle, FinDist.mem_support_pure] at hmap
        rw [hmap]
        rw [hrank] at hprogress
        omega

def referencePlayers (profile : SourceBehavioralProfile core) :
    Player → runtime.application.PlayerPolicy := fun who =>
  runtime.liftPlayerPolicy (applicationPlan.liftProfile (fun _ => 0) profile who)

/-- Player one has no source decisions in this fragment and performs the
permissionless expiry relay. This is a reference strategy, not deployed code
or a restriction on the set of target strategies. -/
def resolvingPlayers (profile : SourceBehavioralProfile core) :
    Player → runtime.application.PlayerPolicy :=
  Profile.update (sig := MessageApplication.policySignature Player runtime.application)
    (referencePlayers profile) 1 runtime.expiryRelay

def referenceEnvironment : runtime.application.EnvironmentPolicy :=
  runtime.liftEnvironmentPolicy (image 0).serialService

def resolvingEnvironment : runtime.application.EnvironmentPolicy :=
  runtime.application.switchEnvironmentAfter 2 referenceEnvironment (runtime.expiryService 1)

def referenceSchedule : List (@Invocation Player) := (image 0).serviceInvocations

def resolvingSchedule : List (@Invocation Player) :=
  referenceSchedule ++ WindowedApplication.expiryCycles 1 2

theorem referenceSchedule_eq :
    referenceSchedule = [.player 0, .player 0, .environment, .player 0, .environment] := rfl

private theorem reference_environment_eq
    (players : Player → runtime.application.PlayerPolicy) :
    runtime.application.runPolicies players resolvingEnvironment referenceSchedule
      initialPolicyExecution = runtime.application.runPolicies players referenceEnvironment
        referenceSchedule initialPolicyExecution := by
  apply runtime.application.runPolicies_environment_congr
  intro history view _ hhi
  have hlength : history.length < 2 := by
    simpa [referenceSchedule_eq, initialPolicyExecution, PolicyExecution.initial,
      Invocation.isEnvironment] using hhi
  simp only [resolvingEnvironment, MessageApplication.switchEnvironmentAfter, hlength, ↓reduceIte]

private theorem expiry_environment_eq
    (players : Player → runtime.application.PlayerPolicy)
    (schedule : List (@Invocation Player)) (execution : runtime.application.PolicyExecution)
    (hlength : 2 ≤ execution.environmentHistory.length) :
    runtime.application.runPolicies players resolvingEnvironment schedule execution =
      runtime.application.runPolicies players (runtime.expiryService 1) schedule execution := by
  apply runtime.application.runPolicies_environment_congr
  intro history view hlo _
  have hafter : ¬history.length < 2 := by omega
  simp only [resolvingEnvironment, MessageApplication.switchEnvironmentAfter, hafter, ↓reduceIte]

/-- The actual finite service completes every raw owner behavior. The other
player supplies the permissionless relay; no assumption of eventual completion
or restriction on the owner's messages appears in this statement. -/
theorem resolving_service_complete
    (players : Player → runtime.application.PlayerPolicy)
    (hrelay : players 1 = runtime.expiryRelay)
    (next : runtime.application.PolicyExecution)
    (hnext : next ∈ (runtime.application.runPolicies players resolvingEnvironment
      resolvingSchedule initialPolicyExecution).support) :
    next.native.application.base.memory.finished compiled.graph.nodeCount = true := by
  simp only [resolvingSchedule, WindowedApplication.expiryCycles, List.append_nil,
    MessageApplication.runPolicies_append,
    FinDist.support_bind, Set.mem_iUnion] at hnext
  obtain ⟨before, hbefore, middle, hmiddle, hnext⟩ := hnext
  have hbeforeSafe := run_safe players resolvingEnvironment referenceSchedule
    initialPolicyExecution before initial_safe hbefore
  have hmiddleSafe := run_safe players resolvingEnvironment
    (WindowedApplication.expiryCycle 1) before middle hbeforeSafe hmiddle
  have hnextSafe := run_safe players resolvingEnvironment
    (WindowedApplication.expiryCycle 1) middle next hmiddleSafe hnext
  have hbeforeLength : before.environmentHistory.length = 2 := by
    have hlength := runtime.application.runPolicies_environmentHistory_length
      players resolvingEnvironment referenceSchedule initialPolicyExecution before hbefore
    simpa [referenceSchedule_eq, initialPolicyExecution, PolicyExecution.initial,
      Invocation.isEnvironment] using hlength
  have hmiddleLength : middle.environmentHistory.length = 4 := by
    have hlength := runtime.application.runPolicies_environmentHistory_length
      players resolvingEnvironment (WindowedApplication.expiryCycle 1) before middle hmiddle
    simpa [WindowedApplication.expiryCycle, Invocation.isEnvironment, hbeforeLength] using hlength
  rw [expiry_environment_eq players _ before (by omega)] at hmiddle
  rw [expiry_environment_eq players _ middle (by omega)] at hnext
  have hfirst := expiry_cycle_progress players hrelay before middle hbeforeSafe
    (by omega) hmiddle
  have hsecond := expiry_cycle_progress players hrelay middle next hmiddleSafe (by omega) hnext
  have hbound := unresolvedCount_le_two before.native.application
  apply (unresolvedCount_zero_iff_finished _ hnextSafe.2.1).1
  omega

/-- Before timeout resolution, the other player's relay policy has no turns
and the service is exactly the source-law reference service. -/
private theorem reference_prefix_source_law (profile : SourceBehavioralProfile core) :
    (runtime.application.runPolicies (resolvingPlayers profile) resolvingEnvironment
      referenceSchedule initialPolicyExecution).map (fun out =>
        (out.native.application.base.memory.finished compiled.graph.nodeCount,
          compiled.readPublicTerminal? out.native.application.base.memory)) =
      (denoteSource core profile source.env).map
        (fun terminal => (true, some terminal.erasePubEnv)) := by
  rw [reference_environment_eq]
  have hplayers : runtime.application.runPolicies (resolvingPlayers profile)
      referenceEnvironment referenceSchedule initialPolicyExecution =
      runtime.application.runPolicies (referencePlayers profile)
        referenceEnvironment referenceSchedule initialPolicyExecution := by
    apply runtime.application.runPolicies_congr_on_schedule
    intro who hwho
    have hwhoZero : who = 0 := by simpa [referenceSchedule_eq] using hwho
    subst who
    exact Profile.update_of_ne (sig :=
      MessageApplication.policySignature Player runtime.application) _ _ (by decide)
  rw [hplayers]
  have hinitial : applicationPlan.InitialControllerReadsPublic := by
    apply applicationPlan.initialControllerReadsPublic_of_allInitialFieldsPublic
    apply compiled.allInitialFieldsPublic_of_owners
    intro field hfield
    change field ∈ [] at hfield
    cases hfield
  have horigins : (image 0).HasBindingOrigins := by decide
  exact applicationPlan.windowed_service_source_public_law checked (fun _ => 0)
    bindingSelector (fun _ => none) (fun _ => 10) profile hinitial horigins

/-- Honest source play has the original source law under the same service
that resolves every owner deviation. Expiry rounds retain the completed result
and do not change the source choices made during the reference prefix. -/
theorem resolving_source_law (profile : SourceBehavioralProfile core) :
    (runtime.application.runPolicies (resolvingPlayers profile) resolvingEnvironment
      resolvingSchedule initialPolicyExecution).map (fun out =>
        (out.native.application.base.memory.finished compiled.graph.nodeCount,
          compiled.readPublicTerminal? out.native.application.base.memory)) =
      (denoteSource core profile source.env).map
        (fun terminal => (true, some terminal.erasePubEnv)) := by
  let read := fun state : WindowedApplication.State Player simpleExpr =>
    (state.base.memory.finished compiled.graph.nodeCount,
      compiled.readPublicTerminal? state.base.memory)
  rw [resolvingSchedule, MessageApplication.runPolicies_append, FinDist.map_bind]
  calc
    _ = (runtime.application.runPolicies (resolvingPlayers profile) resolvingEnvironment
        referenceSchedule initialPolicyExecution).map (fun out => read out.native.application) := by
      rw [FinDist.map_eq_bind]
      apply FinDist.bind_congr
      intro execution hexecution
      have hsafe := run_safe (resolvingPlayers profile) resolvingEnvironment referenceSchedule
        initialPolicyExecution execution initial_safe hexecution
      have hlength : execution.environmentHistory.length = 2 := by
        have h := runtime.application.runPolicies_environmentHistory_length
          (resolvingPlayers profile) resolvingEnvironment referenceSchedule
          initialPolicyExecution execution hexecution
        simpa [referenceSchedule_eq, initialPolicyExecution, PolicyExecution.initial,
          Invocation.isEnvironment] using h
      have hfinished : execution.native.application.base.memory.finished
          compiled.graph.nodeCount = true := by
        have hmap : read execution.native.application ∈
            ((runtime.application.runPolicies (resolvingPlayers profile) resolvingEnvironment
              referenceSchedule initialPolicyExecution).map
                (fun out => read out.native.application)).support := by
          rw [FinDist.support_map]
          exact ⟨execution, hexecution, rfl⟩
        rw [reference_prefix_source_law, FinDist.support_map] at hmap
        obtain ⟨terminal, _, heq⟩ := hmap
        exact (congrArg Prod.fst heq).symm
      rw [expiry_environment_eq _ _ execution (by omega)]
      have hrelay : resolvingPlayers profile 1 = runtime.expiryRelay := Profile.update_same ..
      have hlaw := runtime.expiryCycles_inactive (resolvingPlayers profile) 1 hrelay 2
        execution (by omega) (finished_active_none _ hsafe.2.1 hsafe.2.2.2.1 hfinished)
      have hread := congrArg (fun law => law.map read) hlaw
      simpa only [FinDist.map_comp, Function.comp_def, FinDist.map_pure] using hread
    _ = _ := reference_prefix_source_law profile

end VegasTests.ConditionalApplicationImage

/-- info: 'VegasTests.ConditionalApplicationImage.resolving_service_complete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalApplicationImage.resolving_service_complete

/-- info: 'VegasTests.ConditionalApplicationImage.resolving_source_law' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms VegasTests.ConditionalApplicationImage.resolving_source_law
