/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateInputs
import Interaction.SealedCandidateSubmission

/-! # Admission and delivery of generated candidate messages

Each packet submitted by a generated graph policy is ready for admission in
its actual candidate execution. The owner's private cache supplies any required
opening. Arbitrary opponent traffic cannot invalidate the packet while its
site remains unfinished; draining the pool completes the site.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)

private theorem nodeCommand_candidate_ready (who : Player) (policy : CommitPolicy G who)
    (execution : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hmemory : SealedResolution.PreparedCandidateOwner (supported.resolvingRuntime nullValue window)
      who execution)
    (node : Fin G.nodeCount) (store : Store L)
    (law : FinDist (supported.compile.messageApplication (Value := L.Val ty)).PlayerCommand)
    (hselected : supported.nodeCommand? who execution.native.application.visible.timeouts
      policy.proposals
      ((supported.resolvingRuntime nullValue window).eventHistory
        ((supported.resolvingRuntime nullValue window).registeredPlayerHistory
          (execution.principalHistory who)))
      ((supported.resolvingRuntime nullValue window).eventView
        ((supported.resolvingRuntime nullValue window).registeredPlayerView
          (State.observe _ execution.native who))) store node = some law)
    (payload : SealedProgram.Payload Player (L.Val ty)) (hsubmit : .submit payload ∈ law.support)
    (serial : Nat) :
    SealedResolution.CandidateSubmissionReady (supported.resolvingRuntime nullValue window)
      execution.native.application ⟨(who, serial), payload⟩ node.val := by
  let runtime := supported.resolvingRuntime nullValue window
  let state := execution.native.application.visible
  let history := runtime.eventHistory
    (runtime.registeredPlayerHistory (execution.principalHistory who))
  let view := runtime.eventView (runtime.registeredPlayerView (State.observe _ execution.native
    who))
  change supported.nodeCommand? who state.timeouts policy.proposals history view store node = some
    law
    at hselected
  unfold SealedShape.nodeCommand? at hselected
  split at hselected
  · contradiction
  · split at hselected
    next hready =>
      have hrequires : (G.messagePrerequisites node).all state.completed = true := by
        have h := (state.prerequisitesDone_discharge (G.sealedRule node)).symm.trans hready.2
        simpa only [Graph.sealedRule] using h
      split at hselected
      next owner guard hsem =>
        split at hselected
        next howner =>
          subst owner
          rw [← Option.some.inj hselected] at hsubmit
          obtain ⟨hpayload, _⟩ := supported.commitCommand_submission who policy.proposals node
            guard hsem
            history store payload hsubmit
          subst payload
          refine .commitment who serial node.val (who, node.val) (G.messagePrerequisites node)
            ?_ rfl hrequires
          change supported.compile.rules[node.val]? = _
          rw [supported.compile_rule, G.sealedRule_commit_eq node who guard hsem]
        next => contradiction
      next source hsem =>
        let discharged := supported.compile.discharge state.timeouts
        change (discharged.openingHandle? view.application who node.val).map _ = some law
          at hselected
        cases hhandle : discharged.openingHandle? view.application who node.val with
        | none => simp only [hhandle, Option.map_none] at hselected; contradiction
        | some handle =>
            obtain ⟨sourceSlot, rfl⟩ := SealedProgram.openingHandle?_eq_some_owner
              discharged view.application who node.val handle hhandle
            obtain ⟨requires, hrule, _, _, haccepted⟩ := SealedProgram.openingHandle?_sound
              discharged view.application who node.val sourceSlot hhandle
            have hkind : (G.sealedRule node).kind = .reveal who sourceSlot := by
              change (supported.compile.discharge _).rules[node.val]? = _ at hrule
              simp only [SealedProgram.discharge, List.getElem?_map, supported.compile_rule,
                Option.map_some, Option.some.injEq] at hrule
              exact congrArg SealedRule.kind hrule
            have hbase : runtime.program.rules[node.val]? =
                some ⟨.reveal who sourceSlot, G.messagePrerequisites node⟩ := by
              change supported.compile.rules[node.val]? = _
              rw [supported.compile_rule]
              apply congrArg some
              calc
                G.sealedRule node = ⟨(G.sealedRule node).kind, (G.sealedRule node).requires⟩ := rfl
                _ = _ := by rw [hkind]; rfl
            rw [hhandle] at hselected
            simp only [Option.map_some] at hselected
            split at hselected
            · rw [← Option.some.inj hselected, FinDist.mem_support_pure] at hsubmit
              cases hsubmit
            next value hcache =>
              rw [← Option.some.inj hselected, FinDist.mem_support_pure] at hsubmit
              have hpayload := MessageInterface.PlayerCommand.submit.inj hsubmit
              subst payload
              refine .opening who serial node.val sourceSlot (who, sourceSlot) value
                (G.messagePrerequisites node) hbase rfl haccepted ?_ hrequires
              erw [runtime.eventHistory_cache, runtime.registeredPlayerHistory_cache] at hcache
              erw [hmemory.memory sourceSlot, hcache]
              rfl
      next dist hsem => exact (supported.noSamples node dist hsem).elim
    next => contradiction

/-- Every actual generated submission has the candidate validator's stable
admission data. This is derived from the policy and its native history, including
after defaults and under arbitrary opponent and environment policies. -/
theorem candidatePolicy_submission_ready (who : Player) (policy : CommitPolicy G who)
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment : (supported.resolvingRuntime nullValue
      window).candidateApplication.EnvironmentPolicy)
    (hplayer : players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who policy))
    (schedule : List (@Invocation Player))
    (execution : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hactual : execution ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies players
        environment schedule (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈ (players who (execution.principalHistory who)
      (State.observe _ execution.native who)).support) (serial : Nat) :
    ∃ node : Fin G.nodeCount,
      SealedResolution.CandidateSubmissionReady (supported.resolvingRuntime nullValue window)
        execution.native.application ⟨(who, serial), payload⟩ node.val := by
  let runtime := supported.resolvingRuntime nullValue window
  have hmemory := supported.candidatePolicy_memory nullValue window who policy.proposals players
    environment
    hplayer schedule execution hactual
  rw [hplayer] at hsubmit
  change .submit payload ∈ (supported.resolvingPolicy nullValue window who policy
    (runtime.registeredPlayerHistory (execution.principalHistory who))
    (runtime.registeredPlayerView (State.observe _ execution.native who))).support at hsubmit
  unfold SealedShape.resolvingPolicy SealedShape.resolvingProposalPolicy at hsubmit
  dsimp only at hsubmit
  unfold Option.getD at hsubmit
  split at hsubmit
  next law hselected =>
    obtain ⟨node, _, hnode⟩ := List.exists_of_findSome?_eq_some hselected
    exact ⟨node, supported.nodeCommand_candidate_ready nullValue window who policy execution
      hmemory node _ law hnode payload hsubmit serial⟩
  next => simp only [FinDist.mem_support_pure] at hsubmit; cases hsubmit

/-- Every generated preparation selects a fresh candidate slot. Own-command
memory establishes freshness even after unrelated candidates have been accepted
or timed out. -/
theorem candidatePolicy_registration_fresh
    (who : Player) (policy : CommitPolicy G who)
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicy)
    (hplayer : players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who policy))
    (schedule : List (@Invocation Player))
    (execution : (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hactual : execution ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies players
        environment schedule (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (slot : Nat) (value : L.Val ty)
    (hcommand : .privateCommand ⟨(slot, value)⟩ ∈ (players who (execution.principalHistory who)
      (State.observe _ execution.native who)).support) :
    execution.native.application.service.lookup (who, slot) = .fresh := by
  let runtime := supported.resolvingRuntime nullValue window
  have hmemory := supported.candidatePolicy_memory nullValue window who policy.proposals players
    environment
    hplayer schedule execution hactual
  rw [hplayer] at hcommand
  change .privateCommand ⟨(slot, value)⟩ ∈ (supported.resolvingPolicy nullValue window who policy
    (runtime.registeredPlayerHistory (execution.principalHistory who))
    (runtime.registeredPlayerView (State.observe _ execution.native who))).support at hcommand
  unfold SealedShape.resolvingPolicy SealedShape.resolvingProposalPolicy at hcommand
  dsimp only at hcommand
  obtain ⟨node, guard, hsem, reads, hslot, hcache, _⟩ := supported.selected_registration_kernel
    who execution.native.application.visible.timeouts policy.proposals _ _ _ slot value hcommand
  rw [hslot]
  erw [runtime.eventHistory_cache, runtime.registeredPlayerHistory_cache] at hcache
  erw [hmemory.memory node.val, hcache]
  rfl

/-- While an owner follows its generated policy, it cannot prepare an occupied
candidate again. Opponent and environment policies are unrestricted. This
one-preparation charge does not depend on a fixed selected graph node. -/
theorem candidatePolicy_no_reregistration
    (who : Player) (policy : CommitPolicy G who)
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment :
      (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicy)
    (hplayer : players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who policy))
    (before after : List (@Invocation Player))
    (execution next :
      (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hactual : execution ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies players
        environment before (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (hnext : next ∈ ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
      players environment after execution).support)
    (slot : Nat) (hfixed : execution.native.application.service.lookup (who, slot) ≠ .fresh)
    (value : L.Val ty) :
    .privateCommand ⟨(slot, value)⟩ ∉ (players who (next.principalHistory who)
      (State.observe _ next.native who)).support := by
  let runtime := supported.resolvingRuntime nullValue window
  have hprefix : next ∈ (runtime.candidateApplication.runPolicies players environment
      (before ++ after)
      (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))).support := by
    simp only [runtime.candidateApplication.runPolicies_append, FinDist.support_bind,
      Set.mem_iUnion]
    exact ⟨execution, hactual, hnext⟩
  have hretained := runtime.runPolicies_candidate_lookup_of_not_fresh
    runtime.candidateHandle_sound players environment after
    execution next (who, slot) hfixed hnext
  intro hcommand
  exact hfixed (hretained.symm.trans (supported.candidatePolicy_registration_fresh nullValue
    window who policy players environment hplayer (before ++ after) next hprefix
    slot value hcommand))

/-- Servicing an actual generated packet completes its site. Opponents and the
environment remain arbitrary throughout the suffix; the only service premise
is that the pending pool has drained by its end. -/
theorem candidatePolicy_submission_completed_of_drained
    (who : Player) (policy : CommitPolicy G who)
    (players : Player →
      (supported.resolvingRuntime nullValue window).candidateApplication.PlayerPolicy)
    (environment : (supported.resolvingRuntime nullValue
      window).candidateApplication.EnvironmentPolicy)
    (hplayer : players who = (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
      (supported.resolvingPolicy nullValue window who policy))
    (before after : List (@Invocation Player))
    (execution submitted next :
      (supported.resolvingRuntime nullValue window).candidateApplication.PolicyExecution)
    (hactual : execution ∈
      ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies players
        environment before (PolicyExecution.initial _ (State.initial _
          (supported.resolvingRuntime nullValue window).candidateInitial))).support)
    (payload : SealedProgram.Payload Player (L.Val ty))
    (hsubmit : .submit payload ∈ (players who (execution.principalHistory who)
      (State.observe _ execution.native who)).support)
    (hstep : submitted ∈ ((supported.resolvingRuntime nullValue
      window).candidateApplication.playerStep
      who execution (.submit payload)).support)
    (hnext : next ∈ ((supported.resolvingRuntime nullValue window).candidateApplication.runPolicies
      players environment after submitted).support) (hdrained : next.native.pool.pending = []) :
    ∃ node : Fin G.nodeCount,
      payload.node? = some node.val ∧ next.native.application.visible.completed node.val = true
        := by
  let runtime := supported.resolvingRuntime nullValue window
  obtain ⟨node, hready⟩ := supported.candidatePolicy_submission_ready nullValue window who policy
    players environment hplayer before execution hactual payload hsubmit
    (execution.native.pool.nextSerial who)
  have hnode : payload.node? = some node.val := by cases hready <;> rfl
  have hnative : submitted.native =
      { execution.native with pool := (execution.native.pool.submit who payload).2 } := by
    simp only [playerStep, advance, PlayerCommand.toAction, MessageApplication.step,
      FinDist.pure_bind, FinDist.mem_support_pure] at hstep
    subst submitted
    rfl
  have hready' : SealedResolution.CandidateSubmissionReady runtime submitted.native.application
      ⟨(who, execution.native.pool.nextSerial who), payload⟩ node.val := by
    rw [hnative]
    exact hready
  have hpending : (⟨(who, execution.native.pool.nextSerial who), payload⟩ :
      Message Player (SealedProgram.Payload Player (L.Val ty))) ∈ submitted.native.pool.pending
        := by
    rw [hnative]
    exact List.mem_append_right _ List.mem_cons_self
  rcases SealedResolution.runPolicies_candidate_pendingOrCompleted players environment after
      submitted next hpending hready' hnext with hcomplete | ⟨hretained, _⟩
  · exact ⟨node, hnode, hcomplete⟩
  · simp only [hdrained, List.not_mem_nil] at hretained

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidatePolicy_submission_completed_of_drained'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidatePolicy_submission_completed_of_drained

/-- info: 'Vegas.EventGraph.SealedFragment.candidatePolicy_no_reregistration'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidatePolicy_no_reregistration
