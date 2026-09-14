/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateValues
import Vegas.Compile.SealedPolicyProgress
import Vegas.Compile.SealedResolutionAdmission

/-! # Ready-player progress under arbitrary candidate traffic

Public event provenance, authenticated own acceptance, and the generated
owner's private cache establish the shared graph-selector progress theorem.
The argument remains valid after defaults and with arbitrary other players.
No graph realization, source policy, or timeout-free prefix is assumed.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)

/-- The generated owner's accepted graph commitments have canonical handles
and cached values, even when other owners submit unopenable commitments. -/
theorem candidatePolicy_ownCommitCache
    (who : Player) (policy : CommitPolicy G who)
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
          (supported.resolvingRuntime nullValue window).candidateInitial))).support) :
    supported.OwnCommitCache who execution.native.application.visible.events
      ((supported.resolvingRuntime nullValue window).eventHistory
        ((supported.resolvingRuntime nullValue window).registeredPlayerHistory
          (execution.principalHistory who))) := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial _ runtime.candidateInitial)
  have hmemory := supported.candidatePolicy_memory nullValue window who policy players environment
    hplayer schedule execution hactual
  have hpublic := runtime.runPolicies_candidate_publicEvents players environment schedule initial
    execution (SealedResolution.EventInvariant.initial (runtime := runtime)).publicEvents hactual
  have hauth := runtime.runPolicies_candidate_acceptance players environment schedule initial
    execution SealedResolution.CandidateAcceptanceInvariant.initial hactual
  have hfixed := runtime.runPolicies_candidate_accepted_not_fresh players environment schedule
    initial execution (by
      intro node handle hmem
      have : SealedProgram.Event.accepted node handle ∈
          ([] : List (SealedProgram.Event Player (L.Val ty))) :=
        (runtime.refresh_accepted_iff false {} node handle).mp hmem
      contradiction) hactual
  intro node guard hsem hdone
  have hrule : runtime.program.rules[node.val]? =
      some ⟨.commit who, G.messagePrerequisites node⟩ := by
    change supported.compile.rules[node.val]? = _
    rw [supported.compile_rule, G.sealedRule_commit_eq node who guard hsem]
  have hsome := (hpublic.done_eq_accepted_isSome runtime node.val who
    (G.messagePrerequisites node) hrule).symm.trans hdone
  obtain ⟨handle, hread⟩ := Option.isSome_iff_exists.mp hsome
  have hmem := SealedProgram.accepted_mem_of_accepted?_eq_some hread
  obtain ⟨_, requires, hrule'⟩ := hauth node.val handle hmem
  have howner : handle.1 = who := by
    rw [hrule] at hrule'
    exact (SealedRuleKind.commit.inj (congrArg SealedRule.kind
      (Option.some.inj hrule'))).symm
  have hcanonical := supported.candidatePolicy_accepted_slot nullValue window who policy
    players environment hplayer schedule execution hactual node.val handle hmem howner
  subst handle
  have hslot := hmemory.memory node.val
  have hnonfresh := hfixed node.val (who, node.val) hmem
  cases hcache : (runtime.program.registrationEncoding node.val).cachedValue
      runtime.candidateApplication (execution.principalHistory who) with
  | none =>
      rw [hcache] at hslot
      exact (hnonfresh hslot).elim
  | some value =>
      refine ⟨value, hread, ?_⟩
      erw [runtime.eventHistory_cache, runtime.registeredPlayerHistory_cache]
      exact hcache

/-- At every actual ready-player poll, the generated candidate policy
prepares a fresh value or submits a commitment/opening at an unfinished ready
site no later than the target. This includes execution after defaults. -/
theorem candidatePolicy_progress_of_ready
    (who : Player) (policy : CommitPolicy G who)
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
    (target : Fin G.nodeCount)
    (hnotDone : execution.native.application.visible.completed target.val = false)
    (hrequires : (G.messagePrerequisites target).all
      execution.native.application.visible.completed = true)
    (howned :
      (∃ guard, (G.nodeRow target).sem = .commit who guard) ∨
      ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow target).sem = .reveal (G.nodeTarget producer) ∧
        (G.nodeRow producer).sem = .commit who guard) :
    ∀ command ∈ (players who (execution.principalHistory who)
      (State.observe _ execution.native who)).support,
      ∃ selected : Fin G.nodeCount,
        selected.val ≤ target.val ∧
        execution.native.application.visible.completed selected.val = false ∧
        (G.messagePrerequisites selected).all
          execution.native.application.visible.completed = true ∧
        supported.ProgressCommand who
          ((supported.resolvingRuntime nullValue window).eventHistory
            ((supported.resolvingRuntime nullValue window).registeredPlayerHistory
              (execution.principalHistory who))) selected command := by
  let runtime := supported.resolvingRuntime nullValue window
  let initial := PolicyExecution.initial runtime.candidateApplication
    (State.initial _ runtime.candidateInitial)
  have hcache := supported.candidatePolicy_ownCommitCache nullValue window who policy players
    environment hplayer schedule execution hactual
  have hpublic := runtime.runPolicies_candidate_publicEvents players environment schedule initial
    execution (SealedResolution.EventInvariant.initial (runtime := runtime)).publicEvents hactual
  have hbackward : ∀ (node : Nat) (rule : SealedRule Player),
      runtime.program.rules[node]? = some rule →
      ∀ prior ∈ rule.requires, prior < node := by
    intro node rule hrule prior hprior
    exact supported.compile_rule_requires_lt hrule hprior
  have hsource : ∀ (node : Nat) (owner : Player) (source : Nat) (requires : List Nat),
      runtime.program.rules[node]? = some ⟨.reveal owner source, requires⟩ → source < node := by
    intro node owner source requires hrule
    exact supported.compile_reveal_source_lt hrule rfl
  have hclosed := runtime.runPolicies_resolutionClosed
    (fun (service : CommitmentCandidates Player Nat (L.Val ty)) owner slot value =>
      service.prepare owner slot value)
    runtime.candidateHandle runtime.candidateHandle_records hbackward hsource
    players environment schedule initial execution
    (runtime.refresh_resolutionClosed hbackward hsource false {}) hactual
  rw [hplayer]
  exact supported.resolvingPolicy_progress_of_ready nullValue window who policy
    (runtime.registeredPlayerHistory (execution.principalHistory who))
    (runtime.registeredPlayerView (State.observe _ execution.native who))
    hpublic hcache hclosed target hnotDone hrequires howned

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidatePolicy_progress_of_ready'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidatePolicy_progress_of_ready
