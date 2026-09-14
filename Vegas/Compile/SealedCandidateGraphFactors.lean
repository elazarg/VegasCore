/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateGraphKernel
import Interaction.SealedCandidateProvenance

/-! # Graph replay likelihood as native preparation probabilities

The graph restriction weight is constant on the normalized reference law.
Its factors are the unchanged graph opponents' native preparation probabilities
at actual replay checkpoints. This evaluates the graph-side replay mass; equality
with the native runner's mass additionally requires invocation counting.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty)
variable (nullValue : L.Val ty) (window : Nat) (focal : Player)
variable (deviator :
  List (supported.resolvingRuntime nullValue window).candidateApplication.PlayerEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.View →
  (supported.resolvingRuntime nullValue window).candidateApplication.PlayerCommand)
variable (environment :
  List (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).candidateApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))

/-- Original native probability of a recorded honest preparation. Focal,
fresh, and unopenable slots contribute one. -/
def candidateReplayRegistrationFactor (reference : Fin G.nodeCount → L.Val ty)
    (profile : CommitPolicyProfile G) (who : Player) (slot : Nat) : ℝ :=
  let runtime := supported.resolvingRuntime nullValue window
  let trace := supported.candidateReplay nullValue window reference focal
    deviator environment schedule
  let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  if who = focal then 1 else
    match ((trace.prefixThrough stop).last.native.application.service.lookup (who, slot)).opening?
        with
    | none => 1
    | some value =>
        let selected := runtime.candidateApplication.commandCheckpoint
          (supported.candidateValuePlayers nullValue window reference focal
            (fun history view => FinDist.pure (deviator history view))) trace stop who
              (.privateCommand ⟨(slot, value)⟩)
        (runtime.candidatePlayerPolicy
          (supported.resolvingPolicy nullValue window who (profile who))
          (selected.principalHistory who)
          (State.observe runtime.candidateApplication selected.native who)).prob
            (.privateCommand ⟨(slot, value)⟩)

variable [Fintype Player]
variable (hinfo : G.PublicPrefixReadable) (hguards : GuardLive G) (fallback : L.Val ty)

/-- Each normalized graph realization has the same likelihood: a finite
product of fixed native preparation probabilities at actual graph sites. -/
theorem restrictedCandidateGraphRun_weight_eq_product
    (reference : Fin G.nodeCount → L.Val ty) (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let stopped := (supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough (fun execution :
        runtime.candidateApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    let restriction := supported.recordedChoiceRestriction (fun who => decide (who ≠ focal))
      (fun handle => (stopped.last.native.application.service.lookup handle).opening?)
    let original := Profile.update (sig := ⟨CommitPolicy G, ReachableConfig G⟩) profile focal
      (supported.extractedCandidateCommitPolicy hinfo nullValue window focal deviator
        environment schedule fallback)
    ∀ cfg ∈ (supported.candidateGraphRun hinfo hguards nullValue window focal deviator
      environment schedule fallback (restriction.apply profile)).support,
      restriction.weight original G.nodeOrder cfg.1 =
        (G.nodeOrder.map fun node => match (G.nodeRow node).sem with
          | .commit who _ => supported.candidateReplayRegistrationFactor nullValue window focal
              deviator environment schedule reference profile who node.val
          | _ => 1).prod := by
  classical
  intro runtime stopped restriction original cfg hcfg
  have hterminal := supported.candidateGraphRun_terminal hinfo hguards nullValue window focal
    deviator environment schedule fallback _ cfg hcfg
  have hchoices := runPolicyNodes_support_commitValues supported.graphWF hguards _
    ⟨Config.initial G, .initial⟩ (CommitValuesSupported.initial _) G.nodeOrder cfg hcfg
  unfold CommitRestriction.weight
  congr 1
  apply List.map_congr_left
  intro node _hnode
  cases hsem : (G.nodeRow node).sem with
  | commit who guard =>
      obtain ⟨reads, hreads, _, _, _⟩ := hchoices node (hterminal node) who guard hsem
      rw [CommitRestriction.factor_commit _ _ _ node who guard hsem reads hreads]
      by_cases hwho : who = focal
      · simp only [restriction, recordedChoiceRestriction, hwho, ne_eq, not_true_eq_false,
          decide_false, Bool.false_eq_true, ↓reduceIte, candidateReplayRegistrationFactor]
      · simp only [restriction, recordedChoiceRestriction, hwho, ne_eq, not_false_eq_true,
          decide_true, ↓reduceIte, original, Profile.update_of_ne _ _ hwho]
        cases hlookup : (stopped.last.native.application.service.lookup (who, node.val)).opening?
            with
        | none =>
            simp only [Option.map_none, candidateReplayRegistrationFactor, if_neg hwho]
            erw [hlookup]
        | some value =>
            simp only [Option.map_some]
            let trace := supported.candidateReplay nullValue window reference focal
              deviator environment schedule
            let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
              !execution.native.application.visible.timeouts.isEmpty
            let players := supported.candidateValuePlayers nullValue window reference focal
              (fun history view => FinDist.pure (deviator history view))
            let release := fun execution : runtime.candidateApplication.PolicyExecution =>
              !stop execution && decide (.privateCommand ⟨(node.val, value)⟩ ∈
                (players who (execution.principalHistory who)
                  (State.observe runtime.candidateApplication execution.native who)).support)
            have htrace : trace ∈ (runtime.candidateApplication.tracePolicies players
                (fun history view => FinDist.pure (environment history view)) schedule
                (PolicyExecution.initial _
                  (State.initial _ runtime.candidateInitial))).support := by
              rw [supported.candidateReplay_law, FinDist.mem_support_pure]
            have hselected := runtime.candidateRegistrationCheckpoint_selected players
              (fun history view => FinDist.pure (environment history view)) schedule _ trace htrace
              stop who node.val value (by intro h; cases h)
              (CommitmentCandidate.opening?_eq_some_iff _ _ |>.mp hlookup)
            have hclear :
                (stopped.firstRelease release).native.application.visible.timeouts = [] := by
              simpa only [MessageApplication.commandCheckpoint, stop, Bool.not_eq_eq_eq_not,
                Bool.not_false, List.isEmpty_iff] using hselected.1
            obtain ⟨actual, test, htest, inputs, hslot, _, hinputs, hkernel⟩ :=
              supported.restrictedCandidateGraphRun_registration_kernel hinfo hguards nullValue
                window focal deviator environment schedule fallback reference profile release cfg
                hcfg hclear who hwho node.val value hselected.2 (profile who)
            have hnode : actual = node := Fin.ext hslot.symm
            subst actual
            have hguard : test = guard := (NodeSem.commit.inj (htest.symm.trans hsem)).2
            subst test
            have heq : inputs = reads := Option.some.inj (hinputs.symm.trans hreads)
            subst inputs
            simp only [candidateReplayRegistrationFactor, if_neg hwho]
            erw [hlookup]
            change _ = (runtime.candidatePlayerPolicy
              (supported.resolvingPolicy nullValue window who (profile who))
              ((stopped.firstRelease release).principalHistory who)
              (State.observe runtime.candidateApplication
                (stopped.firstRelease release).native who)).prob _
            rw [hkernel]
            let encode := fun choice : {v : L.Val guard.ty // guard.eval v reads = true} =>
              (.privateCommand ⟨(node.val, cast
                (congrArg L.Val (supported.commitType node who guard hsem)) choice.1)⟩ :
                  runtime.candidateApplication.PlayerCommand)
            have hinj : Function.Injective encode := by
              intro left right heq
              have hvalue := congrArg (fun request => request.down.2)
                (MessageInterface.PlayerCommand.privateCommand.inj heq)
              apply Subtype.ext
              simpa only [cast_cast, cast_eq] using
                congrArg (cast
                  (congrArg L.Val (supported.commitType node who guard hsem).symm)) hvalue
            have hprob := FinDist.prob_map_of_injective encode hinj
              (profile who node guard hsem reads)
              ⟨cast (congrArg L.Val (supported.commitType node who guard hsem).symm) value,
                supported.commitGuard node who guard hsem _ reads⟩
            simpa only [encode, cast_cast, cast_eq] using hprob.symm
  | sample dist | reveal source =>
      exact CommitRestriction.factor_internal _ _ _ node (by simp [hsem, NodeSem.isInternal])

/-- The complete graph-side replay prefix mass is the product of native
checkpoint probabilities. No source program or source policy occurs. -/
theorem candidateGraphRun_replay_prob_eq_product
    (reference : Fin G.nodeCount → L.Val ty) (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let stop := fun execution : runtime.candidateApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (supported.candidateReplay nullValue window reference focal
      deviator environment schedule).prefixThrough stop
    ((supported.candidateGraphRun hinfo hguards nullValue window focal deviator environment
      schedule fallback profile).map fun cfg =>
        (supported.candidateReplay nullValue window (cfg.1.nodeValues fallback) focal
          deviator environment schedule).prefixThrough stop).prob stopped =
      (G.nodeOrder.map fun node => match (G.nodeRow node).sem with
        | .commit who _ => supported.candidateReplayRegistrationFactor nullValue window focal
            deviator environment schedule reference profile who node.val
        | _ => 1).prod := by
  intro runtime stop stopped
  change ((runPolicyNodes supported.graphWF hguards _ _ _).map _).prob _ = _
  rw [supported.candidateReplay_graph_likelihood]
  rw [recordedChoiceRestriction_apply_update _ _ focal (by simp)]
  exact (FinDist.expect_congr (supported.restrictedCandidateGraphRun_weight_eq_product nullValue
    window focal deviator environment schedule hinfo hguards fallback reference profile)).trans
      (FinDist.expect_const _ _)

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.candidateGraphRun_replay_prob_eq_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.candidateGraphRun_replay_prob_eq_product
