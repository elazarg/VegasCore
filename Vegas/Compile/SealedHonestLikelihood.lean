/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedHonestCylinder
import Interaction.SealedResolutionProvenance

/-! # All-player graph likelihood of assigned native replay

The graph restriction weight is a product of the original native preparation
probabilities. All graph profiles are permitted, including dependent choices
and reference cylinders having zero original probability.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
variable (environment :
  List (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentEntry →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentObservation →
  (supported.resolvingRuntime nullValue window).messageApplication.EnvironmentPolicyCommand)
variable (schedule : List (@Invocation Player))

/-- The original graph kernel's native probability of an occupied registration.
Unoccupied slots contribute one. Every player retains its original policy. -/
def assignedRegistrationFactor (reference : Fin G.nodeCount → L.Val ty)
    (profile : CommitPolicyProfile G) (who : Player) (slot : Nat) : ℝ :=
  let runtime := supported.resolvingRuntime nullValue window
  let trace := supported.resolvingAssignedReplay nullValue window reference environment schedule
  let stop := fun execution : runtime.messageApplication.PolicyExecution =>
    !execution.native.application.visible.timeouts.isEmpty
  match (trace.prefixThrough stop).last.native.application.service.lookup (who, slot) with
  | none => 1
  | some value =>
      let selected := runtime.messageApplication.commandCheckpoint
        (supported.resolvingAssignedPlayers nullValue window reference) trace stop who
          (.privateCommand ⟨(slot, value)⟩)
      (supported.resolvingPolicy nullValue window who (profile who)
        (selected.principalHistory who)
        (State.observe runtime.messageApplication selected.native who)).prob
          (.privateCommand ⟨(slot, value)⟩)

variable [Fintype Player] (hguards : GuardLive G)

/-- Every normalized graph realization has the same all-player likelihood,
with one native probability factor per actual graph commitment. -/
theorem assignedRestriction_weight_eq_product
    (reference : Fin G.nodeCount → L.Val ty) (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let stopped := (supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough
        (fun execution : runtime.messageApplication.PolicyExecution =>
          !execution.native.application.visible.timeouts.isEmpty)
    let restriction := supported.recordedChoiceRestriction (fun _ => true)
      stopped.last.native.application.service.lookup
    ∀ cfg ∈ (runPolicyNodes supported.graphWF hguards (restriction.apply profile)
      ⟨Config.initial G, .initial⟩ G.nodeOrder).support,
      restriction.weight profile G.nodeOrder cfg.1 =
        (G.nodeOrder.map fun node => match (G.nodeRow node).sem with
          | .commit who _ => supported.assignedRegistrationFactor nullValue window
              environment schedule reference profile who node.val
          | _ => 1).prod := by
  classical
  intro runtime stopped restriction cfg hcfg
  have hterminal := runPolicyNodes_terminal supported.graphWF hguards (restriction.apply profile)
    ⟨Config.initial G, .initial⟩ G.nodeOrder G.nodeOrder_readyOrder
    (fun node => Or.inr (by simp)) cfg hcfg
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
      simp only [restriction, recordedChoiceRestriction, ↓reduceIte]
      cases hlookup : stopped.last.native.application.service.lookup (who, node.val) with
      | none =>
          simp only [Option.map_none, assignedRegistrationFactor]
          erw [hlookup]
      | some value =>
          simp only [Option.map_some]
          let trace := supported.resolvingAssignedReplay nullValue window reference
            environment schedule
          let stop := fun execution : runtime.messageApplication.PolicyExecution =>
            !execution.native.application.visible.timeouts.isEmpty
          let players := supported.resolvingAssignedPlayers nullValue window reference
          let release := fun execution : runtime.messageApplication.PolicyExecution =>
            !stop execution && decide (.privateCommand ⟨(node.val, value)⟩ ∈
              (players who (execution.principalHistory who)
                (State.observe runtime.messageApplication execution.native who)).support)
          have htrace : trace ∈ (runtime.messageApplication.tracePolicies players
              (fun history view => FinDist.pure (environment history view)) schedule
              (PolicyExecution.initial _ (State.initial _ runtime.initial))).support := by
            rw [supported.resolvingAssignedReplay_law, FinDist.mem_support_pure]
          have hselected := runtime.registrationCheckpoint_selected players
            (fun history view => FinDist.pure (environment history view)) schedule _ trace htrace
            stop who node.val value (by intro h; cases h) hlookup
          have hclear :
              (stopped.firstRelease release).native.application.visible.timeouts = [] := by
            simpa only [MessageApplication.commandCheckpoint, stop, Bool.not_eq_eq_eq_not,
              Bool.not_false, List.isEmpty_iff] using hselected.1
          obtain ⟨actual, test, htest, inputs, hslot, _, hinputs, hkernel⟩ :=
            supported.restrictedGraphRun_assigned_registration_kernel hguards nullValue window
              environment schedule reference profile release cfg hcfg hclear who node.val value
              hselected.2 (profile who)
          have hnode : actual = node := Fin.ext hslot.symm
          subst actual
          have hguard : test = guard := (NodeSem.commit.inj (htest.symm.trans hsem)).2
          subst test
          have heq : inputs = reads := Option.some.inj (hinputs.symm.trans hreads)
          subst inputs
          simp only [assignedRegistrationFactor]
          erw [hlookup]
          change _ = (supported.resolvingPolicy nullValue window who (profile who)
            ((stopped.firstRelease release).principalHistory who)
            (State.observe runtime.messageApplication
              (stopped.firstRelease release).native who)).prob _
          rw [hkernel]
          let encode := fun choice : {v : L.Val guard.ty // guard.eval v reads = true} =>
            (.privateCommand ⟨(node.val, cast
              (congrArg L.Val (supported.commitType node who guard hsem)) choice.1)⟩ :
                runtime.messageApplication.PlayerCommand)
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

/-- The original graph probability of an assigned native prefix is the product
of its native preparation factors. The graph law has no policy replacement. -/
theorem graphRun_assignedReplay_prob_eq_product (fallback : L.Val ty)
    (reference : Fin G.nodeCount → L.Val ty) (profile : CommitPolicyProfile G) :
    let runtime := supported.resolvingRuntime nullValue window
    let stop := fun execution : runtime.messageApplication.PolicyExecution =>
      !execution.native.application.visible.timeouts.isEmpty
    let stopped := (supported.resolvingAssignedReplay nullValue window reference
      environment schedule).prefixThrough stop
    ((runPolicyNodes supported.graphWF hguards profile ⟨Config.initial G, .initial⟩
      G.nodeOrder).map fun cfg =>
        (supported.resolvingAssignedReplay nullValue window (cfg.1.nodeValues fallback)
          environment schedule).prefixThrough stop).prob stopped =
      (G.nodeOrder.map fun node => match (G.nodeRow node).sem with
        | .commit who _ => supported.assignedRegistrationFactor nullValue window
            environment schedule reference profile who node.val
        | _ => 1).prod := by
  intro runtime stop stopped
  rw [supported.assignedReplay_graph_likelihood]
  exact (FinDist.expect_congr (supported.assignedRestriction_weight_eq_product nullValue window
    environment schedule hguards reference profile)).trans (FinDist.expect_const _ _)

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.graphRun_assignedReplay_prob_eq_product'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.graphRun_assignedReplay_prob_eq_product
