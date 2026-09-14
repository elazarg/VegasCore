/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedHonestNative
import Vegas.Compile.SealedHonestCompletion
import Vegas.Compile.SealedPolicyDeadline
import Vegas.Compile.SealedTermination
import Interaction.SealedResolutionCompletion

/-! # Original graph outcomes in the public pending-message driver

Periodic inclusion capacity and a sufficient timeout window ensure that the
all-compiled execution completes without defaults. The graph/native
probability law then supplies an exact coupling with the original graph
profile. The native marginal is the actual early-stopping round driver,
not a separate execution or a postulated graph game. The wire policy may be
randomized and may adapt to its full pending-message observation.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication
open GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Honest graph outcome preservation for the sealed pending-message
backend. Graph kernels are unchanged. All supported pairs have normal native
completion and decode to the retained graph realization. The assumptions
concern roster coverage, real inclusion capacity, the timeout window, and a
sufficient whole-period budget; acceptance and successful completion are
conclusions. No unilateral utility or equilibrium claim is made here. -/
theorem exists_honest_round_graph_coupling
    (supported : SealedFragment G ty) (hguards : GuardLive G) (nullValue : L.Val ty) (window : Nat)
    (principals : List Player) (serviceSlots : Nat)
    (profile : CommitPolicyProfile G)
    (wire : (supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (reserved : Nat → Bool)
    (hservice :
      (supported.resolvingRuntime nullValue window).messageApplication.InclusionService
        (fun turn => reserved turn = true)
        ((supported.resolvingRuntime nullValue
          window).messageApplication.wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1))
        serviceSlots).countP reserved)
    (hroster : ∀ who, who ∈ principals)
    (hwindow : G.nodeCount * (period + 1) + 2 ≤ window)
    (total : Nat) (hperiods : period ∣ total)
    (hbound : G.nodeCount * (window + 1) ≤ total) :
    let runtime := supported.resolvingRuntime nullValue window
    ∃ coupling : FinDist (ReachableConfig G ×
        runtime.messageApplication.PolicyExecution),
      coupling.map Prod.fst =
        runPolicyNodes supported.graphWF hguards profile ⟨Config.initial G, .initial⟩ G.nodeOrder ∧
      coupling.map Prod.snd =
        runtime.roundDriver.runRounds principals serviceSlots
          (fun who => supported.resolvingPolicy nullValue window who (profile who))
          wire total (PolicyExecution.initial _ (State.initial _ runtime.initial)) ∧
      ∀ cfg next, (cfg, next) ∈ coupling.support →
        runtime.complete next.native.application.visible = true ∧
        next.native.application.visible.timeouts = [] ∧
        G.decodeSealedFrom ty next.native.application.service
          (Config.initial _) next.native.application.visible.events = some cfg.1 := by
  intro runtime
  let players := fun who => supported.resolvingPolicy nullValue window who (profile who)
  let environment := runtime.roundDriver.environmentPolicy serviceSlots wire
  let schedule := MessageApplication.roundSchedule principals serviceSlots total
  let initial := PolicyExecution.initial runtime.messageApplication
    (State.initial runtime.messageApplication runtime.initial)
  let width := (MessageApplication.roundInvocations principals serviceSlots).length
  let release := fun execution : runtime.messageApplication.PolicyExecution =>
    runtime.complete execution.native.application.visible
  let readout := PolicyTrace.firstReleaseEvery width release total
  have hdriver := runtime.roundDriver.runRounds_eq_tracePolicies principals serviceSlots
    players wire
    total initial (by rfl)
  have hcomplete (next : runtime.messageApplication.PolicyExecution)
      (hnext : next ∈
        (runtime.roundDriver.runRounds
          principals serviceSlots players wire total initial).support) :
      runtime.complete next.native.application.visible = true :=
    supported.resolvingRuntime_runRounds_complete nullValue window principals
      serviceSlots players wire total hbound next hnext
  have hclear (next : runtime.messageApplication.PolicyExecution)
      (hnext : next ∈
        (runtime.roundDriver.runRounds
          principals serviceSlots players wire total initial).support) :
      next.native.application.visible.timeouts = [] :=
    supported.runRounds_timeouts_eq_nil nullValue window principals serviceSlots
      profile wire reserved hservice period hperiod hcapacity hroster hwindow total
      hperiods next hnext
  have htraceClear (trace : runtime.messageApplication.PolicyTrace)
      (htrace : trace ∈
        (runtime.messageApplication.tracePolicies players environment schedule initial).support) :
      trace.last.native.application.visible.timeouts = [] := by
    have hselected : readout trace ∈
        (runtime.roundDriver.runRounds
          principals serviceSlots players wire total initial).support := by
      rw [hdriver, FinDist.support_map]
      exact ⟨trace, htrace, rfl⟩
    obtain ⟨front, suffix, _, _, hsuffix⟩ :=
      runtime.messageApplication.tracePolicies_firstReleaseEvery_split players environment
        width total release (by simp [width, MessageApplication.roundInvocations]) schedule initial
        trace (by simp [schedule, width, MessageApplication.roundSchedule_length]) htrace
    exact (runtime.runPolicies_complete_clear
      (fun (service : IdealCommitments Player Nat (L.Val ty)) owner slot value =>
        (service.sealValue owner slot value).state) runtime.handle
      runtime.handle_eq_none_of_complete_clear
      players environment suffix (readout trace) trace.last
      (hcomplete _ hselected) (hclear _ hselected) hsuffix).2.1
  obtain ⟨responses, hresponses⟩ := supported.exists_honest_replay_mixture hguards nullValue window
    schedule nullValue profile environment htraceClear
  let coupling : FinDist (ReachableConfig G ×
      runtime.messageApplication.PolicyExecution) :=
    responses.bind fun response => (runPolicyNodes supported.graphWF hguards profile
      ⟨Config.initial G, .initial⟩ G.nodeOrder).map fun cfg =>
      (cfg, readout (supported.resolvingAssignedReplay nullValue window
        (cfg.1.nodeValues nullValue) response schedule))
  have hgraph : coupling.map Prod.fst = runPolicyNodes supported.graphWF hguards profile
      ⟨Config.initial G, .initial⟩ G.nodeOrder := by
    simp only [coupling, FinDist.map_bind, FinDist.map_comp, Function.comp_def,
      FinDist.bind_const]
    exact FinDist.map_id _
  have hnative : coupling.map Prod.snd =
      runtime.roundDriver.runRounds principals serviceSlots players wire total initial := by
    rw [hdriver]
    have hmapped := congrArg (FinDist.map readout) hresponses
    simpa only [coupling, FinDist.map_bind, FinDist.map_comp, Function.comp_def] using hmapped
  refine ⟨coupling, hgraph, hnative, ?_⟩
  intro cfg next hpair
  have hnext : next ∈
      (runtime.roundDriver.runRounds
        principals serviceSlots players wire total initial).support := by
    rw [← hnative, FinDist.support_map]
    exact ⟨(cfg, next), hpair, rfl⟩
  refine ⟨hcomplete next hnext, hclear next hnext, ?_⟩
  simp only [coupling, FinDist.support_bind, Set.mem_iUnion,
    FinDist.support_map, Set.mem_image, Prod.mk.injEq] at hpair
  obtain ⟨response, _, actual, hactual, hcfg, hreadout⟩ := hpair
  subst actual
  exact supported.resolvingAssignedReplay_firstCompleteEvery_decode
    nullValue window principals serviceSlots total cfg
    (runPolicyNodes_terminal supported.graphWF hguards profile ⟨Config.initial G, .initial⟩
      G.nodeOrder G.nodeOrder_readyOrder (fun node => Or.inr (by simp)) cfg hactual)
    nullValue response next
    hreadout.symm (hcomplete next hnext) (hclear next hnext)

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.exists_honest_round_graph_coupling' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.exists_honest_round_graph_coupling
