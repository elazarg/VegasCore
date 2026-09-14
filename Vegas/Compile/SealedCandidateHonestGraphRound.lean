/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateHost
import Vegas.Compile.SealedHonestGraphRound
import Vegas.Compile.SealedPublicOutcome

/-! # Honest graph outcomes in the candidate stopped-round driver

The graph/native honest coupling passes through the checked commitment-host
embedding. The result retains the original graph profile, proves native normal
completion from deadline-relative service, and agrees on every public field.
No source program or public-prefix readability premise is required.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Every graph profile has its original graph law and public outcome under
the candidate driver. Service ensures normal completion. Wire-policy retyping
is surjective and preserves observable inputs; no candidate deviations are
restricted by this all-compiled law. -/
theorem exists_honest_candidate_round_graph_coupling
    (supported : SealedFragment G ty) (hguards : GuardLive G)
    (nullValue : L.Val ty) (window : Nat) (principals : List Player) (serviceSlots : Nat)
    (profile : CommitPolicyProfile G)
    (wire : (supported.resolvingRuntime nullValue window).messageApplication.WirePolicy)
    (reserved : Nat → Bool)
    (hservice : (supported.resolvingRuntime nullValue window).messageApplication.InclusionService
      (fun turn => reserved turn = true)
      ((supported.resolvingRuntime nullValue window).messageApplication.wireEnvironment wire))
    (period : Nat) (hperiod : 0 < period)
    (hcapacity : ∀ block, period * principals.length ≤
      (List.range' (((block + 1) * period - 1) * (serviceSlots + 1)) serviceSlots).countP reserved)
    (hroster : ∀ who, who ∈ principals)
    (hwindow : G.nodeCount * (period + 1) + 2 ≤ window)
    (total : Nat) (hperiods : period ∣ total) (hbound : G.nodeCount * (window + 1) ≤ total) :
    let runtime := supported.resolvingRuntime nullValue window
    ∃ coupling : FinDist (ReachableConfig G × runtime.candidateApplication.PolicyExecution),
      coupling.map Prod.fst =
        runPolicyNodes supported.graphWF hguards profile ⟨Config.initial G, .initial⟩ G.nodeOrder ∧
      coupling.map Prod.snd = runtime.candidateRoundDriver.runRounds principals serviceSlots
        (fun who => runtime.candidatePlayerPolicy
          (supported.resolvingPolicy nullValue window who (profile who)))
        (runtime.candidateWirePolicy wire) total
        (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial)) ∧
      ∀ cfg next, (cfg, next) ∈ coupling.support →
        Terminal G cfg.1 ∧ runtime.complete next.native.application.visible = true ∧
        next.native.application.visible.timeouts = [] ∧
        ∀ ref : FieldRef L, G.fieldRefPublic ref →
          Store.getAs (G.publicSealedStore ty next.native.application.visible.events)
            ref.field ref.ty = Store.getAs cfg.1.store ref.field ref.ty := by
  intro runtime
  obtain ⟨joint, hgraph, hnative, hpairs⟩ :=
    supported.exists_honest_round_graph_coupling hguards nullValue window principals serviceSlots
      profile wire reserved hservice period hperiod hcapacity hroster hwindow total hperiods hbound
  let coupling := joint.map fun pair => (pair.1, runtime.candidateExecution pair.2)
  refine ⟨coupling, ?_, ?_, ?_⟩
  · simpa only [coupling, FinDist.map_comp, Function.comp_def] using hgraph
  · have hmapped := congrArg (FinDist.map runtime.candidateExecution) hnative
    simpa only [coupling, FinDist.map_comp, Function.comp_def] using
      hmapped.trans (supported.candidateRounds_law nullValue window principals serviceSlots
        profile wire total)
  · intro cfg next hpair
    simp only [coupling, FinDist.support_map, Set.mem_image] at hpair
    obtain ⟨⟨actual, execution⟩, hpair, heq⟩ := hpair
    have hcfg : actual = cfg := congrArg Prod.fst heq
    have hnext : runtime.candidateExecution execution = next := congrArg Prod.snd heq
    subst actual next
    obtain ⟨hcomplete, hclear, hdecode⟩ := hpairs cfg execution hpair
    have hrun : execution ∈ (runtime.roundDriver.runRounds principals serviceSlots
        (fun who => supported.resolvingPolicy nullValue window who (profile who)) wire total
        (PolicyExecution.initial _ (State.initial _ runtime.initial))).support := by
      rw [← hnative, FinDist.support_map]
      exact ⟨(cfg, execution), hpair, rfl⟩
    have hinvariant := runtime.runRounds_eventInvariant principals serviceSlots _ wire total _
      execution SealedResolution.EventInvariant.initial hrun
    have hcfgSupport : cfg ∈ (runPolicyNodes supported.graphWF hguards profile
        ⟨Config.initial G, .initial⟩ G.nodeOrder).support := by
      rw [← hgraph, FinDist.support_map]
      exact ⟨(cfg, execution), hpair, rfl⟩
    refine ⟨runPolicyNodes_terminal supported.graphWF hguards profile
      ⟨Config.initial G, .initial⟩ G.nodeOrder G.nodeOrder_readyOrder
      (fun node => Or.inr (by simp)) cfg hcfgSupport, hcomplete, hclear, ?_⟩
    exact supported.publicSealedStore_agrees nullValue window execution.native.application
      hinvariant cfg.1 hdecode

end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.exists_honest_candidate_round_graph_coupling'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.exists_honest_candidate_round_graph_coupling
