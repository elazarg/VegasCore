/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedCandidateGraphRounds
import Vegas.Compile.SealedCandidateHonestGraphRound
import Vegas.Compile.SealedCandidateDeadline
import Vegas.Compile.SealedGraphUtility
import Interaction.SealedCandidateSettlement
import Vegas.EventGraph.Strategic
import GameTheoryExtensions.Core.UtilitySimulation

/-! # Strategic preservation to the candidate-message round game

The target is the actual stopped candidate driver, with unrestricted native
player policies and an adaptive wire policy. Deadline-relative service protects
unchanged players. The deviation coupling preserves their graph kernels;
independent graph settlement and a uniform graph quitting bound supply the
utility comparison after timeout. No source-image or runtime incentive premise
occurs in this backend certificate.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.GameForm
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

/-- Operational parameters of the actual candidate driver. The budget ensures
completion even when every remaining site must resolve by default. -/
structure CandidateRoundModel (supported : SealedFragment G ty)
    (nullValue : L.Val ty) (window : Nat) where
  principals : List Player
  serviceSlots : Nat
  total : Nat
  wire : (supported.resolvingRuntime nullValue window).candidateApplication.WirePolicy
  budget : G.nodeCount * (window + 1) ≤ total

namespace CandidateRoundModel

variable {supported : SealedFragment G ty} {nullValue : L.Val ty} {window : Nat}

/-- The shared native interpreter and stopping rule, viewed as a game. -/
def game (model : CandidateRoundModel supported nullValue window) : GameForm Player where
  sig := MessageApplication.policySignature Player
    (supported.resolvingRuntime nullValue window).candidateApplication
  play players :=
    let runtime := supported.resolvingRuntime nullValue window
    runtime.candidateRoundDriver.runRounds model.principals model.serviceSlots players model.wire
      model.total (PolicyExecution.initial _ (State.initial _ runtime.candidateInitial))

def compileStrategy (model : CandidateRoundModel supported nullValue window)
    (who : Player) (policy : CommitPolicy G who) : model.game.sig.Strategy who :=
  (supported.resolvingRuntime nullValue window).candidatePlayerPolicy
    (supported.resolvingPolicy nullValue window who policy)

def compileProfile (model : CandidateRoundModel supported nullValue window)
    (profile : CommitPolicyProfile G) : Profile model.game.sig :=
  fun who => model.compileStrategy who (profile who)

def nativeUtility (model : CandidateRoundModel supported nullValue window)
    (utility : G.PublicUtility) (next : model.game.sig.Outcome) : Player → ℝ :=
  utility.eval (G.publicSealedStore ty next.native.application.visible.events)

/-- Reserved inclusion capacity at the actual timeout scale. Unreserved wire
actions may depend on the pending pool and all other environment observations. -/
structure Timely (model : CandidateRoundModel supported nullValue window) where
  reserved : Nat → Bool
  service : (supported.resolvingRuntime nullValue window).candidateApplication.InclusionService
    (fun turn => reserved turn = true)
    ((supported.resolvingRuntime nullValue window).candidateApplication.wireEnvironment model.wire)
  period : Nat
  positive : 0 < period
  capacity : ∀ block, period * model.principals.length ≤
    (List.range' (((block + 1) * period - 1) * (model.serviceSlots + 1))
      model.serviceSlots).countP reserved
  roster : ∀ who, who ∈ model.principals
  windowBound : G.nodeCount * (period + 1) + 2 ≤ window
  wholePeriods : period ∣ model.total

private theorem play_publicInvariant (model : CandidateRoundModel supported nullValue window)
    (players : Profile model.game.sig) (next : model.game.sig.Outcome)
    (hnext : next ∈ (model.game.play players).support) :
    let runtime := supported.resolvingRuntime nullValue window
    SealedResolution.PublicEventInvariant runtime next.native.application.visible ∧
      SealedResolution.SettlementInvariant runtime next.native.application.visible := by
  intro runtime
  exact runtime.runRounds_candidate_publicInvariant model.principals model.serviceSlots
    players model.wire model.total _ next
    ⟨SealedResolution.PublicEventInvariant.initial runtime,
      SealedResolution.SettlementInvariant.initial runtime⟩ hnext

/-- Every timeout in a unilateral deviation belongs to that deviator. The
claim concerns actual supported executions, not an assumed policy discipline. -/
theorem deviation_timeout_owner (model : CandidateRoundModel supported nullValue window)
    (timely : model.Timely) (profile : CommitPolicyProfile G) (who : Player)
    (replacement : model.game.sig.Strategy who) (next : model.game.sig.Outcome)
    (hnext : next ∈ (model.game.play
      (Profile.update (model.compileProfile profile) who replacement)).support)
    (htimeout : next.native.application.visible.timeouts ≠ []) :
    ∃ node : Fin G.nodeCount, node.val ∈ next.native.application.visible.timeouts ∧
      ((∃ guard, (G.nodeRow node).sem = .commit who guard) ∨
        ∃ (producer : Fin G.nodeCount) (guard : EventGuard L),
          (G.nodeRow node).sem = .reveal (G.nodeTarget producer) ∧
          (G.nodeRow producer).sem = .commit who guard) := by
  obtain ⟨index, hindex⟩ := List.exists_mem_of_ne_nil _ htimeout
  obtain ⟨node, owner, hnode, hnot, howned⟩ :=
    supported.candidate_runRounds_timeout_owner nullValue window model.principals
      model.serviceSlots _ model.wire timely.reserved timely.service timely.period
      timely.positive timely.capacity profile (fun player => player ≠ who)
      (by
        intro player hplayer
        rw [Profile.update_of_ne _ _ hplayer]
        rfl)
      (fun player _ => timely.roster player) timely.windowBound model.total timely.wholePeriods
      next hnext index hindex
  have heq : owner = who := not_not.mp hnot
  subst owner
  exact ⟨node, by simpa only [hnode] using hindex, howned⟩

variable [Fintype Player]

/-- The original graph profile and its compiled native profile have the same
expected public utility. The candidate wire policy is arbitrary subject to
the operational service condition; no source program is used. -/
theorem honest_utility (model : CandidateRoundModel supported nullValue window)
    (timely : model.Timely) (hguards : GuardLive G) (utility : G.PublicUtility)
    (profile : CommitPolicyProfile G) (who : Player) :
    (model.game.play (model.compileProfile profile)).expect
        (fun next => model.nativeUtility utility next who) =
      ((policyGame G supported.graphWF hguards).play profile).expect
        (fun cfg => utility.eval cfg.1.store who) := by
  let runtime := supported.resolvingRuntime nullValue window
  obtain ⟨wire, hwire⟩ := runtime.candidateWirePolicy_surjective model.wire
  have hservice := runtime.inclusionService_of_candidateWirePolicy wire
    (fun turn => timely.reserved turn = true) (by rw [hwire]; exact timely.service)
  obtain ⟨coupling, hgraph, hnative, hpairs⟩ :=
    supported.exists_honest_candidate_round_graph_coupling hguards nullValue window
      model.principals model.serviceSlots profile wire timely.reserved hservice timely.period
      timely.positive timely.capacity timely.roster timely.windowBound model.total
      timely.wholePeriods model.budget
  rw [hwire] at hnative
  change coupling.map Prod.snd = model.game.play (model.compileProfile profile) at hnative
  change coupling.map Prod.fst = (policyGame G supported.graphWF hguards).play profile at hgraph
  rw [← hnative, FinDist.expect_map, ← hgraph, FinDist.expect_map]
  apply FinDist.expect_congr
  intro pair hpair
  exact utility.congr _ _ (hpairs pair.1 pair.2 hpair).2.2.2 who

/-- Every unrestricted randomized candidate deviation is bounded by one legal
graph deviation against the unchanged graph opponents. The finite response
mixture is constructed from the native runner, not supplied by the caller. -/
theorem deviation_bound (model : CandidateRoundModel supported nullValue window)
    (timely : model.Timely) (hinfo : G.PublicPrefixReadable) (hguards : GuardLive G)
    (hunique : G.UniqueReveals) (utility : G.PublicUtility) (bound : Player → ℝ)
    (hbound : utility.QuitBound nullValue bound) (profile : CommitPolicyProfile G)
    (who : Player) (replacement : model.game.sig.Strategy who) :
    ∃ alternative : CommitPolicy G who,
      (model.game.play (Profile.update (model.compileProfile profile) who replacement)).expect
          (fun next => model.nativeUtility utility next who) ≤
        ((policyGame G supported.graphWF hguards).play
          (Profile.update profile who alternative)).expect
            (fun cfg => utility.eval cfg.1.store who) := by
  obtain ⟨responses, hgraph, hnative, hpairs⟩ :=
    supported.exists_randomized_candidate_round_graph_coupling hinfo hguards nullValue window
      model.principals model.serviceSlots model.total who nullValue profile replacement model.wire
  let coupling := responses.bind fun commands => supported.candidateGraphRoundCoupling
    hinfo hguards nullValue window model.principals model.serviceSlots model.total who
      commands.1 commands.2 nullValue profile
  change coupling.map Prod.snd = model.game.play
    (Profile.update (model.compileProfile profile) who replacement) at hnative
  have hpointwise : coupling.expect (fun pair => model.nativeUtility utility pair.2 who) ≤
      coupling.expect (fun pair => utility.eval pair.1.1.store who) := by
    apply FinDist.expect_mono
    intro pair hpair
    obtain ⟨hterminal, hcomplete, hagrees⟩ := hpairs pair.1 pair.2 hpair
    have hdone := hcomplete model.budget
    by_cases hclear : pair.2.native.application.visible.timeouts = []
    · exact (utility.congr _ _ (hagrees hdone hclear) who).le
    · have hnext : pair.2 ∈ (model.game.play
          (Profile.update (model.compileProfile profile) who replacement)).support := by
        rw [← hnative, FinDist.support_map]
        exact ⟨pair, hpair, rfl⟩
      obtain ⟨node, htimeout, howned⟩ :=
        model.deviation_timeout_owner timely profile who replacement pair.2 hnext hclear
      obtain ⟨hevents, hsettlement⟩ := model.play_publicInvariant _ pair.2 hnext
      exact supported.timeout_utility_le_graph hguards hunique nullValue window utility bound
        hbound pair.2.native.application.visible hevents hsettlement hdone
        node who htimeout howned pair.1 hterminal
  have hnativeExpect := congrArg
    (fun law => law.expect (fun next => model.nativeUtility utility next who)) hnative
  simp only [FinDist.expect_map] at hnativeExpect
  have hgraphExpect := congrArg
    (fun law => law.expect (fun cfg => utility.eval cfg.1.store who)) hgraph
  simp only [FinDist.expect_map, FinDist.expect_bind] at hgraphExpect
  obtain ⟨commands, _, hmean⟩ := FinDist.exists_expect_le_support responses
    (fun commands => (supported.candidateGraphRun hinfo hguards nullValue window who
      commands.1 commands.2 (roundSchedule model.principals model.serviceSlots model.total)
      nullValue profile).expect (fun cfg => utility.eval cfg.1.store who))
  refine ⟨supported.extractedCandidateCommitPolicy hinfo nullValue window who commands.1
    commands.2 (roundSchedule model.principals model.serviceSlots model.total) nullValue, ?_⟩
  apply hnativeExpect.symm.le.trans
  apply hpointwise.trans
  convert hgraphExpect.le.trans hmean using 1
  · exact FinDist.expect_bind _ _ _
  · rfl

/-- A composable graph-to-candidate strategic edge for public-outcome
utilities satisfying the graph-only uniform quitting bound. -/
def utilitySimulation (model : CandidateRoundModel supported nullValue window)
    (timely : model.Timely) (hinfo : G.PublicPrefixReadable) (hguards : GuardLive G)
    (hunique : G.UniqueReveals) (utility : G.PublicUtility) (bound : Player → ℝ)
    (hbound : utility.QuitBound nullValue bound) :
    UtilitySimulation (policyGame G supported.graphWF hguards) model.game
      (fun cfg => utility.eval cfg.1.store) (model.nativeUtility utility) where
  compileStrategy := model.compileStrategy
  honest_utility := model.honest_utility timely hguards utility
  deviation_bound := model.deviation_bound timely hinfo hguards hunique utility bound hbound

/-- Same-error Nash preservation and reflection at compiled graph profiles.
The conclusion does not characterize equilibria outside the compiler image. -/
theorem isεNash_compileProfile_iff (model : CandidateRoundModel supported nullValue window)
    (timely : model.Timely) (hinfo : G.PublicPrefixReadable) (hguards : GuardLive G)
    (hunique : G.UniqueReveals) (utility : G.PublicUtility) (bound : Player → ℝ)
    (hbound : utility.QuitBound nullValue bound) (ε : ℝ) (profile : CommitPolicyProfile G) :
    IsεNash model.game (model.nativeUtility utility) ε (model.compileProfile profile) ↔
      IsεNash (policyGame G supported.graphWF hguards) (fun cfg => utility.eval cfg.1.store)
        ε profile :=
  (model.utilitySimulation timely hinfo hguards hunique utility bound hbound
    ).isεNash_compileProfile_iff ε profile

end CandidateRoundModel
end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.CandidateRoundModel.deviation_bound'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.CandidateRoundModel.deviation_bound

/-- info: 'Vegas.EventGraph.SealedFragment.CandidateRoundModel.isεNash_compileProfile_iff'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.CandidateRoundModel.isεNash_compileProfile_iff
