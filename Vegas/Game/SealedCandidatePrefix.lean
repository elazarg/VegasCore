/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SealedCandidate
import Vegas.Compile.SealedCandidateTimeoutSettlement

/-! # Candidate deviations under prefix-relative quitting comparisons

The actual native deviation and a retained graph deviation admit a legal
quitting settlement with matching public inputs at the defaulted producer.
A graph-only comparison of those continuations therefore bounds the native
deviation without a global quitting cap or utility floor. Randomized native
policies and adaptive wire choices are handled by the existing response mixture.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment.CandidateRoundModel

open Interaction Interaction.MessageApplication GameTheory GameTheory.GameForm
open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]
variable {supported : SealedFragment G ty} {nullValue : L.Val ty} {window : Nat}

omit [Fintype Player] [DecidableEq (L.Val ty)] in
private theorem owner_eq_of_timeout_site
    (timeoutNode producer : Fin G.nodeCount) (owner who : Player) (guard : EventGuard L)
    (hcommit : (G.nodeRow producer).sem = .commit owner guard)
    (hsite : timeoutNode = producer ∨
      (G.nodeRow timeoutNode).sem = .reveal (G.nodeTarget producer))
    (howned : (∃ otherGuard, (G.nodeRow timeoutNode).sem = .commit who otherGuard) ∨
      ∃ (otherProducer : Fin G.nodeCount) (otherGuard : EventGuard L),
        (G.nodeRow timeoutNode).sem = .reveal (G.nodeTarget otherProducer) ∧
        (G.nodeRow otherProducer).sem = .commit who otherGuard) :
    owner = who := by
  rcases hsite with rfl | hreveal
  · rcases howned with ⟨otherGuard, hother⟩ | ⟨otherProducer, otherGuard, hother, _⟩
    · exact (NodeSem.commit.inj (hcommit.symm.trans hother)).1
    · rw [hcommit] at hother
      contradiction
  · rcases howned with ⟨otherGuard, hother⟩ | ⟨otherProducer, otherGuard, hother, hproducer⟩
    · rw [hreveal] at hother
      contradiction
    · have htarget := NodeSem.reveal.inj (hreveal.symm.trans hother)
      have hsame : producer = otherProducer := by
        apply Fin.ext
        unfold Graph.nodeTarget at htarget
        omega
      subst otherProducer
      exact (NodeSem.commit.inj (hcommit.symm.trans hproducer)).1

/-- Every arbitrary native deviation is bounded by a graph deviation against
the unchanged opponents if prefix-matched legal quitting settlements are no
better than the supported graph continuation. The incentive premise mentions
only the graph game, its public reads and utility, never native execution. -/
theorem deviation_bound_of_quit_prefix
    (model : CandidateRoundModel supported nullValue window) (timely : model.Timely)
    (hinfo : G.PublicPrefixReadable) (hguards : GuardLive G) (hunique : G.UniqueReveals)
    (utility : G.PublicUtility) (profile : CommitPolicyProfile G) (who : Player)
    (hquitting : ∀ (alternative : CommitPolicy G who)
      (quitting continued : ReachableConfig G),
      continued ∈ ((policyGame G supported.graphWF hguards).play
        (Profile.update profile who alternative)).support →
      Terminal G quitting.1 →
      ∀ (producer : Fin G.nodeCount) (guard : EventGuard L),
        (G.nodeRow producer).sem = .commit who guard →
        quitting.1.store (G.nodeTarget producer) = some (⟨ty, nullValue⟩ : TypedValue L) →
        (∀ ref ∈ guard.choiceReads, G.fieldRefPublic ref →
          Store.getAs quitting.1.store ref.field ref.ty =
            Store.getAs continued.1.store ref.field ref.ty) →
        utility.eval quitting.1.store who ≤ utility.eval continued.1.store who)
    (replacement : model.game.sig.Strategy who) :
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
  have hwindow : 0 < window := by have hbound := timely.windowBound; omega
  have hpointwise : coupling.expect (fun pair => model.nativeUtility utility pair.2 who) ≤
      coupling.expect (fun pair => utility.eval pair.1.1.store who) := by
    apply FinDist.expect_mono
    intro pair hpair
    have hcomplete := (hpairs pair.1 pair.2 hpair).2.1 model.budget
    by_cases hclear : pair.2.native.application.visible.timeouts = []
    · exact (utility.congr _ _ ((hpairs pair.1 pair.2 hpair).2.2 hcomplete hclear) who).le
    · have hnext : pair.2 ∈ (model.game.play
          (Profile.update (model.compileProfile profile) who replacement)).support := by
        rw [← hnative, FinDist.support_map]
        exact ⟨pair, hpair, rfl⟩
      have hpure := hpair
      change pair ∈ (responses.bind fun commands => supported.candidateGraphRoundCoupling
        hinfo hguards nullValue window model.principals model.serviceSlots model.total who
          commands.1 commands.2 nullValue profile).support at hpure
      simp only [FinDist.support_bind, Set.mem_iUnion] at hpure
      obtain ⟨commands, _hcommands, hcommandPair⟩ := hpure
      obtain ⟨node, producer, owner, guard, quitting, htimeout, hcommit, hsite,
          hterminal, hvalue, hpublic, hreads⟩ :=
        supported.candidateGraphRoundCoupling_timeout_settlement hinfo hguards
          nullValue window model.principals model.serviceSlots model.total who
          commands.1 commands.2 nullValue hwindow hunique profile pair.1 pair.2 hcommandPair
          hcomplete hclear
      obtain ⟨actualNode, hnode, howned⟩ :=
        model.timeout_owner timely profile who replacement pair.2 hnext node.val htimeout
      have hnodes : actualNode = node := Fin.ext hnode
      subst actualNode
      have howner := owner_eq_of_timeout_site node producer owner who guard hcommit hsite howned
      subst owner
      have hcontinued : pair.1 ∈ (supported.candidateGraphRun hinfo hguards nullValue window who
          commands.1 commands.2 (roundSchedule model.principals model.serviceSlots model.total)
          nullValue profile).support := by
        rw [← supported.candidateGraphRoundCoupling_graph, FinDist.support_map]
        exact ⟨pair, hcommandPair, rfl⟩
      have hbound := hquitting
        (supported.extractedCandidateCommitPolicy hinfo nullValue window who commands.1 commands.2
          (roundSchedule model.principals model.serviceSlots model.total) nullValue)
        quitting pair.1 hcontinued hterminal producer guard hcommit hvalue hreads
      exact (utility.congr _ _ hpublic who).le.trans hbound
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

end Vegas.EventGraph.SealedFragment.CandidateRoundModel

/-- info: 'Vegas.EventGraph.SealedFragment.CandidateRoundModel.deviation_bound_of_quit_prefix'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.CandidateRoundModel.deviation_bound_of_quit_prefix
