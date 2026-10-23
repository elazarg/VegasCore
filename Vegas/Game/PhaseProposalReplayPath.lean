/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.CompiledRevealPhase
import Vegas.Source.CommitRecoveryNonCommitPath

/-! # Actual source history extensions retain native replay annotations -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol
  GameTheory.Protocol.ExecutionProtocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The existing trace fold retains the actual source transitions, rather
than only their joint action or public address projections. -/
def proposalSourceSteps (setup : Setup (Player := Player) (L := L))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    List setup.commitRecoveryProtocol.StepEvent :=
  letI : Zero (List setup.commitRecoveryProtocol.StepEvent) := ⟨[]⟩
  letI : Add (List setup.commitRecoveryProtocol.StepEvent) := ⟨List.append⟩
  Trace.valueSum (fun event => [event]) trace

theorem proposalSourceSteps_extend (setup : Setup (Player := Player) (L := L))
    {before after : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace before)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (legal : setup.commitRecoveryProtocol.Legal before joint)
    (supported : after ∈ (setup.commitRecoveryProtocol.step before ⟨joint, legal⟩).support) :
    proposalSourceSteps setup (prior.extend joint legal supported) =
      proposalSourceSteps setup prior ++ [⟨before, joint, legal, after, supported⟩] := rfl

theorem proposalSourceSteps_length (setup : Setup (Player := Player) (L := L))
    {state : setup.commitRecoveryProtocol.State}
    (trace : setup.commitRecoveryProtocol.Trace state) :
    (proposalSourceSteps setup trace).length = trace.length := by
  induction trace with
  | start => rfl
  | extend prior joint legal supported ih =>
      simp only [proposalSourceSteps_extend, List.length_append, List.length_singleton,
        ih, Trace.length]

/-- Only the newly appended part is annotated. Earlier saved source
instructions keep their original physical namespace and evidence. -/
def NativeSourceReplayExtension (setup : Setup (Player := Player) (L := L))
    {graph : Vegas.EventGraph Player L} (native : EventGraphRuntime.State graph)
    (generation : Nat) {before after : setup.commitRecoveryProtocol.State}
    (prior : setup.commitRecoveryProtocol.Trace before)
    (trace : setup.commitRecoveryProtocol.Trace after) : Prop :=
  ∃ (events : List setup.commitRecoveryProtocol.StepEvent)
    (points : List (ProtocolState setup.program × Finset Player)),
    points.IsChain (NativePublicSourceStep native 0 setup.program) ∧
    points.head?.map (fun point => CommitRecoveryState.atPoint point.1 point.2 generation) =
      before ∧
    proposalSourceSteps setup trace = proposalSourceSteps setup prior ++ events ∧
    (∀ event ∈ events, ∃ first last : ProtocolState setup.program × Finset Player,
      event.source = some (CommitRecoveryState.atPoint first.1 first.2 generation) ∧
      event.target = some (CommitRecoveryState.atPoint last.1 last.2 generation) ∧
      NativePublicSourceStep native 0 setup.program first last ∧
      NativeDisclosureReadback native 0 setup.program first.1 first.2 event.joint ∧
      first ∈ points) ∧
    events.length = trace.length - prior.length ∧
    ∀ index (bound : index < events.length),
      (events[index]'bound).source.map (fun state => instructionCount setup.program -
        ProtocolState.remaining setup.program state.point) =
      before.map (fun state => instructionCount setup.program -
        ProtocolState.remaining setup.program state.point + index)

/-- Lift the already reconstructed native source path into the actual source
history, retaining each new step's original native annotation. The source
transition and setup law are unchanged. -/
theorem native_public_path_history
    (setup : Setup (Player := Player) (L := L))
    {graph : Vegas.EventGraph Player L} (native : EventGraphRuntime.State graph)
    (initial : Config Player L setup.context) (generation : Nat)
    (first last : ProtocolState setup.program × Finset Player)
    (path : Relation.ReflTransGen (NativePublicSourceStep native 0 setup.program) first last)
    (prior : setup.commitRecoveryProtocol.Trace
      (some (CommitRecoveryState.atPoint first.1 first.2 generation))) :
    ∃ (trace : setup.commitRecoveryProtocol.Trace
        (some (CommitRecoveryState.atPoint last.1 last.2 generation)))
      (states : List (ProtocolState setup.program × Finset Player))
      (joints : List (Player → Option (CommitRecoveryMove Player L)))
      (events : List setup.commitRecoveryProtocol.StepEvent),
      (first :: states).IsChain (NativePublicSourceStep native 0 setup.program) ∧
      (first :: states).getLast (List.cons_ne_nil _ _) = last ∧
      setup.commitRecoveryProtocol.ReachesWithin joints.length
        ⟨_, prior⟩ ⟨_, trace⟩ ∧
      trace.length = prior.length + joints.length ∧
      setup.recoveryJointRecall trace = joints.reverse ++ setup.recoveryJointRecall prior ∧
      setup.recoveryAddressWord trace = setup.recoveryAddressWord prior ++
        states.map (fun point =>
          (CommitRecoveryState.atPoint point.1 point.2 generation).publicAddress) ∧
      proposalSourceSteps setup trace = proposalSourceSteps setup prior ++ events ∧
      (∀ event ∈ events, ∃ before after : ProtocolState setup.program × Finset Player,
        event.source = some (CommitRecoveryState.atPoint before.1 before.2 generation) ∧
        event.target = some (CommitRecoveryState.atPoint after.1 after.2 generation) ∧
        NativePublicSourceStep native 0 setup.program before after ∧
        NativeDisclosureReadback native 0 setup.program before.1 before.2 event.joint ∧
        before ∈ first :: states) ∧
      events.length = joints.length ∧
      ∀ index (bound : index < events.length),
        (events[index]'bound).source.map (fun state => instructionCount setup.program -
          ProtocolState.remaining setup.program state.point) =
        some (instructionCount setup.program -
          ProtocolState.remaining setup.program first.1 + index) := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl =>
      exact ⟨prior, [], [], [], .singleton _, rfl, .refl 0 _,
        by simp only [List.length_nil, Nat.add_zero], rfl,
        (List.append_nil _).symm, (List.append_nil _).symm,
        (fun _ absent => (List.not_mem_nil absent).elim), rfl, fun _ absent => by
          simp only [List.length_nil] at absent; omega⟩
  | @head first middle moved _rest ih =>
      obtain ⟨running, notCommit, _joint, _supported⟩ := moved.1
      obtain ⟨joint, supported, nativeDisclosure⟩ := moved.2.2.2
      obtain ⟨legalJoint, legal, realized, disclosure⟩ := CommitRecoveryState.nonCommit_successor
        setup.program initial first.1 first.2 generation notCommit running joint middle supported
      have legal' : setup.commitRecoveryProtocol.Legal
          (some (CommitRecoveryState.atPoint first.1 first.2 generation)) legalJoint := legal
      have realized' : some (CommitRecoveryState.atPoint middle.1 middle.2 generation) ∈
          (setup.commitRecoveryProtocol.step _ ⟨legalJoint, legal'⟩).support :=
        (PMF.mem_support_map_iff _ _ _).mpr ⟨_, realized, rfl⟩
      let next := prior.extend legalJoint legal' realized'
      let event : setup.commitRecoveryProtocol.StepEvent := ⟨_, legalJoint, legal', _, realized'⟩
      obtain ⟨trace, states, joints, events, chain, ending, reached, length, word,
        addresses, steps, annotated, eventCount, cursors⟩ := ih next
      refine ⟨trace, middle :: states, legalJoint :: joints, event :: events,
        .cons_cons moved chain, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [List.getLast_cons_cons] using ending
      · simpa only [List.length_cons] using
          (ReachesWithin.step (E := setup.commitRecoveryProtocol)
            legalJoint legal' realized' reached)
      · simp only [next, Trace.length, List.length_cons] at length ⊢
        omega
      · simpa only [next, Setup.recoveryJointRecall, List.reverse_cons, List.append_assoc,
          List.singleton_append] using word
      · simpa only [next, Setup.recoveryAddressWord_extend, Option.elim_some, List.map_cons,
          List.append_assoc, List.singleton_append] using addresses
      · simpa only [next, proposalSourceSteps_extend, List.append_assoc,
          List.singleton_append] using steps
      · intro selected member
        rcases List.mem_cons.mp member with same | later
        · subst selected
          exact ⟨first, middle, rfl, rfl, moved,
            NativeDisclosureReadback.of_disclosure_eq native 0 setup.program first.1 first.2
              joint legalJoint nativeDisclosure disclosure, List.mem_cons_self⟩
        · obtain ⟨before, after, source, target, relation, readback, member⟩ :=
            annotated selected later
          exact ⟨before, after, source, target, relation, readback, List.mem_cons_of_mem _ member⟩
      · simpa only [List.length_cons] using congrArg Nat.succ eventCount
      · intro index bound
        cases index with
        | zero => rfl
        | succ index =>
          have earlier := cursors index (by simp only [List.length_cons] at bound; omega)
          simp only [List.getElem_cons_succ]
          rw [earlier]
          have ranked := moved.position
          congr 1
          omega

end Vegas
