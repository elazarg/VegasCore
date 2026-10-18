/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseProposalTyping
import Vegas.Pending.PhasePacketAddress
import Vegas.Source.ProposalRecoveryAddress
import Vegas.Compile.EventGraphLayout
import Vegas.Compile.EventGraphAssembly

/-! # Publication proposal addresses agree with physical phase origins -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {Γ : SourceCtx Player L} {O : Finset VarId}

theorem publicationAt_outputLayout (program : SourceProgram Player L Γ O)
    (event : Fin (eventCount program)) :
    program.publicationAt event.val = true ↔ (outputLayout program event).IsPublication := by
  induction program with
  | ret => exact Fin.elim0 event
  | sample name fresh law next ih =>
      refine Fin.cases ?_ (fun later => ?_) event
      · simp only [Fin.val_zero, publicationAt, outputLayout, Fin.cases_zero,
          EventField.IsPublication, Bool.false_eq_true]
      · exact ih later
  | commit name owner fresh guard next ih =>
      refine Fin.cases ?_ (fun later => ?_) event
      · simp only [Fin.val_zero, publicationAt, outputLayout, Fin.cases_zero,
          EventField.IsPublication, Bool.false_eq_true]
      · exact ih later
  | reveal published owner name fresh source unresolved next ih =>
      refine Fin.cases ?_ (fun later => ?_) event
      · simp only [Fin.val_zero, publicationAt, outputLayout, Fin.cases_zero,
          EventField.IsPublication]
      · exact ih later

/-- A maximal native publication interval has the static source scan address.
This uses the whole plan boundary, rather than the source saved checkpoint
which advances after every individual publication. -/
theorem publicationBlockLow_of_phase (program : SourceProgram Player L Γ O)
    (mode : ExecutionMode)
    (plan : RuntimePhasePlan ((toEventGraph program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (phase : RuntimePhase ((toEventGraph program).withMode mode))
    (member : phase ∈ plan.phases) (kind : phase.kind = .reveal)
    (event : ((toEventGraph program).withMode mode).EventId) (inside : event ∈ phase.events) :
    program.publicationBlockLow event.val = phase.low := by
  have interval := (phase.mem_events event).mp inside
  apply program.publicationBlockLow_eq_of_interval phase.low event.val interval.1
  · intro index lower upper
    have bounded : index < eventCount program := lt_trans upper event.isLt
    let selected : ((toEventGraph program).withMode mode).EventId := ⟨index, bounded⟩
    have field := phase.fields selected lower (upper.trans interval.2)
    rw [kind] at field
    obtain ⟨payload, output⟩ := field
    apply (publicationAt_outputLayout program selected).mpr
    change outputLayout program selected = .publication payload at output
    rw [output]
    trivial
  · obtain ⟨before, after, word⟩ := List.mem_iff_append.mp member
    rcases before.eq_nil_or_concat' with empty | ⟨earlier, previous, prior⟩
    · left
      apply plan.first phase
      rw [word, empty]
      exact Option.mem_some_iff.mpr rfl
    · right
      have orderedWord : plan.phases = earlier ++ previous :: phase :: after := by
        simpa only [prior, List.append_assoc, List.singleton_append] using word
      have adjacent := (List.isChain_iff_forall_rel_of_append_cons_cons.mp plan.adjacent)
        orderedWord
      have different := (List.isChain_iff_forall_rel_of_append_cons_cons.mp maximal) orderedWord
      have notReveal : previous.kind ≠ .reveal := by
        intro reveal
        rw [reveal, kind] at different
        rcases different with impossible | impossible
        · exact impossible rfl
        · cases impossible
      have previousBounds : previous.low ≤ phase.low - 1 ∧ phase.low - 1 < previous.high := by
        have nonempty := previous.nonempty
        omega
      have bounded : phase.low - 1 < eventCount program :=
        previousBounds.2.trans_le previous.bounded
      let selected : ((toEventGraph program).withMode mode).EventId :=
        ⟨phase.low - 1, bounded⟩
      have field := previous.fields selected previousBounds.1 previousBounds.2
      apply Bool.eq_false_of_not_eq_true
      intro published
      have publication := (publicationAt_outputLayout program selected).mp published
      change (((toEventGraph program).withMode mode).outputLayout selected).IsPublication
        at publication
      cases selectedKind : previous.kind with
      | reveal => exact notReveal selectedKind
      | commitment =>
          rw [selectedKind] at field
          obtain ⟨owner, payload, output⟩ := field
          rw [output] at publication
          exact publication
      | sample =>
          rw [selectedKind] at field
          obtain ⟨payload, output⟩ := field
          rw [output] at publication
          exact publication

/-- The actual phase in a counted opening packet is the source's maximal
publication-block address, including packets of retired attempts. -/
theorem submitted_proposal_publicationBlockLow [Fintype Player]
    (program : SourceProgram Player L Γ O) (mode : ExecutionMode)
    (runtime : EventGraphRuntime ((toEventGraph program).withMode mode))
    (leaks : MessageNetwork.ObservationRule Player
      (CommitAttemptPacket ((toEventGraph program).withMode mode)))
    (plan : RuntimePhasePlan ((toEventGraph program).withMode mode))
    (maximal : plan.phases.IsChain fun before after =>
      before.kind ≠ after.kind ∨ before.kind = .sample)
    (bounds : MessageBounds ((toEventGraph program).withMode mode))
    (inputs : PMF ((toEventGraph program).withMode mode).Inputs) (horizon : Nat)
    (scheduler : (phaseApplication runtime leaks).Scheduler)
    (control : (phaseApplication runtime leaks).Control)
    (trace : ((PhaseCount.onePacketMenu runtime leaks bounds).protocol
      (inputs.map (PhaseRuntimeState.initial plan)) horizon scheduler).Trace (some control))
    (message : Message Player (CommitAttemptPacket ((toEventGraph program).withMode mode)))
    (submitted : message ∈ control.execution.network.inputs)
    (coordinate : CommitAttemptEvent ((toEventGraph program).withMode mode)) (raw : Raw L)
    (proposed : PhaseProposal.packetProposal? message.payload = some (coordinate, raw)) :
    program.publicationBlockLow coordinate.event.val = coordinate.attempt.phase := by
  obtain ⟨attempt, candidate, call⟩ :=
    PhaseProposal.opening_of_packetProposal message.payload coordinate raw proposed
  have origins := PhaseCount.packetPhaseOrigins_history runtime leaks plan bounds inputs horizon
    scheduler trace
  obtain ⟨phase, member, named, eventCall, inside, phaseAddress⟩ := origins message submitted
  rw [call] at eventCall
  have same : coordinate.event = named := Option.some.inj eventCall
  subst named
  have clean := (PhaseCount.onePacketMenu_countClean runtime leaks bounds scheduler).history
    _ horizon (fun state _ => PhaseCount.countClean_initial runtime leaks state) trace
  obtain ⟨payload, value, publication, _typed⟩ := PhaseProposal.permitted_proposal_typed
    control.execution.network.inputs message
      ((PhaseCount.permits_eq_true_iff _ _).mp (clean.2 message submitted)) coordinate raw proposed
  have interval := (phase.mem_events coordinate.event).mp inside
  have fields := phase.fields coordinate.event interval.1 interval.2
  have kind : phase.kind = .reveal := by
    cases selected : phase.kind with
    | reveal => rfl
    | commitment =>
        rw [selected] at fields
        obtain ⟨owner, ty, output⟩ := fields
        cases publication.symm.trans output
    | sample =>
        rw [selected] at fields
        obtain ⟨ty, output⟩ := fields
        cases publication.symm.trans output
  rw [publicationBlockLow_of_phase program mode plan maximal phase member kind
    coordinate.event inside, ← phaseAddress, attempt]

end Vegas
