/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServiceRosterPrefixLaw
import Vegas.Game.RevealServicePayoffs
import Vegas.Compile.EventGraphReadoutComplete

/-! # Source continuations after completed roster phases

The existing public checkpoint locates the source protocol state inside the
original program. Executing the remaining actual roster blocks has its exact
source continuation law. Actual response counts and published-message invariants
are retained; there is no reset of private recall or passive observations.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

omit [Fintype Player] in
private theorem decodePrefix_terminal_readout
    {Field : Type} [DecidableEq Field] {layout : Field → EventGraph.EventField Player L}
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (reveals : program.RevealOnly)
    (refs : ContextRefs layout Γ) (revelations : Revelations Γ)
    (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
    (store : EventGraph.Store layout) (history : History Player L) :
    (decodePrefix? program refs revelations outputs (eventCount program) store history).bind
        (ProtocolState.readout program) =
      decodeState? (terminalRefsWith program refs outputs) store := by
  induction program with
  | ret payoffs =>
      simp only [eventCount, decodePrefix?, terminalRefsWith]
      cases decoded : decodeState? refs store <;> rfl
  | sample name fresh law next ih => exact reveals.elim
  | commit name owner fresh guard next ih => exact reveals.elim
  | reveal published owner name fresh selected unresolved next ih =>
      simp only [eventCount, decodePrefix?, terminalRefsWith, Option.bind_map]
      exact ih reveals _ _ _

private theorem source_prefix_terminal_readout
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (reveals : program.RevealOnly)
    (profile : BehavioralProfile program) (source : Config Player L Γ) :
    ((fun law => law.bind (ProtocolState.behavioralStateStep program profile))^[eventCount program]
      (PMF.pure (ProtocolState.entry program source))).map (ProtocolState.readout program) =
      (runFrom program profile source).map some := by
  induction program with
  | ret payoffs =>
      simp [eventCount, runFrom, runWith, ProtocolState.readout, ProtocolState.entry, PMF.pure_map]
  | sample name fresh law next ih => exact reveals.elim
  | commit name owner fresh guard next ih => exact reveals.elim
  | reveal published owner name fresh selected unresolved next ih =>
      rw [eventCount, ProtocolState.behavioralStatePrefix_reveal, PMF.map_bind,
        runFrom_reveal, PMF.map_bind]
      apply bind_congr_on_support _
      intro disclose _
      rw [PMF.map_comp]
      exact ih reveals (afterReveal profile) (revealSuccessor published selected source disclose)

omit [Fintype Player] in
/-- All remaining blocks from a typed checkpoint, with the exact current own
response counts, implement the original residual source runner. -/
theorem run_roster_source_suffix_option_law
    [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program) (initial : State L setup.context)
    {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (reveals : program.RevealOnly)
    (profile : BehavioralProfile program)
    (source : Config Player L Γ) (refs : ContextRefs (graphLayout setup.program) Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat)
    (aligned : CompiledPolicySuffix setup.program wholeProfile program profile
      refs source.revelations [] embedding refsBefore offset)
    (execution : (application setup leaks).Execution)
    (checkpoint : PublicCheckpoint setup leaks initial source refs offset execution)
    (counts : ∀ who, (execution.recall who).length =
      (((List.finRange (graph setup).order.eventCount).take offset).flatMap rosters).count who)
    (clean : execution.network.Satisfies (fun message =>
      message.id ∈ execution.network.ledger.map Message.id))
    (serials : execution.network.SerialsBeforeNext) :
    ((runtime setup).runInteractionPlan leaks
      (rosterPolicy setup leaks rosters timing wholeProfile) network
      ((List.finRange (eventCount program)).flatMap fun index =>
        rosterBlock setup rosters (embedding.event index)) execution).map
      (fun final => decodeState? (terminalRefsWith program refs embedding.ref)
        final.application.config.store) = (runFrom program profile source).map some := by
  let := Fintype.ofFinite Player
  have prefixLaw := run_roster_source_prefix_option_law setup leaks rosters timing network
    wholeProfile initial program reveals profile source refs embedding refsBefore offset aligned
    (eventCount program) le_rfl execution checkpoint counts clean serials
  have terminalLaw := congrArg (fun law => law.map
    (fun state => state.bind (ProtocolState.readout program))) prefixLaw
  rw [List.take_of_length_le (by simp)] at terminalLaw
  simp only [PMF.map_comp, Function.comp_def,
    decodePrefix_terminal_readout program reveals, Option.bind_some] at terminalLaw
  exact terminalLaw.trans (source_prefix_terminal_readout program reveals profile source)

omit [Fintype Player] in
/-- The full remaining native roster plan from an existing source protocol
position has its original continuation law. This holds after any supported
earlier physical timing and silent responses satisfying the checkpoint. -/
theorem roster_prefix_continuation_option_law
    [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (wholeProfile : BehavioralProfile setup.program) (initial : State L setup.context) :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (_reveals : program.RevealOnly)
      (profile : BehavioralProfile program)
      (refs : ContextRefs (graphLayout setup.program) Γ) (revelations : Revelations Γ)
      (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
        program) (refsBefore : ContextRefsBefore refs embedding) (offset : Nat),
      CompiledPolicySuffix setup.program wholeProfile program profile refs revelations []
        embedding refsBefore offset →
      ∀ (count : Nat) (state : ProtocolState program)
        (execution : (application setup leaks).Execution),
      PublicPrefixCheckpoint setup leaks initial program refs revelations embedding.ref
        offset count state execution →
      (∀ who, (execution.recall who).length =
        List.count who (List.flatMap rosters
          ((List.finRange (graph setup).order.eventCount).take (offset + count)))) →
      execution.network.Satisfies (fun message =>
        message.id ∈ execution.network.ledger.map Message.id) →
      execution.network.SerialsBeforeNext →
      ((runtime setup).runInteractionPlan leaks
        (rosterPolicy setup leaks rosters timing wholeProfile) network
        (((List.finRange (eventCount program)).drop count).flatMap fun index =>
          rosterBlock setup rosters (embedding.event index)) execution).map
        (fun final => decodeState? (terminalRefsWith program refs embedding.ref)
          final.application.config.store) =
        (ProtocolState.continuationLaw program profile state).map some := by
  let := Fintype.ofFinite Player
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro reveals profile refs revelations embedding refsBefore offset aligned count state
        execution related counts clean serials
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [← revelationsEq] at aligned
          rw [List.drop_zero]
          exact run_roster_source_suffix_option_law setup leaks rosters timing network wholeProfile
            initial _ reveals profile state refs embedding refsBefore offset aligned
            execution checkpoint counts clean serials
      | succ count => exact related.elim
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile refs revelations embedding refsBefore offset aligned count state
        execution related counts clean serials
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [← revelationsEq] at aligned
          rw [List.drop_zero, ProtocolState.continuationLaw_entry]
          exact run_roster_source_suffix_option_law setup leaks rosters timing network wholeProfile
            initial _ reveals profile source refs embedding refsBefore offset aligned
            execution checkpoint counts clean serials
      | succ count =>
          cases state with
          | inl source => exact related.elim
          | inr state =>
              let index : Fin (eventCount
                (.reveal published owner name fresh selected unresolved next)) :=
                  ⟨0, by simp [eventCount]⟩
              let tailEmbedding := embedding.tail next (by simp [eventCount]) (fun _ => rfl)
              let tailRefs := refs.cons (name := published) (cell := .publication payload)
                (embedding.ref index)
              have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
                intro readName cell ref remaining
                cases ref with
                | here =>
                    change (embedding.event index).val <
                      (embedding.event (Fin.succ remaining)).val
                    apply embedding.strictMono
                    exact Fin.mk_lt_mk.mpr (Nat.zero_lt_succ _)
                | there ref => exact refsBefore ref (Fin.succ remaining)
              have tailAligned : CompiledPolicySuffix setup.program wholeProfile next
                  (afterReveal profile) tailRefs (revelations.reveal selected)
                  [] tailEmbedding tailBefore (offset + 1) := by
                simpa only [Registry.weaken, List.map_nil, tailRefs, tailEmbedding] using
                  aligned.revealTail (whole := setup.program) (wholeProfile := wholeProfile)
                    fresh selected unresolved next profile refs revelations [] embedding
                    refsBefore offset
              have tailCounts : ∀ who, (execution.recall who).length =
                  (((List.finRange (graph setup).order.eventCount).take
                    (offset + 1 + count)).flatMap rosters).count who := by
                simpa only [Nat.add_assoc, Nat.add_comm 1 count] using counts
              have tailLaw := ih reveals (afterReveal profile) tailRefs
                (revelations.reveal selected) tailEmbedding tailBefore (offset + 1) tailAligned
                count state execution related tailCounts clean serials
              simp only [eventCount, List.finRange_succ, List.drop_succ_cons, ← List.map_drop,
                List.flatMap_map, terminalRefsWith, ProtocolState.continuationLaw, Sum.elim_inr]
              convert tailLaw using 1 <;> rfl

omit [Fintype Player] in
/-- The compiler's terminal context contains every event output. Consequently
the explicit terminal-cut guard is redundant with successful typed decoding,
even at an arbitrary structurally valid native control state. -/
theorem sourceReadout_eq_decode (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (control : (application setup leaks).Control) :
    sourceReadout setup leaks (some control) =
      decodeState? (terminalRefs setup.program) control.execution.application.config.store := by
  unfold sourceReadout
  rw [Option.bind_some]
  cases decoded : decodeState? (terminalRefs setup.program)
      control.execution.application.config.store with
  | none => simp only [decoded, ite_self]
  | some source =>
      have complete := terminal_decode_complete setup.program .sequential
        control.execution.application.config (by rw [decoded]; rfl)
      dsimp only
      rw [ite_eq_left complete, decoded]

omit [Fintype Player] in
/-- The whole-program instance uses the actual guarded native readout and
the original source protocol state after the completed phase prefix. -/
theorem roster_continuation_sourceReadout_law [Finite Player]
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (rosters : (graph setup).EventId → List Player)
    (timing : TimingLaw setup rosters)
    (network : (runtime setup).NetworkPolicy leaks)
    (reveals : setup.program.RevealOnly)
    (profile : BehavioralProfile setup.program) (initial : State L setup.context)
    (count : Nat) (state : ProtocolState setup.program)
    (execution : (application setup leaks).Execution)
    (checkpoint : PublicPrefixCheckpoint setup leaks initial setup.program
      (ContextRefs.initial setup.context (outputLayout setup.program))
      (Revelations.initial setup.context) (outputEmbedding setup.program).ref
      0 count state execution)
    (counts : ∀ who, (execution.recall who).length =
      (((List.finRange (graph setup).order.eventCount).take count).flatMap rosters).count who)
    (clean : execution.network.Satisfies (fun message =>
      message.id ∈ execution.network.ledger.map Message.id))
    (serials : execution.network.SerialsBeforeNext) :
    ((runtime setup).runInteractionPlan leaks (rosterPolicy setup leaks rosters timing profile)
      network (((List.finRange (eventCount setup.program)).drop count).flatMap
        (rosterBlock setup rosters)) execution).map
      (fun final => sourceReadout setup leaks (some ⟨0, none, final⟩)) =
      (ProtocolState.continuationLaw setup.program profile state).map some := by
  simp_rw [sourceReadout_eq_decode]
  exact roster_prefix_continuation_option_law setup leaks rosters timing network profile initial
    setup.program reveals profile (ContextRefs.initial setup.context (outputLayout setup.program))
    (Revelations.initial setup.context) (outputEmbedding setup.program)
    (initialRefsBefore setup.program) 0 (CompiledPolicySuffix.whole setup.program profile)
    count state execution checkpoint (by simpa only [Nat.zero_add] using counts) clean serials

end Vegas
