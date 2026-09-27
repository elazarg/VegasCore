/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.RevealServicePrefixLaw

/-! # Remaining service execution from a decoded source position

The source protocol position selects its existing continuation evaluator.
The proof locates that position within the original compiled graph and applies
the checked actual suffix law; there is no source-history inverse or new runner.
-/

noncomputable section

namespace Vegas.SourceProgram.RevealService

open GameTheory.Math.Probability Interaction EventGraphRuntime EventLowering

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- Remaining actual C-service execution has the continuation law of the
decoded source protocol state. It allows arbitrary physical alias selectors
with the prescribed Boolean marginals. -/
theorem prefix_continuation_option_law
    (setup : Setup (Player := Player) (L := L))
    (leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup)))
    (bounds : MessageBounds (graph setup)) (watcher : Player)
    (observer : ∀ event, (graph setup).actor? event ≠ some watcher)
    (wholeProfile : BehavioralProfile setup.program)
    (players : Player → (application setup leaks).Policy)
    (watcherPolicy : players watcher = (application setup leaks).reportFirstUnpublished)
    (ordinary : ∀ who, who ≠ watcher → ∀ past view response,
      response ∈ (players who past view).support → response ∈
        ordinaryActions setup leaks (bounds.withInitialValues (initialLaw setup)) who past view)
    (projects : ∀ who, who ≠ watcher → ∀ past view opening,
      opening? setup leaks who past view = some opening →
      opening ∈ ((bounds.withInitialValues (initialLaw setup)).menu (runtime setup) leaks).actions
        who past view →
      (players who past view).map (sourceChoice setup leaks) =
        sourceChoiceLaw setup leaks wholeProfile who view)
    (initial : State L setup.context) (initialSupport : initial ∈ setup.initialLaw.support) :
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
      PrefixCheckpoint setup leaks initial program refs revelations embedding.ref
        offset count state execution →
      ((runtime setup).runInteractionPlan leaks players
        ((runtime setup).reportNetwork leaks watcher)
        (((List.finRange (eventCount program)).drop count).flatMap fun index =>
          block setup watcher (embedding.event index)) execution).map
        (fun final => decodeState? (terminalRefsWith program refs embedding.ref)
          final.application.config.store) =
        (ProtocolState.continuationLaw program profile state).map some := by
  intro Γ openNames program
  induction program with
  | ret payoffs =>
      intro reveals profile refs revelations embedding refsBefore offset aligned count state
        execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [← revelationsEq] at aligned
          rw [List.drop_zero]
          exact run_source_suffix_option_law setup leaks bounds watcher observer wholeProfile
            players watcherPolicy ordinary projects initial initialSupport _ reveals profile state
            refs embedding refsBefore offset aligned execution checkpoint
      | succ count => exact related.elim
  | sample name fresh law next ih =>
      intro impossible
      exact impossible.elim
  | commit name owner fresh guard next ih =>
      intro impossible
      exact impossible.elim
  | @reveal Γ openNames published owner name payload fresh selected unresolved next ih =>
      intro reveals profile refs revelations embedding refsBefore offset aligned count state
        execution related
      cases count with
      | zero =>
          obtain ⟨source, rfl, revelationsEq, checkpoint⟩ := related
          rw [← revelationsEq] at aligned
          rw [List.drop_zero, ProtocolState.continuationLaw_entry]
          exact run_source_suffix_option_law setup leaks bounds watcher observer wholeProfile
            players watcherPolicy ordinary projects initial initialSupport _ reveals profile source
            refs embedding refsBefore offset aligned execution checkpoint
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
              have tailLaw := ih reveals (afterReveal profile) tailRefs
                (revelations.reveal selected) tailEmbedding tailBefore (offset + 1) tailAligned
                count state execution related
              simp only [eventCount, List.finRange_succ, List.drop_succ_cons, ← List.map_drop,
                List.flatMap_map, terminalRefsWith, ProtocolState.continuationLaw, Sum.elim_inr]
              convert tailLaw using 1 <;> rfl

end Vegas.SourceProgram.RevealService
