/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.CompiledRevealReadback
import Vegas.Game.RecordedSourceHistory
import Vegas.Game.ServiceRevealTail
import Vegas.Compile.EventGraphSuffix
import Vegas.Pending.PhaseFailureOrder

/-! # Source-order reconstruction of completed concurrent reveal phases -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
theorem publication_failure_iff_read {graph : Vegas.EventGraph Player L}
    (native : EventGraphRuntime.State graph) (event : graph.EventId)
    {owner : Player} {payload : L.Ty}
    (binding : FieldRef graph.layout (.binding owner payload))
    (checks : List (GuardCheck graph.layout payload))
    (outputEq : graph.outputLayout event = .publication payload)
    (codeEq : cast (congrArg (EventCode graph.layout) outputEq) (graph.nodes event) =
      .resolve owner payload binding checks)
    (value : PublicationResult (L.Val payload))
    (stored : (⟨.inr event, outputEq⟩ : FieldRef graph.layout (.publication payload)).get?
      native.config.store = some value) :
    native.PublicFailure event ↔ value = .failure := by
  have viewed := nodeView_eq_resolve outputEq codeEq
  have missed : native.publicView.missedBinding event = false := by
    simp only [PublicView.missedBinding, outputEq]
  simp only [EventGraphRuntime.State.PublicFailure, missed, Bool.false_eq_true, false_or,
    RecoveryState.publicationFailed, viewed]
  change cast (congrArg Option (congrArg EventField.Value outputEq))
    (native.config.outputs event) = some value at stored
  have castSome : ∀ {α β : Type} (same : α = β) (item : α),
      cast (congrArg Option same) (some item) = some (cast same item) := by
    intro α β same item
    cases same
    rfl
  have castNone : ∀ {α β : Type} (same : α = β),
      cast (congrArg Option same) (none : Option α) = (none : Option β) := by
    intro α β same
    cases same
    rfl
  cases output : native.config.outputs event with
  | none =>
      rw [output, castNone (congrArg EventField.Value outputEq)] at stored
      cases stored
  | some result =>
      rw [output, castSome (congrArg EventField.Value outputEq)] at stored
      have same := Option.some.inj stored
      dsimp only
      rw [same]
      cases value <;> simp

namespace EventGraphRuntime.RecoveryState

omit [DecidableEq Player] in
/-- Reading the next source-ranked failed publication moves its owner into
the inherited set for subsequent source-order reconstruction. -/
theorem OrderedPublicFailures.raise {graph : Vegas.EventGraph Player L}
    {native : RecoveryState graph} {low : Nat} {inherited : Finset Player}
    (valid : native.OrderedPublicFailures low inherited)
    (current : graph.EventId) (ranked : current.val = low) {owner : Player}
    (acting : graph.actor? current = some owner) (nextInherited : Finset Player)
    (members : ∀ who, who ∈ nextInherited ↔ who ∈ inherited ∨
      (who = owner ∧ native.native.PublicFailure current)) :
    native.OrderedPublicFailures (low + 1) nextInherited := by
  intro event who lower publication owned completed reason
  apply valid event who (by omega) publication owned completed
  rcases reason with excluded | ⟨prior, previous, earlier, actor, failed⟩
  · rcases (members who).mp excluded with old | ⟨rfl, failed⟩
    · exact Or.inl old
    · exact Or.inr ⟨current, by omega, by omega, acting, failed⟩
  · exact Or.inr ⟨prior, by omega, earlier, actor, failed⟩

end EventGraphRuntime.RecoveryState

variable (setup : Setup (Player := Player) (L := L)) (mode : EventGraph.ExecutionMode)

/-- Completed publications reconstruct an actual sequence of recovery
instructions in source order. The final store may have been produced by any
physical ordering of independent reveals. Excluded slots retain no effective
owned source action, while active slots retain the recorded disclosure bit. -/
theorem completed_reveal_phase_source_path :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (prefixed : RevealPrefix program count)
    (refs : ContextRefs (graphLayout setup.program) Γ)
    (revelations : Revelations Γ) (registry : Registry Γ)
    (embedding : OutputEmbedding (inputLayout setup.context) (outputLayout setup.program)
      program) (before : ContextRefsBefore refs embedding) (offset : Nat)
    (_compiled : CompiledSuffix setup.program program refs revelations registry
      embedding before offset)
    (native : RecoveryState ((toEventGraph setup.program).withMode mode))
    {inputs : ((toEventGraph setup.program).withMode mode).Inputs}
    (_reachable : native.native.config.Reachable inputs)
    (entry : SourceProgram.Config Player L Γ) (inherited : Finset Player)
    (_agree : refs.Agrees entry.state native.native.config.store)
    (_guards : Registry.FailureExtension entry.registry registry entry.state)
    (_failures : Revelations.PreservesFailures entry.revelations entry.state)
    (_sameRevelations : (@Config.revelations Player L Γ entry) = @revelations)
    (_unique : (Γ.map Prod.fst).Nodup)
    (_ordered : native.OrderedPublicFailures offset inherited)
    (_completed : ∀ index : Fin (eventCount program), index.val < count →
      embedding.event index ∈ native.native.config.cut.completed),
    ∃ final : SourceProgram.Config Player L (revealTail count program prefixed).context,
    ∃ excluded : Finset Player,
      (revealTailRefs setup count program prefixed refs embedding).Agrees
        final.state native.native.config.store ∧
      Registry.FailureExtension final.registry
        (revealTailRegistry count program prefixed registry) final.state ∧
      Revelations.PreservesFailures final.revelations final.state ∧
      (@Config.revelations Player L _ final) =
        (revealTailRevelations count program prefixed revelations :
          Revelations (revealTail count program prefixed).context) ∧
      (∀ who, who ∈ excluded ↔ who ∈ inherited ∨
        ∃ index : Fin (eventCount program), index.val < count ∧
          ((toEventGraph setup.program).withMode mode).actor? (embedding.event index) = some who ∧
          native.native.PublicFailure (embedding.event index)) ∧
      Relation.ReflTransGen
        (fun left right : ProtocolState program × Finset Player =>
          ¬ ProtocolState.terminal program left.1 ∧
          ProtocolState.atCommit program left.1 = false ∧
          ∃ joint, right ∈ (ProtocolState.recoveryStep program left.1 left.2 joint).support)
        (ProtocolState.entry program entry, inherited)
        ((revealTail count program prefixed).lift
          (ProtocolState.entry _ final), excluded) ∧
      ∀ (_actions : ∀ index action,
        decodeEventAction setup.program (embedding.event index) action =
          decodeEventAction program index
            (cast (congrArg EventField.Action (embedding.layout_eq index)) action)),
        RecordedSourceHistory setup.program mode native.native.config offset count
          entry.history final.history excluded := by
  intro count
  induction count with
  | zero =>
      intro Γ O program prefixed refs revelations registry embedding before offset compiled native
        inputs reachable entry inherited agree guards failures sameRevelations unique ordered
        completed
      refine ⟨entry, inherited, agree, guards, failures, sameRevelations, ?_, .refl, ?_⟩
      · intro who
        simp only [Nat.not_lt_zero, false_and, exists_false, or_false]
      · intro _actions
        exact RecordedSourceHistory.empty setup.program mode native.native.config offset
          entry.history inherited
  | succ count ih =>
      intro Γ O program prefixed refs revelations registry embedding before offset compiled native
        inputs reachable entry inherited agree guards failures sameRevelations unique ordered
        completed
      cases program with
      | ret _ => exact prefixed.elim
      | sample _ _ _ _ => exact prefixed.elim
      | commit _ _ _ _ _ => exact prefixed.elim
      | @reveal Γ O published owner name payload fresh source unresolved next =>
          subst revelations
          let zero : Fin (eventCount (.reveal published owner name fresh source unresolved next)) :=
            ⟨0, by simp only [eventCount]; omega⟩
          let event := embedding.event zero
          have outputEq : ((toEventGraph setup.program).withMode mode).outputLayout event =
              .publication payload := by
            change outputLayout setup.program (embedding.event zero) = .publication payload
            simpa only [zero, outputLayout, Fin.mk_zero, Fin.cases_zero] using
              embedding.layout_eq zero
          have codeEq : cast (congrArg (EventCode (graphLayout setup.program)) outputEq)
              ((toEventGraph setup.program).nodes event) =
              .resolve owner payload (refs.get source)
                (compileChecks (published := published) refs registry
                  entry.revelations source) := by
            simpa only [event, zero, compileRankedNodes, outputLayout, Fin.mk_zero, Fin.cases_zero]
              using compiled.nodeEq zero
          have rankEq : event.val = offset := by
            simpa only [zero, Nat.add_zero] using compiled.rankEq zero
          have acting : ((toEventGraph setup.program).withMode mode).actor? event = some owner :=
            (EventCode.actor_cast outputEq _).symm.trans (congrArg EventCode.actor codeEq)
          have headDone := completed zero (by change 0 < count + 1; omega)
          have suppressed : owner ∈ inherited →
              (⟨.inr event, outputEq⟩ : FieldRef (graphLayout setup.program)
                (.publication payload)).get? native.native.config.store = some .failure := by
            intro inactive
            have failed := ordered event owner (by omega)
              (by rw [outputEq]; trivial) acting headDone (Or.inl inactive)
            obtain ⟨disclose, action, recorded, actual, headAgree, _⟩ :=
              completed_reveal_source_successor native.native.config reachable event headDone
                outputEq refs entry registry source codeEq agree guards failures unique
            have stored := headAgree HasVar.here
            have failedValue := (publication_failure_iff_read native.native event
              (refs.get source) _ outputEq codeEq _ stored).mp failed
            exact stored.trans (congrArg some failedValue)
          obtain ⟨disclose, action, after, nextExcluded, recorded, actual, oneStep, nextAgree,
            nextGuards, nextFailures, nextRevelations, nextHistory, nextExcludedEq⟩ :=
            completed_reveal_recovery_successor fresh source unresolved next
              native.native.config reachable event headDone outputEq refs entry registry inherited
              codeEq agree guards failures unique suppressed
          let tailEmbedding := embedding.tail next (by simp only [eventCount]) (fun _ => rfl)
          let tailRefs := refs.cons (name := published) (cell := .publication payload)
            (⟨.inr event, outputEq⟩ : FieldRef (graphLayout setup.program) (.publication payload))
          have tailBefore : ContextRefsBefore tailRefs tailEmbedding := by
            intro readName cell selected remaining
            cases selected with
            | here =>
                change (embedding.event zero).val < (embedding.event (Fin.succ remaining)).val
                apply embedding.strictMono
                change 0 < remaining.val + 1
                omega
            | there selected => exact before selected (Fin.succ remaining)
          have nextCompiled : CompiledSuffix setup.program next tailRefs after.revelations
              registry.weaken tailEmbedding tailBefore (offset + 1) := by
            rw [nextRevelations]
            exact compiled.revealTail setup.program fresh source unresolved next refs
              entry.revelations registry embedding before offset
          have members : ∀ who, who ∈ nextExcluded ↔ who ∈ inherited ∨
              (who = owner ∧ native.native.PublicFailure event) := by
            intro who
            have stored : (⟨.inr event, outputEq⟩ : FieldRef (graphLayout setup.program)
                (.publication payload)).get? native.native.config.store =
                some (after.state.get HasVar.here) := nextAgree HasVar.here
            have failedIff := publication_failure_iff_read native.native event
              (refs.get source) _ outputEq codeEq _ stored
            rw [nextExcludedEq]
            cases value : after.state.get HasVar.here with
            | failure =>
                have failed := failedIff.mpr value
                simp only [Finset.mem_insert, failed, and_true]
                exact or_comm
            | success value =>
                have notFailed : ¬ native.native.PublicFailure event := by
                  rw [failedIff, value]
                  simp only [reduceCtorEq, not_false_eq_true]
                simp only [notFailed, and_false, or_false]
          have nextOrdered := ordered.raise event rankEq acting nextExcluded members
          have nextUnique : (((published, CellTy.publication payload) :: Γ).map Prod.fst).Nodup :=
            List.nodup_cons.mpr ⟨fresh, unique⟩
          have nextCompleted : ∀ index : Fin (eventCount next), index.val < count →
              tailEmbedding.event index ∈ native.native.config.cut.completed := by
            intro index inside
            exact completed (Fin.succ index) (by simp only [Fin.val_succ]; omega)
          obtain ⟨final, excluded, finalAgree, finalGuards, finalFailures, finalRevelations,
            finalMembers, path, word⟩ := ih next prefixed tailRefs after.revelations registry.weaken
              tailEmbedding tailBefore (offset + 1) nextCompiled native reachable after
              nextExcluded nextAgree nextGuards nextFailures rfl nextUnique nextOrdered
              nextCompleted
          refine ⟨final, excluded, finalAgree, finalGuards, finalFailures, ?_, ?_, ?_, ?_⟩
          · simpa only [revealTailRevelations, nextRevelations] using finalRevelations
          · intro who
            rw [finalMembers, members]
            constructor
            · rintro ((old | ⟨rfl, failed⟩) | ⟨index, inside, actor, failed⟩)
              · exact Or.inl old
              · exact Or.inr ⟨zero, by change 0 < count + 1; omega, acting, failed⟩
              · exact Or.inr ⟨Fin.succ index, by simp only [Fin.val_succ]; omega, actor, failed⟩
            · rintro (old | ⟨index, inside, actor, failed⟩)
              · exact Or.inl (Or.inl old)
              · by_cases first : index.val = 0
                · have same : index = zero := Fin.ext first
                  subst index
                  have sameOwner : who = owner := Option.some.inj (actor.symm.trans acting)
                  exact Or.inl (Or.inr ⟨sameOwner, failed⟩)
                · let later : Fin (eventCount next) := ⟨index.val - 1, by
                    have bounded := index.isLt
                    simp only [eventCount] at bounded
                    omega⟩
                  have same : Fin.succ later = index := Fin.ext (by
                    simp only [Fin.val_succ, later]
                    omega)
                  rw [← same] at actor failed
                  exact Or.inr ⟨later, by dsimp only [later]; omega, actor, failed⟩
          · have lifted := Relation.ReflTransGen.lift
              (fun state : ProtocolState next × Finset Player => (Sum.inr state.1, state.2))
              (p := fun left right =>
                ¬ ProtocolState.terminal
                  (.reveal published owner name fresh source unresolved next) left.1 ∧
                ProtocolState.atCommit
                  (.reveal published owner name fresh source unresolved next) left.1 = false ∧
                ∃ joint, right ∈ (ProtocolState.recoveryStep
                  (.reveal published owner name fresh source unresolved next)
                  left.1 left.2 joint).support)
              (by
                intro left right step
                obtain ⟨running, notCommit, joint, supported⟩ := step
                refine ⟨running, notCommit, joint, ?_⟩
                exact (PMF.mem_support_map_iff _ _ _).mpr ⟨right, supported, rfl⟩)
              _ _ path
            apply Relation.ReflTransGen.head ?_ lifted
            refine ⟨(fun impossible => impossible), rfl,
              Function.update (fun _ => none) owner
                (some ⟨.reveal owner name disclose, false⟩), ?_⟩
            dsimp only [Prod.fst, Prod.snd, ProtocolState.entry]
            rw [oneStep]
            exact (PMF.mem_support_pure_iff _ _).mpr rfl
          · intro actions
            have tailActions : ∀ index action,
                decodeEventAction setup.program (tailEmbedding.event index) action =
                  decodeEventAction next index
                    (cast (congrArg EventField.Action (tailEmbedding.layout_eq index)) action) := by
              intro index action
              have current := actions (Fin.succ index) action
              dsimp only [tailEmbedding]
              simpa only [decodeEventAction, Fin.cases_succ, OutputEmbedding.tail,
                Fin.cast_eq_self] using current
            have decoded : decodeEventAction setup.program event action =
                some (.reveal owner name disclose) := by
              have encoded := actions zero action
              have returned : cast (congrArg EventField.Action (embedding.layout_eq zero)) action =
                  disclose := actual
              rw [returned] at encoded
              change decodeEventAction setup.program (embedding.event zero) action = _
              simpa only [decodeEventAction, zero, Fin.mk_zero, Fin.cases_zero] using encoded
            have appended : ∀ who, who ∉ excluded → after.history who =
                (Function.update entry.history owner
                  (entry.history owner ++ [.reveal owner name disclose])) who := by
              intro who survives
              by_cases inactive : owner ∈ inherited
              · have different : who ≠ owner := by
                  intro same
                  subst who
                  exact survives ((finalMembers owner).mpr
                    (Or.inl ((members owner).mpr (Or.inl inactive))))
                rw [nextHistory, ite_eq_left inactive, Function.update_of_ne different]
              · rw [nextHistory, ite_eq_right inactive]
            exact RecordedSourceHistory.cons setup.program mode native.native.config offset count
              entry.history after.history final.history excluded ⟨event, action⟩ recorded rankEq
              (.reveal owner name disclose) decoded appended (word tailActions)


end Vegas
