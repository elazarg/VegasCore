/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketForced

/-! # Failures in typed source prefix readouts

Typed decoding retains the public default history and records failed binding
and publication cells at their source positions. These properties concern the
stored result independently of the requested graph action. Action-level
failure diagnostics separately retain public omission and accepted bad bindings.
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- An action choice with no successful binding and no disclosure. Omission
and an accepted unopenable binding remain distinct choices. -/
def Failing (choice : Option (OwnAction Player L)) : Prop :=
  (∀ owner name payload result, choice = some (.commit owner name payload result) →
    result.getD .failure = .failure) ∧ OwnAction.disclosure choice = false

/-- Omission and accepted unopenable binding actions both incur failure debt. -/
theorem decodeEventAction_failing_binding {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (bound : count < eventCount program) {owner : Player} {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .binding owner payload)
      (choice : Option (PublicationResult (L.Val payload))),
      choice.getD .failure = .failure →
      Failing (decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm)
          choice)) := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound owner payload outputEq choice failed
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq choice failed
  | commit name commitOwner fresh guard next ih =>
      intro count bound owner payload outputEq choice failed
      cases count with
      | zero =>
          change EventGraph.EventField.binding commitOwner _ = _ at outputEq
          obtain ⟨rfl, rfl⟩ := EventGraph.EventField.binding.inj outputEq
          refine ⟨fun actor actorName actorPayload result chosen => ?_, rfl⟩
          cases chosen
          exact failed
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq choice failed
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound owner payload outputEq choice failed
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq choice failed

/-- The decoded action of a publication event completed with withholding is
failing. -/
theorem decodeEventAction_failing_publication {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (bound : count < eventCount program) {payload : L.Ty}
      (outputEq : outputLayout program ⟨count, bound⟩ = .publication payload),
      Failing (decodeEventAction program ⟨count, bound⟩
        (cast (congrArg EventGraph.EventField.Action outputEq.symm) false)) := by
  induction program with
  | ret _ =>
      intro count bound
      simp [eventCount] at bound
  | sample _ _ _ next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | commit name commitOwner fresh guard next ih =>
      intro count bound payload outputEq
      cases count with
      | zero => cases outputEq
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq
  | reveal published revealOwner name fresh source unresolved next ih =>
      intro count bound payload outputEq
      cases count with
      | zero =>
          refine ⟨fun actor actorName actorPayload result chosen => ?_, rfl⟩
          cases Option.some.inj chosen
      | succ count => exact ih count (Nat.lt_of_succ_lt_succ bound) outputEq

namespace ProtocolState

/-- No reveal has failed at a program's entry. -/
theorem not_revealFailed_entry (who : Player) {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) :
    ¬ RevealFailed who program (entry program config) := by
  cases program <;> exact fun failed => failed

end ProtocolState

/-- Decoding a later source point preserves agreement for every cell of the
program's original context. -/
theorem decodeSourcePrefix?_base_agrees {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count
        store history defaults =
        some point → refs.Agrees (ProtocolState.base program point) store
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨cells, cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      rw [ProtocolState.base_entry]
      exact decodeState?_agrees refs store cells cellsDecoded
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded => by
      cases program with
      | ret _ => simp [decodeSourcePrefix?] at decoded
      | sample _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro source
          exact decodeSourcePrefix?_base_agrees count next _ _ _ _ store history defaults rest
            restDecoded (.there source)
      | commit _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro source
          exact decodeSourcePrefix?_base_agrees count next _ _ _ _ store history defaults rest
            restDecoded (.there source)
      | reveal _ _ _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          intro source
          exact decodeSourcePrefix?_base_agrees count next _ _ _ _ store history defaults rest
            restDecoded (.there source)

/-- Every failed source reveal at a decoded point is reflected in an earlier
publication output. In particular, nonfailed earlier outputs rule it out. -/
theorem not_revealFailed_of_decodeSourcePrefix? {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ (count : Nat) {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (point : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count
        store history defaults =
        some point →
      (∀ event : Fin (eventCount program), event.val < count → ∀ payload
        (outputEq : outputLayout program event = .publication payload),
        cast (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value) outputEq)
          ((outputs event).get? store) ≠ some .failure) →
      ∀ who, ¬ ProtocolState.RevealFailed who program point
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded,
      _clean, who => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨cells, _cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact ProtocolState.not_revealFailed_entry who program _
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded, clean, who => by
      cases program with
      | ret _ => simp [decodeSourcePrefix?] at decoded
      | sample _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          apply not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history defaults
            rest
            restDecoded ?_ who
          intro event earlier payload outputEq
          exact clean event.succ (by simpa using Nat.succ_lt_succ earlier) payload outputEq
      | commit _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          apply not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history defaults
            rest
            restDecoded ?_ who
          intro event earlier payload outputEq
          exact clean event.succ (by simpa using Nat.succ_lt_succ earlier) payload outputEq
      | reveal published owner name fresh selected unresolved next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have later := not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history
            defaults rest restDecoded (fun event earlier payload outputEq =>
              clean event.succ (by simpa using Nat.succ_lt_succ earlier) payload outputEq) who
          rintro (⟨_sameOwner, failed⟩ | failed)
          · have agrees := decodeSourcePrefix?_base_agrees count next _ _ _ _ store history
              defaults rest restDecoded HasVar.here
            have noFailure := clean ⟨0, by simp [eventCount]⟩ (by simp) _ rfl
            apply noFailure
            simpa [ContextRefs.cons, cellValue, failed] using agrees
          · exact later failed

namespace ProtocolState

/-- **A stored failed publication is a failed reveal.** A point decoded past a
reveal of `who` whose stored publication is a failure shows `who`'s reveal
failed. -/
theorem revealFailed_of_decode_failure {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (state : ProtocolState program) (bound : count < eventCount program) (who : Player)
      (payload : L.Ty) (publication : outputLayout program ⟨count, bound⟩ = .publication payload),
      decodeSourcePrefix? program refs registry revelations outputs (count + 1)
        store history defaults =
          some state →
      eventOwner? program ⟨count, bound⟩ = some who →
      (outputs ⟨count, bound⟩).get? store = some (cast
        (congrArg EventGraph.EventField.Value publication.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) →
      RevealFailed who program state := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history defaults state bound who payload
        publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ bound) who
            payload publication restDecoded owned read
  | commit name owner fresh guard next ih =>
      intro count refs registry revelations outputs store history defaults state bound who payload
        publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ bound) who
            payload publication restDecoded owned read
  | reveal published owner name fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history defaults state bound who payload
        publication decoded owned read
      cases count with
      | zero =>
          cases Option.some.inj owned
          cases publication
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          obtain ⟨cells, cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp restDecoded
          refine Or.inl ⟨rfl, ?_⟩
          rw [base_entry]
          unfold decodeState? at cellsDecoded
          erw [read] at cellsDecoded
          obtain ⟨head, headEq, rest⟩ := Option.bind_eq_some_iff.mp cellsDecoded
          obtain ⟨tail, _, cellsEq⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj headEq
          cases Option.some.inj cellsEq
          rfl
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact Or.inr (ih count _ _ _ _ store history defaults rest
            (Nat.lt_of_succ_lt_succ bound) who payload publication restDecoded owned read)


/-- A failed binding cell at its completed source position is an unresolved
failed binding, independently of the requested graph action. -/
theorem failedBinding_of_decode_failure {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (_unique : (Γ.map Prod.fst).Nodup) (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (state : ProtocolState program) (bound : count < eventCount program) (who : Player)
      (payload : L.Ty) (binding : outputLayout program ⟨count, bound⟩ = .binding who payload),
      decodeSourcePrefix? program refs registry revelations outputs (count + 1)
        store history defaults = some state →
      eventOwner? program ⟨count, bound⟩ = some who →
      (outputs ⟨count, bound⟩).get? store = some (cast
        (congrArg EventGraph.EventField.Value binding.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) →
      FailedBinding who program state := by
  induction program with
  | ret _ =>
      intro _ count _ _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample name fresh law next ih =>
      intro unique count refs registry revelations outputs store history defaults state bound who
        payload binding decoded owned read
      cases count with
      | zero => cases binding
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history defaults rest
            (Nat.lt_of_succ_lt_succ bound) who payload binding restDecoded owned read
  | commit name owner fresh guard next ih =>
      intro unique count refs registry revelations outputs store history defaults state bound who
        payload binding decoded owned read
      cases count with
      | zero =>
          cases Option.some.inj owned
          cases binding
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          obtain ⟨cells, cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp restDecoded
          apply failedBinding_entry
          refine ⟨List.nodup_cons.mpr ⟨fresh, unique⟩,
            name, _, .here, Finset.mem_insert_self _ _, ?_⟩
          unfold decodeState? at cellsDecoded
          erw [read] at cellsDecoded
          obtain ⟨head, headEq, rest⟩ := Option.bind_eq_some_iff.mp cellsDecoded
          obtain ⟨tail, _, cellsEq⟩ := Option.bind_eq_some_iff.mp rest
          cases Option.some.inj headEq
          cases Option.some.inj cellsEq
          rfl
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history defaults rest
            (Nat.lt_of_succ_lt_succ bound) who payload binding restDecoded owned read
  | reveal published owner name fresh source unresolved next ih =>
      intro unique count refs registry revelations outputs store history defaults state bound who
        payload binding decoded owned read
      cases count with
      | zero => cases binding
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          exact Or.inr (ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history
            defaults rest (Nat.lt_of_succ_lt_succ bound) who payload binding restDecoded owned read)

/-- **A failing completion makes its actor owe a failure.** At a point decoded
after `count` events, stepping with a failing action at the event of index
`count`, owned by `who`, makes `who` owe a failure. -/
theorem owesFailure_of_decode_failing {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    (Γ.map Prod.fst).Nodup → ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (state : ProtocolState program) (bound : count < eventCount program) (who : Player)
      (choice : Option (OwnAction Player L)) (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
          some state →
      eventOwner? program ⟨count, bound⟩ = some who → Failing choice →
      target ∈ (step program state (fun _ => choice)).support →
      OwesFailure who program target := by
  induction program with
  | ret _ =>
      intro _ count _ _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro unique count refs registry revelations outputs store history defaults state bound who
        choice target decoded owned failing reached
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history defaults rest
            (Nat.lt_of_succ_lt_succ bound) who choice after read owned failing supported
  | @commit commitCtx commitNames name owner payload fresh guard next ih =>
      intro unique count refs registry revelations outputs store history defaults state bound who
        choice target decoded owned failing reached
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          have failed : (OwnAction.binding owner name payload choice).getD .failure =
              .failure := by
            unfold OwnAction.binding
            split
            · rename_i found
              exact failing.1 _ _ _ _ found.choose_spec
            · rfl
          refine Or.inr ?_
          change FailedBinding owner next (entry next _)
          generalize binding : OwnAction.binding owner name payload choice = result at failed ⊢
          cases result with
          | none =>
              exact failedBinding_entry next _
                (Config.failedBinding_omission _ unique fresh guard commitNames)
          | some result =>
              cases result with
              | failure =>
                  exact failedBinding_entry next _
                    (Config.failedBinding_commit _ unique fresh guard commitNames)
              | success value => cases failed
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history defaults rest
            (Nat.lt_of_succ_lt_succ bound) who choice after read owned failing supported
  | reveal published owner name fresh source unresolved next ih =>
      intro unique count refs registry revelations outputs store history defaults state bound who
        choice target decoded owned failing reached
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same : target = Sum.inr (entry next (revealSuccessor published source
              ⟨cells, registry, revelations, history, defaults⟩ (OwnAction.disclosure choice))) :=
            (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          refine Or.inl (Or.inl ⟨rfl, ?_⟩)
          rw [base_entry, failing.2]
          exact revealSuccessor_result_of_withholding published source _
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          rcases ih (List.nodup_cons.mpr ⟨fresh, unique⟩) count _ _ _ _ store history defaults rest
            (Nat.lt_of_succ_lt_succ bound) who choice after read owned failing supported with
            indebted | failed
          · exact Or.inl (Or.inr indebted)
          · exact Or.inr (Or.inr failed)

end ProtocolState

end Vegas.SourceProgram
