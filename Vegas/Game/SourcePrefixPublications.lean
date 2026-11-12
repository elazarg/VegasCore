module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Game.OnePacketForced
public import Vegas.Source.IntendedGame
public import Vegas.Source.IntendedForPlayer

@[expose] public section

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

namespace ProtocolView

/-- **Intended actions are not failing.** An intended commitment commits a
value, and an intended reveal discloses. -/
theorem not_failing_of_intendedAvailable (who : Player) : {Γ : SourceCtx Player L} →
    {O : Finset VarId} → (program : SourceProgram Player L Γ O) →
    (view : ProtocolView who program) → (action : OwnAction Player L) →
    action ∈ intendedAvailable who program view → ¬ Failing (some action)
  | _, _, .ret _, _, _, impossible => impossible.elim
  | _, _, .sample _ _ _ next, view, action, member => by
      cases view with
      | inl _ => exact member.elim
      | inr later => exact not_failing_of_intendedAvailable who next later action member
  | _, _, .commit _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          obtain ⟨value, _, rfl⟩ := member
          intro failing
          cases failing.1 _ _ _ _ rfl
      | inr later => exact not_failing_of_intendedAvailable who next later action member
  | _, _, .reveal _ _ _ _ _ _ next, view, action, member => by
      cases view with
      | inl _ =>
          rw [Set.mem_singleton_iff.mp member]
          intro failing
          cases failing.2
      | inr later => exact not_failing_of_intendedAvailable who next later action member

end ProtocolView

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

/-- Failed source reveals of a player occur only at earlier owned publication
outputs. Cleanliness of other players' outputs is unnecessary. -/
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
        store history defaults = some point →
      ∀ who, (∀ event : Fin (eventCount program), event.val < count →
        eventOwner? program event = some who → ∀ payload
        (outputEq : outputLayout program event = .publication payload),
        cast (congrArg (fun kind : EventGraph.EventField Player L => Option kind.Value) outputEq)
          ((outputs event).get? store) ≠ some .failure) →
      ¬ ProtocolState.RevealFailed who program point
  | 0, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded, who, _clean => by
      simp only [decodeSourcePrefix?] at decoded
      obtain ⟨cells, _cellsDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
      exact ProtocolState.not_revealFailed_entry who program _
  | count + 1, _, _, program, refs, registry, revelations, outputs, store, history, defaults, point,
      decoded, who, clean => by
      cases program with
      | ret _ => simp [decodeSourcePrefix?] at decoded
      | sample _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          apply not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history defaults
            rest restDecoded who
          intro event earlier owned payload outputEq
          exact clean event.succ (by simpa using Nat.succ_lt_succ earlier) owned payload outputEq
      | commit _ _ _ _ next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          apply not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history defaults
            rest restDecoded who
          intro event earlier owned payload outputEq
          exact clean event.succ (by simpa using Nat.succ_lt_succ earlier) owned payload outputEq
      | reveal published owner name fresh selected unresolved next =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have later := not_revealFailed_of_decodeSourcePrefix? count next _ _ _ _ store history
            defaults rest restDecoded who (fun event earlier owned payload outputEq =>
              clean event.succ (by simpa using Nat.succ_lt_succ earlier) owned payload outputEq)
          rintro (⟨sameOwner, failed⟩ | failed)
          · have agrees := decodeSourcePrefix?_base_agrees count next _ _ _ _ store history
              defaults rest restDecoded HasVar.here
            have noFailure := clean ⟨0, by simp [eventCount]⟩ (by simp)
              (by simpa [eventOwner?, eventCount, Fin.cases] using congrArg some sameOwner) _ rfl
            apply noFailure
            simpa [ContextRefs.cons, cellValue, failed] using agrees
          · exact later failed

namespace ProtocolState

/-- **A stored failed publication is a failed reveal.** A point decoded after a
reveal of `who` whose stored publication is a failure shows `who`'s reveal
failed. -/
theorem revealFailed_of_decode_failure {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count rank : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (state : ProtocolState program) (bound : count < eventCount program)
      (_completed : count < rank) (who : Player)
      (payload : L.Ty) (publication : outputLayout program ⟨count, bound⟩ = .publication payload),
      decodeSourcePrefix? program refs registry revelations outputs rank
        store history defaults =
          some state →
      eventOwner? program ⟨count, bound⟩ = some who →
      (outputs ⟨count, bound⟩).get? store = some (cast
        (congrArg EventGraph.EventField.Value publication.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))) →
      RevealFailed who program state := by
  induction program with
  | ret _ =>
      intro count rank _ _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count rank refs registry revelations outputs store history defaults state bound
        completed who payload publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          cases rank with
          | zero => omega
          | succ rank =>
              simp only [decodeSourcePrefix?] at decoded
              obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
              exact ih count rank _ _ _ _ store history defaults rest
                (Nat.lt_of_succ_lt_succ bound) (Nat.lt_of_succ_lt_succ completed) who payload
                publication restDecoded owned read
  | commit name owner fresh guard next ih =>
      intro count rank refs registry revelations outputs store history defaults state bound
        completed who payload publication decoded owned read
      cases count with
      | zero => cases publication
      | succ count =>
          cases rank with
          | zero => omega
          | succ rank =>
              simp only [decodeSourcePrefix?] at decoded
              obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
              exact ih count rank _ _ _ _ store history defaults rest
                (Nat.lt_of_succ_lt_succ bound) (Nat.lt_of_succ_lt_succ completed) who payload
                publication restDecoded owned read
  | reveal published owner name fresh source unresolved next ih =>
      intro count rank refs registry revelations outputs store history defaults state bound
        completed who payload publication decoded owned read
      cases rank with
      | zero => omega
      | succ rank =>
          cases count with
          | zero =>
              cases Option.some.inj owned
              cases publication
              simp only [decodeSourcePrefix?] at decoded
              obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
              refine Or.inl ⟨rfl, ?_⟩
              have agrees := decodeSourcePrefix?_base_agrees rank next _ _ _ _ store history
                defaults rest restDecoded HasVar.here
              have sourceRead : some ((base next rest).get HasVar.here) =
                  (outputs ⟨0, bound⟩).get? store := by
                simpa [ContextRefs.cons, cellValue] using agrees.symm
              exact Option.some.inj (sourceRead.trans (by simpa using read))
          | succ count =>
              simp only [decodeSourcePrefix?] at decoded
              obtain ⟨rest, restDecoded, rfl⟩ := Option.map_eq_some_iff.mp decoded
              exact Or.inr (ih count rank _ _ _ _ store history defaults rest
                (Nat.lt_of_succ_lt_succ bound) (Nat.lt_of_succ_lt_succ completed) who payload
                publication restDecoded owned read)


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

private theorem intendedFor_of_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ) (who : Player)
    (holds : IntendedFor who program (entry program config)) : config.IntendedFor who O := by
  cases program <;> exact holds

/-- If an actual owned completion keeps its player intended, its decoded
choice belongs to that player's intended source menu. -/
theorem intendedAvailable_of_decode_intendedFor {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {Γ : SourceCtx Player L}
    {openNames : Finset VarId} (program : SourceProgram Player L Γ openNames) :
    ∀ (count : Nat) (refs : ContextRefs layout Γ)
      (registry : Registry Γ) (revelations : Revelations Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (store : EventGraph.Store layout) (history : History Player L)
      (defaults : DefaultHistory Player)
      (state : ProtocolState program) (bound : count < eventCount program) (actor : Player)
      (action : EventGraph.EventField.Action (outputLayout program ⟨count, bound⟩))
      (target : ProtocolState program),
      decodeSourcePrefix? program refs registry revelations outputs count store history defaults =
          some state →
      IntendedFor actor program state →
      eventOwner? program ⟨count, bound⟩ = some actor →
      target ∈ (step program state
        (fun _ => decodeEventAction program ⟨count, bound⟩ action)).support →
      IntendedFor actor program target →
      ∃ act, decodeEventAction program ⟨count, bound⟩ action = some act ∧
        act ∈ ProtocolView.intendedAvailable actor program (observe actor program state) := by
  induction program with
  | ret _ =>
      intro count _ _ _ _ _ _ _ _ bound
      simp [eventCount] at bound
  | sample _ fresh _ next ih =>
      intro count refs registry revelations outputs store history defaults state bound actor action
        target decoded intended owned reached after
      cases count with
      | zero => cases owned
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨later, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ bound)
            actor action later read intended owned supported after
  | @commit commitCtx commitNames name owner payload fresh guard next ih =>
      intro count refs registry revelations outputs store history defaults state bound actor action
        target decoded intended owned reached after
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change Option (PublicationResult (L.Val payload)) at action
          change ∃ act, some (OwnAction.commit owner name payload action) = some act ∧ _
          have before : (⟨cells, registry, revelations, history, defaults⟩ :
              Config Player L commitCtx).IntendedFor owner commitNames := intended
          have afterConfig : (commitSuccessor name guard
              ⟨cells, registry, revelations, history, defaults⟩ action).IntendedFor owner
                (insert name commitNames) := by
            change IntendedFor owner next (entry next (commitSuccessor name guard
              ⟨cells, registry, revelations, history, defaults⟩
              (OwnAction.binding owner name payload
                (some (.commit owner name payload action))))) at after
            rw [OwnAction.binding_commit] at after
            exact intendedFor_of_entry next _ owner after
          cases action with
          | none =>
              obtain ⟨value, succeeded⟩ := afterConfig.bound .here
              simp [commitSuccessor] at succeeded
          | some result =>
              cases result with
              | failure =>
                  obtain ⟨value, succeeded⟩ := afterConfig.bound .here
                  simp [commitSuccessor, before.active] at succeeded
              | success value =>
                  have prediction := afterConfig.predicted
                    { owner := owner, subject := name, payload := payload, source := .here,
                      guard := guard.weaken }
                    (List.mem_cons_self ..) rfl value
                    (by simp [commitSuccessor, before.active])
                  have accepted : guard.predicts (sourceObserve owner cells) value = true := by
                    simpa only [commitSuccessor, before.active, ite_false, Option.getD_some,
                      SourceGuard.predicts_weaken] using prediction
                  exact ⟨_, rfl, value,
                    Or.inl ((mem_predictedValues_self guard _ value).mpr accepted), rfl⟩
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨later, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ bound)
            actor action later read intended owned supported after
  | @reveal revealCtx revealNames published owner name payload fresh source unresolved next ih =>
      intro count refs registry revelations outputs store history defaults state bound actor action
        target decoded intended owned reached after
      cases count with
      | zero =>
          cases Option.some.inj owned
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨cells, _, rfl⟩ := Option.map_eq_some_iff.mp decoded
          have same := (PMF.mem_support_pure_iff _ _).mp reached
          subst same
          change Bool at action
          change ∃ act, some (OwnAction.reveal owner name action) = some act ∧ _
          have before : (⟨cells, registry, revelations, history, defaults⟩ :
              Config Player L revealCtx).IntendedFor owner revealNames := intended
          have afterConfig : (revealSuccessor published source
              ⟨cells, registry, revelations, history, defaults⟩ action).IntendedFor owner
                (revealNames.erase name) := by
            change IntendedFor owner next (entry next (revealSuccessor published source
              ⟨cells, registry, revelations, history, defaults⟩ action)) at after
            exact intendedFor_of_entry next _ owner after
          cases action with
          | true => exact ⟨_, rfl, rfl⟩
          | false =>
              have active := afterConfig.active
              simp [revealSuccessor, Config.defaulted, DefaultHistory.defaulted,
                DefaultHistory.record, PublicationResult.isFailure] at active
      | succ count =>
          simp only [decodeSourcePrefix?] at decoded
          obtain ⟨rest, read, rfl⟩ := Option.map_eq_some_iff.mp decoded
          simp only [ProtocolState.step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨later, supported, rfl⟩ := reached
          exact ih count _ _ _ _ store history defaults rest (Nat.lt_of_succ_lt_succ bound)
            actor action later read intended owned supported after

end ProtocolState

end Vegas.SourceProgram
