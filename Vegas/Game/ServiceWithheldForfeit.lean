/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ServiceRevealCongruence
import Vegas.Source.Forfeit

/-! # A withheld disclosure is a forfeit

The deviator withholds when one of its disclosures completes with a decision
other than disclosing exactly when its opening is effective
(`Vegas.DeviatorWithheld`). Either way the disclosure publishes a failure: a
refusal always does, and an opening that is not effective does too
(`Vegas.DeviatorWithheld.failure`). Every disclosure of the program is a reveal
cell of its terminal context, read from that disclosure's output
(`Vegas.terminalRefsWith_revealCell`), so on a completed configuration the
terminal readout records a failed reveal of the deviator
(`Vegas.DeviatorWithheld.failedReveals_pos`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open EventGraphRuntime

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

section Compile

omit [DecidableEq Player] [IExpr.ResultTypes L] in
/-- A refusal to disclose publishes a failure. -/
theorem resolveOutput?_false {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {owner : Player} {payload : L.Ty}
    (binding : EventGraph.FieldRef layout (.binding owner payload))
    (checks : List (EventGraph.GuardCheck layout payload)) (store : EventGraph.Store layout)
    {result : PublicationResult (L.Val payload)}
    (resolved : EventGraph.EventCode.resolveOutput? binding checks false store = some result) :
    result = .failure := by
  unfold EventGraph.EventCode.resolveOutput? at resolved
  cases bound : binding.get? store with
  | none => simp [bound] at resolved
  | some value =>
      cases accepted : EventGraph.GuardCheck.allAccepted? checks store .failure with
      | none => simp [bound, accepted] at resolved
      | some verdict =>
          simp only [bound, accepted, Bool.false_eq_true, ↓reduceIte, ite_self, Option.bind_eq_bind,
            Option.bind_some, Option.pure_def, Option.some.injEq] at resolved
          exact resolved.symm

/-- Terminal references of an initial cell read its initial reference. -/
theorem terminalRefsWith_get_terminalRef {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} {name : VarId} {cell : CellTy Player L} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (source : HasVar Γ name cell),
      (terminalRefsWith program refs outputs).get (terminalRef program source) =
        refs.get source
  | _, _, .ret _, _, _, _ => rfl
  | _, _, .sample _ _ _ next, _, _, source =>
      terminalRefsWith_get_terminalRef next _ _ (.there source)
  | _, _, .commit _ _ _ _ next, _, _, source =>
      terminalRefsWith_get_terminalRef next _ _ (.there source)
  | _, _, .reveal _ _ _ _ _ _ next, _, _, source =>
      terminalRefsWith_get_terminalRef next _ _ (.there source)

/-- **Every disclosure is a reveal cell.** Each publication event of a program
is a reveal cell of its terminal context, owned by the event's owner, whose
terminal reference reads the event's output. -/
theorem terminalRefsWith_revealCell {Field : Type} [DecidableEq Field]
    {layout : Field → EventGraph.EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, EventGraph.FieldRef layout (outputLayout program event))
      (event : Fin (eventCount program)) {payload : L.Ty},
      outputLayout program event = .publication payload →
      ∃ cell ∈ revealCells program, eventOwner? program event = some cell.owner ∧
        ((terminalRefsWith program refs outputs).get cell.cell).field = (outputs event).field
  | _, _, .ret _, _, _, event, _, _ => nomatch event
  | _, _, .sample _ _ _ next, refs, outputs, event, payload, layoutEq => by
      refine Fin.cases (fun layoutEq => ?_) (fun later layoutEq => ?_) event layoutEq
      · simp [outputLayout] at layoutEq
      · exact terminalRefsWith_revealCell next _ (fun tailEvent => outputs (Fin.succ tailEvent))
          later layoutEq
  | _, _, .commit _ _ _ _ next, refs, outputs, event, payload, layoutEq => by
      refine Fin.cases (fun layoutEq => ?_) (fun later layoutEq => ?_) event layoutEq
      · simp [outputLayout] at layoutEq
      · exact terminalRefsWith_revealCell next _ (fun tailEvent => outputs (Fin.succ tailEvent))
          later layoutEq
  | _, _, .reveal published owner _ _ _ _ next, refs, outputs, event, payload, layoutEq => by
      refine Fin.cases (fun _ => ?_) (fun later layoutEq => ?_) event layoutEq
      · refine ⟨⟨owner, _, published, terminalRef next .here⟩, List.mem_cons_self .., rfl, ?_⟩
        exact congrArg EventGraph.FieldRef.field
          (terminalRefsWith_get_terminalRef next _ _ .here)
      · obtain ⟨cell, member, owned, field⟩ := terminalRefsWith_revealCell next _
          (fun tailEvent => outputs (Fin.succ tailEvent)) later layoutEq
        exact ⟨cell, List.mem_cons_of_mem _ member, owned, field⟩

/-- A reveal cell of a player holding a failure is a failed reveal of that
player. -/
theorem failedReveals_pos_of_failure {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (who : Player)
    (terminal : State L program.terminalCtx) (cell : RevealCell program.terminalCtx)
    (member : cell ∈ revealCells program) (owned : cell.owner = who)
    (failed : terminal.get cell.cell = .failure) :
    0 < failedReveals program who (publicOutcome program terminal) := by
  unfold failedReveals
  apply List.length_pos_of_mem (a := cell)
  rw [List.mem_filter]
  refine ⟨member, ?_⟩
  simp [owned, RevealCell.failed, publicOutcome, sourcePublicEnv_get_publicRef, failed,
    PublicationResult.isSuccess]

end Compile

variable {setup : Setup (Player := Player) (L := L)} {mode : EventGraph.ExecutionMode}

/-- A disclosure not yet completed counts as opened. -/
theorem OpenedAt.of_not_completed (config : (serviceGraph setup mode).Config)
    {event : (serviceGraph setup mode).EventId} (pending : event ∉ config.cut.completed) :
    OpenedAt config event := by
  unfold OpenedAt
  cases nodeView (serviceGraph setup mode) event with
  | bind => trivial
  | sample => trivial
  | resolve owner payload binding checks outputEq codeEq =>
      intro action member
      exact (pending ((config.history_exact event).mp (List.mem_map_of_mem member))).elim

/-- At a configuration with none of the deviator's disclosures completed, the
deviator has not withheld. -/
theorem not_deviatorWithheld_of_fresh {who : Player} (config : (serviceGraph setup mode).Config)
    (fresh : ∀ event, (serviceGraph setup mode).actor? event = some who →
      event ∉ config.cut.completed) :
    ¬ DeviatorWithheld who config := by
  rintro ⟨event, owned, notOpened⟩
  exact notOpened (OpenedAt.of_not_completed config (fresh event owned))

/-- **A withheld disclosure publishes a failure.** Along a run from a
configuration at which none of the deviator's disclosures is completed, a
withheld disclosure of the deviator has a failure as its output. -/
theorem DeviatorWithheld.failure {who : Player}
    {start final : (serviceGraph setup mode).Config} (reach : ConfigReaches setup start final)
    (fresh : ∀ event, (serviceGraph setup mode).actor? event = some who →
      event ∉ start.cut.completed)
    (withheld : DeviatorWithheld who final) :
    ∃ event, (serviceGraph setup mode).actor? event = some who ∧
      ∃ payload, ∃ outputEq : (serviceGraph setup mode).outputLayout event = .publication payload,
        (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (serviceGraph setup mode).layout
          (.publication payload)).get? final.store = some .failure := by
  obtain ⟨event, owned, notOpened⟩ := withheld
  refine ⟨event, owned, ?_⟩
  unfold OpenedAt at notOpened
  cases node : nodeView (serviceGraph setup mode) event with
  | bind => rw [node] at notOpened; exact (notOpened trivial).elim
  | sample => rw [node] at notOpened; exact (notOpened trivial).elim
  | resolve owner payload binding checks outputEq codeEq =>
      rw [node] at notOpened
      dsimp only at notOpened
      simp only [not_forall] at notOpened
      obtain ⟨action, member, mismatch⟩ := notOpened
      have output := reach.resolve_output member (fresh event owned) (outputEq := outputEq)
        (codeEq := codeEq)
      have done : event ∈ final.cut.completed :=
        (final.history_exact event).mp (List.mem_map_of_mem member)
      have present := (final.output_available event).mpr done
      rw [output, Option.isSome_map] at present
      obtain ⟨result, resolved⟩ := Option.isSome_iff_exists.mp present
      have failed : result = PublicationResult.failure := by
        cases decision : (cast (congrArg EventGraph.EventField.Action outputEq) action : Bool)
        · rw [decision] at resolved
          exact resolveOutput?_false binding checks final.store resolved
        · rw [decision] at mismatch resolved
          cases result with
          | failure => rfl
          | success value =>
              exact (mismatch ⟨fun _ => ⟨value, resolved⟩, fun _ => rfl⟩).elim
      refine ⟨payload, outputEq, ?_⟩
      simp only [EventGraph.FieldRef.get?]
      change cast _ (final.outputs event) = _
      rw [output, resolved, failed, Option.map_some]
      have castSome {A B : Type} (same : A = B) (value : A) :
          cast (congrArg Option same) (some value) = some (cast same value) := by
        cases same
        rfl
      rw [castSome (congrArg EventGraph.EventField.Value outputEq)]
      have castInverse {A B : Type} (same : A = B) (value : B) :
          cast same (cast same.symm value) = value := by
        cases same
        rfl
      exact congrArg some (castInverse (congrArg EventGraph.EventField.Value outputEq) _)

/-- **A withheld disclosure is a failed reveal.** On a completed configuration
reached from one at which none of the deviator's disclosures is completed, if
the deviator withheld, the terminal readout decodes to a state recording a
failed reveal of the deviator. -/
theorem DeviatorWithheld.failedReveals_pos {who : Player}
    {start final : (serviceGraph setup mode).Config} (reach : ConfigReaches setup start final)
    (fresh : ∀ event, (serviceGraph setup mode).actor? event = some who →
      event ∉ start.cut.completed)
    (complete : final.cut.IsPrefix (serviceGraph setup mode).order.eventCount)
    (withheld : DeviatorWithheld who final) :
    ∃ terminal, decodeState? (terminalRefs setup.program) final.store = some terminal ∧
      0 < failedReveals setup.program who (publicOutcome setup.program terminal) := by
  have available : ∀ field, (final.store field).isSome = true := by
    intro field
    cases field with
    | inl input => rfl
    | inr event =>
        exact (final.output_available event).mpr ((complete.2 event).mpr event.isLt)
  obtain ⟨terminal, decoded⟩ := Option.isSome_iff_exists.mp
    (decodeState?_isSome_of_available (terminalRefs setup.program) final.store available)
  refine ⟨terminal, decoded, ?_⟩
  have agree : (terminalRefs setup.program).Agrees terminal final.store :=
    decodeState?_agrees _ _ _ decoded
  obtain ⟨event, owned, payload, outputEq, failed⟩ := withheld.failure reach fresh
  obtain ⟨cell, member, cellOwned, field⟩ := terminalRefsWith_revealCell setup.program
    (ContextRefs.initial setup.context (outputLayout setup.program)) (outputRef setup.program)
    event (payload := payload) outputEq
  have ownerIs : cell.owner = who := by
    rw [eventOwner?_eq_actor] at cellOwned
    exact Option.some.inj (cellOwned.symm.trans owned)
  apply failedReveals_pos_of_failure setup.program who terminal cell member ownerIs
  have read := agree cell.cell
  obtain ⟨cellOwner, cellPayload, cellName, cellRef⟩ := cell
  dsimp only at read field ⊢
  change ((terminalRefs setup.program).get cellRef).field = .inr event at field
  have layoutEq := ((terminalRefs setup.program).get cellRef).layout_eq
  rw [field] at layoutEq
  change (serviceGraph setup mode).outputLayout event = _ at layoutEq
  rw [outputEq] at layoutEq
  cases layoutEq
  have same : (terminalRefs setup.program).get cellRef =
      (⟨.inr event, outputEq⟩ : EventGraph.FieldRef (serviceGraph setup mode).layout
        (.publication payload)) := by
    cases selected : (terminalRefs setup.program).get cellRef with
    | mk selectedField selectedLayout =>
        rw [selected] at field
        cases field
        rfl
  rw [same, failed] at read
  exact (Option.some.inj read).symm

end Vegas
