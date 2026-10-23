/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryBindingComponent
import Vegas.Source.CommitRecoveryVirtualMenu
import Vegas.Source.CommitRecoveryValueMenu
import Vegas.Compile.EventBindingActionFailure

/-! # Typed domain payloads selected at virtual source binding queries -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Protocol

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)

/-- Read a payload from the exact source action encoder. The default only
totalizes inactive and malformed inputs; genuine domain queries encode values. -/
def phaseRecoveryDomainValue (event : (serviceGraph setup mode).EventId)
    (owner : Player) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding owner payload)
    (move : Option (CommitRecoveryMove Player L)) : L.Val payload :=
  match (phaseRecoveryBindingData setup mode event owner payload binding move).1 with
  | .failure => L.someValue payload
  | .success value => value

/-- Every domain choice at the virtual decoded cursor encodes its own typed
value at the selected physical event, with no omission and no default branch. -/
theorem phaseRecoveryDomainValue_faithful
    {Field : Type} {layout : Field → EventField Player L}
    (refs : ContextRefs layout setup.context)
    (outputs : ∀ event, FieldRef layout (outputLayout setup.program event))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (store : Store layout) (past : List (OwnAction Player L))
    (view : ProtocolView who setup.program)
    (decoded : decodeEventView? setup.program refs outputs who event store past = some view)
    (info : setup.commitRecoveryModel.InfoState who)
    (typed : info.1.1.1 = some (ProtocolView.virtualBindings who
      (setup.context.map Prod.fst).toFinset setup.program view))
    (active : setup.commitRecoveryActive who info.1.1)
    (choice : setup.CommitRecoveryValueChoice who info) :
    phaseRecoveryBindingData setup mode event who payload binding choice.1.1 =
      (.success (phaseRecoveryDomainValue setup mode event who payload binding choice.1.1),
        false) := by
  cases selected : choice.1.1 with
  | none =>
      have inactive := choice.1.2
      rw [selected] at inactive
      exact (inactive active).elim
  | some move =>
      have legal := choice.1.2
      rw [selected] at legal
      have available := legal.2
      change info.1.1.1.elim False _ at available
      rw [typed] at available
      have offered : move.action ∈ ProtocolView.available who setup.program
          (CommitmentInterface.forfeiture setup.program) view := by
        simpa only [ProtocolView.available_virtualBindings] using available.1
      obtain ⟨encoded, decodes⟩ := decodeEventView?_available setup.program refs outputs who
        event store past view decoded move.action offered
      have encoding := encodeEventAction?_decodeEventAction_eq_some setup.program event
        encoded move.action decodes
      have domain := choice.2 move selected
      have good : cast (congrArg EventField.Action binding) encoded ≠ .failure :=
        fun failed => domain.2 ((decodeEventAction_binding_failure_iff setup.program event who
          payload binding encoded move.action decodes).mp failed)
      have data : phaseRecoveryBindingData setup mode event who payload binding (some move) =
          (cast (congrArg EventField.Action binding) encoded, false) := by
        simp only [phaseRecoveryBindingData, Option.elim_some, domain.1, Bool.false_eq_true,
          ↓reduceIte, Option.bind_some, encoding, Option.map_some, Option.getD_some]
      unfold phaseRecoveryDomainValue
      rw [data]
      cases result : cast (congrArg EventField.Action binding) encoded with
      | failure => exact (good result).elim
      | success value => rfl

/-- At a decoded binding cursor, the typed value determines the entire legal
proper domain choice. Mapping the original domain law to typed values therefore
preserves each literal atom, including at historical source queries. -/
theorem phaseRecoveryDomainValue_injective
    {Field : Type} {layout : Field → EventField Player L}
    (refs : ContextRefs layout setup.context)
    (outputs : ∀ event, FieldRef layout (outputLayout setup.program event))
    (who : Player) (event : (serviceGraph setup mode).EventId) (payload : L.Ty)
    (binding : (serviceGraph setup mode).outputLayout event = .binding who payload)
    (store : Store layout) (past : List (OwnAction Player L))
    (view : ProtocolView who setup.program)
    (decoded : decodeEventView? setup.program refs outputs who event store past = some view)
    (info : setup.commitRecoveryModel.InfoState who)
    (typed : info.1.1.1 = some (ProtocolView.virtualBindings who
      (setup.context.map Prod.fst).toFinset setup.program view))
    (active : setup.commitRecoveryActive who info.1.1) :
    Function.Injective (fun choice : setup.CommitRecoveryValueChoice who info =>
      phaseRecoveryDomainValue setup mode event who payload binding choice.val.val) := by
  have read (choice : setup.CommitRecoveryValueChoice who info) :
      ∃ move : CommitRecoveryMove Player L,
        choice.val.val = some move ∧ move.missing = false ∧
        decodeEventAction setup.program event
          (cast (congrArg EventField.Action binding.symm)
            (.success (phaseRecoveryDomainValue setup mode event who payload binding
              choice.val.val))) = some move.action := by
    cases selected : choice.val.val with
    | none =>
        have legal := choice.val.property
        rw [selected] at legal
        exact (legal active).elim
    | some move =>
        have legal := choice.val.property
        rw [selected] at legal
        have available := legal.2
        change info.1.1.1.elim False _ at available
        rw [typed] at available
        have offered : move.action ∈ ProtocolView.available who setup.program
            (CommitmentInterface.forfeiture setup.program) view := by
          simpa only [ProtocolView.available_virtualBindings] using available.1
        obtain ⟨encoded, decodes⟩ := decodeEventView?_available setup.program refs outputs who
          event store past view decoded move.action offered
        have encoding := encodeEventAction?_decodeEventAction_eq_some setup.program event
          encoded move.action decodes
        have proper := choice.property move selected
        have data : phaseRecoveryBindingData setup mode event who payload binding choice.val.val =
            (cast (congrArg EventField.Action binding) encoded, false) := by
          simp only [selected, phaseRecoveryBindingData, Option.elim_some, proper.1,
            Bool.false_eq_true, ↓reduceIte, Option.bind_some, encoding, Option.map_some,
            Option.getD_some]
        have faithful := phaseRecoveryDomainValue_faithful setup mode refs outputs who event
          payload binding store past view decoded info typed active choice
        have result := congrArg Prod.fst (data.symm.trans faithful)
        dsimp only [Prod.fst] at result
        have graphEq : encoded = cast (congrArg EventField.Action binding.symm)
            (.success (phaseRecoveryDomainValue setup mode event who payload binding
              choice.val.val)) := by
          have inverse := congrArg (cast (congrArg EventField.Action binding.symm)) result
          simpa only [cast_cast, cast_eq] using inverse
        refine ⟨move, rfl, proper.1, ?_⟩
        have decodedValue := congrArg (decodeEventAction setup.program event) graphEq
        simpa only [selected] using decodedValue.symm.trans decodes
  intro first second sameValue
  obtain ⟨firstMove, firstSelected, firstProper, firstRead⟩ := read first
  obtain ⟨secondMove, secondSelected, secondProper, secondRead⟩ := read second
  dsimp only at sameValue
  have sameRead := congrArg (fun value : L.Val payload => decodeEventAction setup.program event
    (cast (congrArg EventField.Action binding.symm) (.success value))) sameValue
  have sameAction : firstMove.action = secondMove.action :=
    Option.some.inj (firstRead.symm.trans (sameRead.trans secondRead))
  have sameMove : firstMove = secondMove := by
    cases firstMove with
    | mk firstAction firstMissing =>
      cases secondMove with
      | mk secondAction secondMissing =>
        dsimp only at firstProper secondProper sameAction
        cases firstProper
        cases secondProper
        cases sameAction
        rfl
  apply Subtype.ext
  apply Subtype.ext
  rw [firstSelected, secondSelected, sameMove]

end Vegas
