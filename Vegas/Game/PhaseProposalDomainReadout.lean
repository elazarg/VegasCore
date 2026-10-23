/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.PhaseRecoveryDomainValue

/-! # Every typed payload occurs in the actual decoded source domain -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L]

/-- The reverse direction of the existing decoded-view action correspondence,
restricted to usable binding values. This follows the static source syntax,
not a source or runtime execution. -/
theorem decodeEventView_binding_value {Field : Type} {layout : Field → EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, FieldRef layout (outputLayout program event)) (who : Player)
      (event : Fin (eventCount program)) (store : Store layout) (past : List (OwnAction Player L))
      (view : ProtocolView who program),
      decodeEventView? program refs outputs who event store past = some view →
      ∀ (owner : Player) (payload : L.Ty)
        (binding : outputLayout program event = .binding owner payload) (value : L.Val payload),
      ∃ action, decodeEventAction program event
          (cast (congrArg EventField.Action binding.symm) (.success value)) = some action ∧
        action ∈ ProtocolView.available who program (CommitmentInterface.forfeiture program) view ∧
        ¬ action.IsFailure := by
  intro Γ O program
  induction program with
  | ret => intro refs outputs who event; exact Fin.elim0 event
  | sample name fresh law next ih =>
      intro refs outputs who event store past view decoded owner payload binding value
      refine Fin.cases ?_ ?_ event decoded binding
      · intro decoded binding
        cases binding
      · intro tail decoded binding
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who tail store past later present owner payload binding value
  | @commit Γ O name actor ty fresh guard next ih =>
      intro refs outputs who event store past view decoded owner payload binding value
      refine Fin.cases ?_ ?_ event decoded binding
      · intro decoded binding
        obtain ⟨observation, _present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        obtain ⟨rfl, rfl⟩ := EventField.binding.inj binding
        refine ⟨.commit actor name ty (.success value), rfl, ?_, ?_⟩
        · exact ⟨.success value, trivial, rfl⟩
        · intro impossible
          cases impossible
      · intro tail decoded binding
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who tail store past later present owner payload binding value
  | reveal published actor name fresh source unresolved next ih =>
      intro refs outputs who event store past view decoded owner payload binding value
      refine Fin.cases ?_ ?_ event decoded binding
      · intro decoded binding
        cases binding
      · intro tail decoded binding
        obtain ⟨later, present, rfl⟩ := Option.map_eq_some_iff.mp decoded
        exact ih _ _ who tail store past later present owner payload binding value

/-- At a decoded virtual binding query every actual payload is the image of
an ordinary source choice. Erasing own tags or correcting the current omission
controls does not create an unsupported native value. -/
theorem phaseRecoveryDomainValue_surjective
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
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
    Function.Surjective (fun choice : setup.CommitRecoveryValueChoice who info =>
      phaseRecoveryDomainValue setup mode event who payload binding choice.val.val) := by
  intro value
  obtain ⟨action, decodes, available, good⟩ := decodeEventView_binding_value setup.program refs
    outputs who event store past view decoded who payload binding value
  let move : CommitRecoveryMove Player L := ⟨action, false⟩
  have legal : setup.commitRecoveryModel.menu who info (some move) := by
    refine ⟨active, ?_⟩
    rw [typed]
    change action ∈ ProtocolView.available who setup.program
        (CommitmentInterface.forfeiture setup.program)
        (ProtocolView.virtualBindings who (setup.context.map Prod.fst).toFinset
          setup.program view) ∧ _
    refine ⟨?_, ?_⟩
    · rw [ProtocolView.available_virtualBindings]
      exact available
    · split <;> simp only [move, Bool.false_eq_true, false_implies]
  let choice : setup.CommitRecoveryValueChoice who info :=
    ⟨⟨some move, legal⟩, by
      intro other selected
      cases Option.some.inj selected
      exact ⟨rfl, good⟩⟩
  have encoded := encodeEventAction?_decodeEventAction_eq_some setup.program event _ action decodes
  have data : phaseRecoveryBindingData setup mode event who payload binding choice.val.val =
      (.success value, false) := by
    simp only [choice, move, phaseRecoveryBindingData, Option.elim_some, Bool.false_eq_true,
      ↓reduceIte, Option.bind_some, encoded, Option.map_some, Option.getD_some]
    simp only [cast_cast, cast_eq]
  refine ⟨choice, ?_⟩
  exact congrArg (fun pair : PublicationResult (L.Val payload) × Bool => match pair.1 with
    | .failure => L.someValue payload
    | .success result => result) data

/-- A full ordinary domain law therefore remains full after actual payload
readout; no global finite type of expressions or raw values is required. -/
theorem phaseRecoveryDomainValue_fullSupport
    (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
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
    (values : PMF (setup.CommitRecoveryValueChoice who info)) (full : FullSupport values) :
    FullSupport (values.map fun choice =>
      phaseRecoveryDomainValue setup mode event who payload binding choice.val.val) := by
  intro value
  obtain ⟨choice, same⟩ := phaseRecoveryDomainValue_surjective setup mode refs outputs who event
    payload binding store past view decoded info typed active value
  exact (PMF.mem_support_map_iff _ _ _).mpr ⟨choice, full choice, same⟩

end Vegas
