/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.ProtocolState
import GameTheory.Protocol.Information

/-! # Source games as execution protocols

The protocol uses the existing source successor functions. Its legal actions
enforce the commitment interface at every history. The information model gives
policies exactly the existing source view at the current program point.
-/

noncomputable section

namespace Vegas.SourceProgram

open GameTheory.Protocol GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

namespace OwnAction

open Classical in
/-- Decode a correctly addressed source commitment action. The default only
totalizes the function: the execution protocol excludes incorrectly addressed
actions through its availability predicate. -/
def binding (owner : Player) (name : VarId) (payload : L.Ty)
    (action : Option (OwnAction Player L)) : PublicationResult (L.Val payload) :=
  if found : ∃ choice, action = some (.commit owner name payload choice)
  then found.choose else .failure

omit [DecidableEq Player] [IExpr.ResultTypes L] in
@[simp] theorem binding_commit (owner : Player) (name : VarId) (payload : L.Ty)
    (choice : PublicationResult (L.Val payload)) :
    binding owner name payload (some (.commit owner name payload choice)) = choice := by
  have found : ∃ value, some (OwnAction.commit owner name payload choice) =
      some (.commit owner name payload value) := ⟨choice, rfl⟩
  simp only [binding, dite_eq_left found]
  have equality := found.choose_spec
  simpa only [Option.some.injEq, OwnAction.commit.injEq, heq_eq_eq, true_and] using equality.symm

/-- A disclosure decision carries no payload-dependent cast. -/
def disclosure : Option (OwnAction Player L) → Bool
  | some (.reveal _ _ disclose) => disclose
  | _ => false

end OwnAction

namespace ProtocolState

/-- One source transition, using the existing configuration transformers.
Terminal and ill-addressed inputs are totalized here; the protocol's legal
joint-action type prevents their use as transitions. -/
def step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program →
    (Player → Option (OwnAction Player L)) → FinDist (ProtocolState program)
  | _, _, .ret _ => fun config _ => FinDist.pure config
  | _, _, .sample name _ law next => fun state joint =>
      Sum.elim
        (fun config => (L.evalDist law (sourcePublicEnv config.state)).map fun value =>
          Sum.inr (entry next (sampleSuccessor name config value)))
        (fun rest => (step next rest joint).map Sum.inr) state
  | _, _, .commit (payload := payload) name owner _ guard next => fun state joint =>
      Sum.elim
        (fun config => FinDist.pure (Sum.inr (entry next
          (commitSuccessor name guard config
            (OwnAction.binding owner name payload (joint owner))))))
        (fun rest => (step next rest joint).map Sum.inr) state
  | _, _, .reveal published owner _ _ source _ next => fun state joint =>
      Sum.elim
        (fun config => FinDist.pure (Sum.inr (entry next
          (revealSuccessor published source config (OwnAction.disclosure (joint owner))))))
        (fun rest => (step next rest joint).map Sum.inr) state

/-- A value or a withholding decision is always available. Guards constrain
publication, not the admission of a binding action. -/
theorem progress : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (admission : CommitmentInterface program) →
    (state : ProtocolState program) →
    ∃ joint : Player → Option (OwnAction Player L), ∀ who,
      ProtocolView.menu who program admission (observe who program state) (joint who)
  | _, _, .ret _, _, _ => ⟨fun _ => none, fun _ => by simp [ProtocolView.menu,
      ProtocolView.actor]⟩
  | _, _, .sample _ _ _ next, admission, state => by
      cases state with
      | inl config =>
          exact ⟨fun _ => none, fun _ => by
            simp [ProtocolView.menu, ProtocolView.actor, observe]⟩
      | inr rest => exact progress next admission rest
  | _, _, .commit (payload := payload) name owner _ _ next, admission, state => by
      cases state with
      | inl config =>
          refine ⟨fun who => if owner = who then
            some (.commit owner name payload (.success (L.someValue payload))) else none, ?_⟩
          intro who
          by_cases same : owner = who
          · simp only [same, ↓reduceIte, ProtocolView.menu, observe, Sum.elim_inl,
              ProtocolView.actor, ProtocolView.available]
            exact ⟨trivial, .success (L.someValue payload), trivial, rfl⟩
          · simp [same, ProtocolView.menu, observe, ProtocolView.actor]
      | inr rest => exact progress next (fun site => admission (some site)) rest
  | _, _, .reveal _ owner name _ _ _ next, admission, state => by
      cases state with
      | inl config =>
          refine ⟨fun who => if owner = who then some (.reveal owner name false) else none, ?_⟩
          intro who
          by_cases same : owner = who
          · simp only [same, ↓reduceIte, ProtocolView.menu, observe, Sum.elim_inl,
              ProtocolView.actor, ProtocolView.available]
            exact ⟨trivial, false, rfl⟩
          · simp [same, ProtocolView.menu, observe, ProtocolView.actor]
      | inr rest => exact progress next admission rest

end ProtocolState

/-- The actual players are strategic coordinates. Public chance is carried by
the transition kernel at a state with no active player. -/
def executionProtocol {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) : ExecutionProtocol Player where
  State := ProtocolState program
  Action _ := OwnAction Player L
  init := ProtocolState.entry program initial
  active state who :=
    ProtocolView.actor who program (ProtocolState.observe who program state) = some who
  available state who :=
    ProtocolView.available who program admission (ProtocolState.observe who program state)
  terminal := ProtocolState.terminal program
  step state joint := ProtocolState.step program state joint.1
  progress state _ := by
    obtain ⟨joint, legal⟩ := ProtocolState.progress program admission state
    refine ⟨joint, fun who => ?_⟩
    have member := legal who
    cases chosen : joint who <;>
      simpa only [ProtocolView.menu, chosen] using member

theorem protocol_singleMover {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (state : ProtocolState program) {first second : Player}
    (actsFirst : (executionProtocol program admission initial).active state first)
    (actsSecond : (executionProtocol program admission initial).active state second) :
    first = second :=
  Option.some.inj (actsFirst.symm.trans
    ((ProtocolState.actor_observe program state first second).trans actsSecond))

def protocolSignals {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) : InfoSignals (executionProtocol program admission initial) where
  PublicSignal := Unit
  PrivateSignal who := ProtocolView who program
  initialPublic := ()
  initialPrivate who := ProtocolState.observe who program (ProtocolState.entry program initial)
  publicSignal _ := ()
  privateSignal who event := ProtocolState.observe who program event.target
  InfoState who := ProtocolView who program
  initInfo _ view _ := view
  pushInfo _ _ _ view _ := view

/-- The signal carries the existing source view, including retained own
actions. No hidden configuration is inserted into the policy's input. -/
theorem protocol_info {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) (who : Player) :
    ∀ {state} (trace : (executionProtocol program admission initial).Trace state),
      (protocolSignals program admission initial).infoOf who trace =
        ProtocolState.observe who program state
  | _, .start => rfl
  | _, .extend _ _ _ _ => rfl

def informationModel {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
    (initial : Config Player L Γ) :
    InformationModel (executionProtocol program admission initial) where
  toInfoSignals := protocolSignals program admission initial
  menu who := ProtocolView.menu who program admission
  menu_adequate := by
    intro who state trace choice
    rw [protocol_info]
    cases choice <;> rfl

end Vegas.SourceProgram
