/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.SourceSwapAgreement

/-! # Publications carry their bindings or fail

Every revealed commitment publishes a failure or its own binding
(`Vegas.SourceProgram.PublishesOrFails`): a reveal publishes the binding when
it discloses and every completed guard accepts, and a failure otherwise. This
holds at every source point reached from setup
(`Vegas.SourceProgram.ProtocolState.publishesOrFails_step`), so at the decoded
point of every native history of a response menu
(`Vegas.decodedState_publishesOrFails`). Hence a commitment revealed into a
publication cell holding a value holds that value
(`Vegas.SourceProgram.ProtocolState.cell?_eq_of_published`).
-/

noncomputable section

namespace Vegas.SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

section Revelations

variable {Γ : SourceCtx Player L}

/-- Every revealed commitment publishes a failure or its own binding. -/
def PublishesOrFails (revelations : Revelations Γ) (state : State L Γ) : Prop :=
  ∀ {owner : Player} {x : VarId} {payload : L.Ty} (cell : HasVar Γ x (.commitment owner payload)),
    (revelations cell).isRevealed = true →
      (revelations cell).result state = .failure ∨ (revelations cell).result state = state.get cell

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem PublishesOrFails.initial (state : State L Γ) :
    PublishesOrFails (Revelations.initial Γ) state := by
  intro _ _ _ _ revealed
  simp [Revelations.initial, Revelation.isRevealed] at revealed

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem PublishesOrFails.weaken {revelations : Revelations Γ} {state : State L Γ} {name : VarId}
    {cell : CellTy Player L} (head : CellVal L cell)
    (publishes : PublishesOrFails revelations state) :
    PublishesOrFails (revelations.weaken (name := name) (cell := cell)) (Env.cons head state) := by
  intro owner x payload member revealed
  cases member with
  | here => simp [Revelations.weaken, HasVar.tail?, Revelation.isRevealed] at revealed
  | there member =>
      simp only [Revelations.weaken_there, Revelation.isRevealed_weaken] at revealed
      simp only [Revelations.weaken_there, Revelation.result_weaken, Env.cons_get_there]
      exact publishes member revealed

omit [DecidableEq Player] [IExpr.ResultTypes L] in
theorem PublishesOrFails.reveal {owner : Player} {payload : L.Ty} {name published : VarId}
    (unique : (Γ.map Prod.fst).Nodup) {revelations : Revelations Γ} {state : State L Γ}
    (source : HasVar Γ name (.commitment owner payload))
    (head : PublicationResult (L.Val payload)) (opens : head = .failure ∨ head = state.get source)
    (publishes : PublishesOrFails revelations state) :
    PublishesOrFails (revelations.reveal (published := published) source)
      (Env.cons (Val := CellVal (Player := Player) L) (x := published)
        (τ := .publication payload) head state) := by
  intro reader x σ member revealed
  cases member with
  | there member =>
      by_cases same : x = name
      · subst same
        have cellEq := HasVar.type_unique unique member source
        cases cellEq
        cases HasVar.eq_of_nodup unique member source
        simp only [Revelations.reveal_source, Revelation.result, Env.cons_get_here,
          Env.cons_get_there]
        exact opens
      · simp only [Revelations.reveal_of_ne _ source member same,
          Revelation.isRevealed_weaken] at revealed ⊢
        simp only [Revelation.result_weaken, Env.cons_get_there]
        exact publishes member revealed

end Revelations

namespace ProtocolState

/-- Every revealed commitment of the current configuration publishes a failure
or its own binding. -/
def PublishesOrFails : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → ProtocolState program → Prop
  | _, _, .ret _ => fun config => SourceProgram.PublishesOrFails config.revelations config.state
  | _, _, .sample _ _ _ next => Sum.elim
      (fun config => SourceProgram.PublishesOrFails config.revelations config.state)
      (PublishesOrFails next)
  | _, _, .commit _ _ _ _ next => Sum.elim
      (fun config => SourceProgram.PublishesOrFails config.revelations config.state)
      (PublishesOrFails next)
  | _, _, .reveal _ _ _ _ _ _ next => Sum.elim
      (fun config => SourceProgram.PublishesOrFails config.revelations config.state)
      (PublishesOrFails next)

theorem publishesOrFails_entry {Γ : SourceCtx Player L} {O : Finset VarId}
    (program : SourceProgram Player L Γ O) (config : Config Player L Γ)
    (holds : SourceProgram.PublishesOrFails config.revelations config.state) :
    PublishesOrFails program (entry program config) := by
  cases program <;> exact holds

/-- **Publications carry their bindings or fail** after every source step from
a program with distinct names. -/
theorem publishesOrFails_step : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (Γ.map Prod.fst).Nodup →
    (state : ProtocolState program) → (joint : Player → Option (OwnAction Player L)) →
    (target : ProtocolState program) → PublishesOrFails program state →
    target ∈ (step program state joint).support → PublishesOrFails program target
  | _, _, .ret _, _, _, _, _, holds, reached => by
      rw [step, PMF.mem_support_pure_iff] at reached
      rw [reached]
      exact holds
  | _, _, .sample _ fresh _ next, unique, state, joint, target, holds, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.support_map, Set.mem_image] at reached
          obtain ⟨value, _, rfl⟩ := reached
          exact publishesOrFails_entry next _ (PublishesOrFails.weaken _ holds)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact publishesOrFails_step next (List.nodup_cons.mpr ⟨fresh, unique⟩) rest joint after
            holds supported
  | _, _, .commit _ _ fresh _ next, unique, state, joint, target, holds, reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          exact publishesOrFails_entry next _ (PublishesOrFails.weaken _ holds)
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact publishesOrFails_step next (List.nodup_cons.mpr ⟨fresh, unique⟩) rest joint after
            holds supported
  | _, _, .reveal published owner name fresh source _ next, unique, state, joint, target, holds,
      reached => by
      cases state with
      | inl config =>
          simp only [step, Sum.elim_inl, PMF.mem_support_pure_iff] at reached
          subst reached
          refine publishesOrFails_entry next _ (PublishesOrFails.reveal unique source _ ?_ holds)
          split_ifs <;> first | exact Or.inl rfl | exact Or.inr rfl
      | inr rest =>
          simp only [step, Sum.elim_inr, PMF.support_map, Set.mem_image] at reached
          obtain ⟨after, supported, rfl⟩ := reached
          exact publishesOrFails_step next (List.nodup_cons.mpr ⟨fresh, unique⟩) rest joint after
            holds supported

/-- The current configuration of a point where publications carry their
bindings or fail. -/
theorem publishesOrFails_currentConfig : {Γ : SourceCtx Player L} → {O : Finset VarId} →
    (program : SourceProgram Player L Γ O) → (state : ProtocolState program) →
    PublishesOrFails program state →
      SourceProgram.PublishesOrFails (currentConfig program state).2.revelations
        (currentConfig program state).2.state
  | _, _, .ret _, _, holds => holds
  | _, _, .sample _ _ _ next, state, holds => by
      cases state with
      | inl _ => exact holds
      | inr rest => exact publishesOrFails_currentConfig next rest holds
  | _, _, .commit _ _ _ _ next, state, holds => by
      cases state with
      | inl _ => exact holds
      | inr rest => exact publishesOrFails_currentConfig next rest holds
  | _, _, .reveal _ _ _ _ _ _ next, state, holds => by
      cases state with
      | inl _ => exact holds
      | inr rest => exact publishesOrFails_currentConfig next rest holds

variable [DecidableEq (CellTy Player L)]

/-- **A commitment revealed into a publication holding a value holds that
value**, at a point with distinct names where publications carry their bindings
or fail. -/
theorem cell?_eq_of_published {Γ : SourceCtx Player L} {O : Finset VarId}
    {program : SourceProgram Player L Γ O} {state : ProtocolState program}
    (holds : PublishesOrFails program state)
    (unique : ((currentConfig program state).1.map Prod.fst).Nodup)
    {owner : Player} {payload : L.Ty} {name published : VarId}
    (revealed : RevealedInto program state owner payload name published)
    {value : L.Val payload}
    (publication : cell? program state published (.publication payload) =
      some (.success value)) :
    cell? program state name (.commitment owner payload) = some (.success value) := by
  rw [cell?_eq_currentConfig] at publication ⊢
  obtain ⟨source, cell, recorded⟩ := revealed
  have opened := publishesOrFails_currentConfig program state holds source
    (by simp only [recorded, Revelation.isRevealed])
  simp only [recorded, Revelation.result] at opened
  rw [State.cell?_eq_of_hasVar cell unique] at publication
  have publishedEq : (currentConfig program state).2.state.get cell = .success value :=
    Option.some.inj publication
  rw [State.cell?_eq_of_hasVar source unique]
  rcases opened with failed | carried
  · rw [publishedEq] at failed
    cases failed
  · exact congrArg some (carried.symm.trans publishedEq)

end ProtocolState

end Vegas.SourceProgram

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol Interaction
  EventGraphRuntime

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}

theorem publishesOrFails_stepClosed :
    StepClosed setup (ProtocolState.PublishesOrFails setup.program) :=
  fun state joint target holds reached =>
    ProtocolState.publishesOrFails_step setup.program setup.namesNodup state joint target holds
      reached

/-- **Publications carry their bindings or fail along every history** of a
response menu of the default runtime, under any scheduler. -/
theorem decodedState_publishesOrFails (profile : BehavioralProfile setup.program)
    (menu : (application setup leaks).ResponseMenu) (horizon : Nat)
    (scheduler : (application setup leaks).Scheduler) :
    ∀ {state} (_ : (menu.protocol (initialLaw setup) horizon scheduler).Trace state)
      (control : (application setup leaks).Control), state = some control →
      DecodedState setup leaks profile (ProtocolState.PublishesOrFails setup.program)
        (some control) := by
  intro state trace
  induction trace with
  | start => intro _ initialized; cases initialized
  | @extend before after prior joint _ realized ih =>
      intro control current
      subst current
      cases before with
      | none =>
          change some control ∈ ((initialLaw setup).map fun state =>
            some ⟨horizon, none, ReactiveApplication.Execution.initial
              (application setup leaks) state⟩).support at realized
          obtain ⟨state, supported, same⟩ := PMF.support_map .. ▸ realized
          cases Option.some.inj same
          obtain ⟨initial, _, rfl⟩ := PMF.support_map .. ▸ supported
          let residual := SourceResidual.initial setup profile initial
          refine ⟨0, ⟨residual⟩, fun point decoded => ?_⟩
          change sourceServicePrefix? setup 0 (EventGraphRuntime.State.initial
            (graph := graph setup) (setup.eventInputs initial)).config = some point at decoded
          rw [residual.decode, Option.some.injEq] at decoded
          subst decoded
          exact ProtocolState.publishesOrFails_entry setup.program _
            (PublishesOrFails.initial _)
      | some previous =>
          exact decodedHolds_transition publishesOrFails_stepClosed (initialLaw setup)
            horizon scheduler (some previous) (some control) joint (ih previous rfl) realized

end Vegas
