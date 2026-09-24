/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Source.SetupProtocolBehavioral
import Vegas.Expr.Simple
import GameTheoryExtensions.Analysis.Protocol.ConsistencyCompletion

/-! # A source game with a deferred rejecting guard

Alice has a private type and an initial commitment to that type. Bob has an
initial commitment to `true`. Alice binds a dummy Boolean, publishes it, then
resolves her initial commitment. A deferred contradictory guard can make that
resolution fail. Bob's last disclosure decision is a binary guess; payoffs
depend on the private type only when Alice's resolution failed.
-/

noncomputable section

namespace VegasTests.SequentialValidation

open Vegas Vegas.SourceProgram GameTheory GameTheory.Protocol GameTheory.Math.Probability

abbrev initialCtx : SourceCtx Bool simpleExpr :=
  [(0, .privateInput false .bool), (1, .commitment false .bool),
    (2, .commitment true .bool)]

def rejectingGuard : SourceGuard simpleExpr initialCtx false 3 .bool where
  schema := [(1, .bool)]
  schemaNames := by decide
  subjectFresh := by decide
  code := .andBool (.var 1 (.there .here)) (.notBool (.var 1 (.there .here)))
  reads := fun ref => match ref with
    | .here => .commitment (.there .here)

def sourceProgram : SourceProgram Bool simpleExpr initialCtx {1, 2} :=
  .commit 3 false (by decide) rejectingGuard <|
  .reveal 4 false 3 (by decide) .here (by decide) <|
  .reveal 5 false 1 (by decide) (.there (.there (.there .here))) (by decide) <|
  .reveal 6 true 2 (by decide) (.there (.there (.there (.there (.there .here)))))
    (by decide) <|
  .ret []

def initialState (bit : Bool) : State simpleExpr initialCtx :=
  Env.cons bit <| Env.cons (.success bit) <| Env.cons (.success true) <| Env.empty _

def sourceSetup : Setup (Player := Bool) (L := simpleExpr) where
  context := initialCtx
  namesNodup := by decide
  initialLaw := (FinDist.uniformOfFintype (α := Bool)).map initialState
  obligations := {1, 2}
  program := sourceProgram
  accounts := rfl

def sourceAdmission : CommitmentInterface sourceSetup.program :=
  CommitmentInterface.forfeiture sourceProgram

abbrev sourceArena := sourceSetup.executionProtocol sourceAdmission
abbrev sourceModel := sourceSetup.informationModel sourceAdmission

def startConfig (bit : Bool) := sourceSetup.initialConfig (initialState bit)
def boundConfig (bit : Bool) (dummy : PublicationResult Bool) :=
  commitSuccessor 3 rejectingGuard (startConfig bit) dummy
def dummyConfig (bit : Bool) (dummy : PublicationResult Bool) (disclose : Bool) :=
  revealSuccessor 4 .here (boundConfig bit dummy) disclose
def secretConfig (bit : Bool) (dummy : PublicationResult Bool) (first second : Bool) :=
  revealSuccessor 5 (.there (.there (.there .here))) (dummyConfig bit dummy first) second
def finalConfig (bit : Bool) (dummy : PublicationResult Bool) (first second guess : Bool) :=
  revealSuccessor 6 (.there (.there (.there (.there (.there .here)))))
    (secretConfig bit dummy first second) guess

theorem dummy_publication (bit : Bool) (dummy : PublicationResult Bool) (disclose : Bool) :
    (dummyConfig bit dummy disclose).state.get .here =
      if disclose then dummy else .failure := by
  cases bit <;> cases dummy <;> cases disclose
  all_goals first | decide | (rename_i value; cases value <;> decide)

theorem secret_publication (bit : Bool) (dummy : PublicationResult Bool) (first second : Bool) :
    (secretConfig bit dummy first second).state.get .here =
      if (first && dummy.isSuccess) || !second then .failure else .success bit := by
  cases bit <;> cases dummy <;> cases first <;> cases second
  all_goals first | decide | (rename_i value; cases value <;> decide)

theorem guess_publication (bit : Bool) (dummy : PublicationResult Bool)
    (first second guess : Bool) :
    (finalConfig bit dummy first second guess).state.get .here =
      if guess then .success true else .failure := by
  cases bit <;> cases dummy <;> cases first <;> cases second <;> cases guess
  all_goals first | decide | (rename_i value; cases value <;> decide)

instance : Nonempty (PublicationResult Bool) := ⟨.failure⟩

def uniformSourcePolicy (who : Bool) : BehavioralPolicy who sourceProgram :=
  (fun _ _ => FinDist.uniformOfFintype (α := PublicationResult Bool),
    (fun _ _ => FinDist.uniformOfFintype (α := Bool),
      (fun _ _ => FinDist.uniformOfFintype (α := Bool),
        (fun _ _ => FinDist.uniformOfFintype (α := Bool), PUnit.unit))))

theorem uniformSourcePolicy_admitted (who : Bool) :
    (uniformSourcePolicy who).Admitted sourceProgram sourceAdmission := by
  refine ⟨?_, trivial⟩
  intro owner view choice supported
  cases choice <;> trivial

def uniformSourceProfile : Profile sourceModel.behavioralSignature :=
  fun who => sourceSetup.toProtocolBehavioralPolicy sourceAdmission who
    (uniformSourcePolicy who) (uniformSourcePolicy_admitted who)

theorem uniformSourceProfile_full (who : Bool) (info : sourceModel.InfoState who) :
    (uniformSourceProfile who info).FullSupport := by
  have admitted (value : PublicationResult Bool) :
      CommitmentAdmission.forfeiture.Admits value := by
    cases value <;> trivial
  intro choice
  suffices choice.val ∈ ((uniformSourceProfile who info).map Subtype.val).support by
    obtain ⟨other, supported, same⟩ := FinDist.support_map .. ▸ this
    exact (Subtype.ext same) ▸ supported
  rw [uniformSourceProfile, Setup.toProtocolBehavioralPolicy_map_val]
  rcases choice with ⟨action, legal⟩
  change sourceSetup.protocolMenu sourceAdmission who info action at legal
  cases info with
  | none => exact FinDist.mem_support_pure.mpr legal
  | some info =>
      rcases info with current | current | current | current | current
      all_goals cases who <;> cases action
      all_goals
        have allowed := legal
        dsimp [Setup.protocolMenu, sourceSetup, sourceProgram, ProtocolView.menu,
          ProtocolView.actor, ProtocolView.available, sourceAdmission,
          CommitmentInterface.forfeiture] at allowed
        simp_all [sourceSetup, sourceProgram, BehavioralPolicy.protocolAction,
          uniformSourcePolicy, FinDist.support_map,
          FinDist.mem_support_uniformOfFintype, eq_comm]

theorem uniformSourceProfile_fullyMixed :
    (InformationModel.BehavioralAssessment.ofStrategy uniformSourceProfile).IsFullyMixed :=
  fun who site => uniformSourceProfile_full who site.1

instance : Finite sourceArena.History :=
  uniformSourceProfile_fullyMixed.finite_history
    (sourceSetup.protocol_bounded sourceAdmission)

instance : Fintype sourceArena.History := Fintype.ofFinite _

instance (who : Bool) (site : sourceModel.InformationSite who) :
    Fintype (sourceModel.InformationHistory who site.1) := by
  classical
  infer_instance

end VegasTests.SequentialValidation
