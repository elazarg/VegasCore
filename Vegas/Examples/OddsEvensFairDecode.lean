/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Examples.OddsEvensFairProfile
import Vegas.Game.IntendedAuthenticOpening

/-! # Source decoding of the actual intended Odds–Evens policies -/

noncomputable section

namespace Vegas.Examples.OddsEvens

open SourceProgram GameTheory GameTheory.Protocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability

def firstCommitView : DecisionView (L := simpleExpr) even [] :=
  (sourceObserve even (Env.empty (CellVal simpleExpr)), [])

def secondCommitView : DecisionView (L := simpleExpr) odd [(0, .commitment even .bool)] :=
  (sourceObserve odd (Env.cons (.success false) (Env.empty (CellVal simpleExpr))), [])

def firstInfo : setup.ProtocolView even := some (.inl firstCommitView)

def secondInfo : setup.ProtocolView odd := some (.inr (.inl secondCommitView))

def sourceDecoded (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    BehavioralProfile program :=
  setup.decodeBehavioralProfile (CommitmentInterface.values setup.program)
    (setup.intendedSourceProfile profile)

theorem first_commit_decoded (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    commitKernel (sourceDecoded profile) firstCommitView =
      (profile even firstInfo).map
        (fun choice => OwnAction.binding (L := simpleExpr) even 0 .bool choice.1) := by
  change ((profile even firstInfo).map _).map _ = _
  rw [PMF.map_comp]
  rfl

theorem second_commit_decoded (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    commitKernel (afterCommit (sourceDecoded profile)) secondCommitView =
      (profile odd secondInfo).map
        (fun choice => OwnAction.binding (L := simpleExpr) odd 1 .bool choice.1) := by
  change ((profile odd secondInfo).map _).map _ = _
  rw [PMF.map_comp]
  rfl

theorem sourceDecoded_disclosing
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player) :
    Disclosing program (sourceDecoded profile who) :=
  BehavioralPolicy.disclosing_fromProtocol setup.program _ _
    (fun view => setup.intendedSourceProfile_notRefusal profile who (some view))

theorem sourceDecoded_admitted
    (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) (who : Player) :
    (sourceDecoded profile who).Admitted program
      (CommitmentInterface.values setup.program) :=
  ((setup.behavioralPolicyEquiv (CommitmentInterface.values setup.program) who).symm
    (setup.intendedSourceProfile profile who)).2

/-- The initialized intended protocol and its decoded source policies have the
same complete typed-store law. No effective-opening transformation is needed. -/
theorem sourceDecoded_run (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    (setup.intendedModel.runBehavioral profile (instructionCount setup.program + 1)).map
        (fun final => setup.protocolReadout final.state) =
      (setup.run (sourceDecoded profile)).map some := by
  let admission := CommitmentInterface.values setup.program
  let restriction := setup.intendedRestriction admission
  have agrees : restriction.ExtendsProfile profile (setup.intendedSourceProfile profile) :=
    fun _ _ => rfl
  have law := restriction.initialized_law profile (setup.intendedSourceProfile profile) agrees
    (instructionCount setup.program + 1)
  have encoded :
      (fun who => setup.toProtocolBehavioralPolicy admission who (sourceDecoded profile who)
        (sourceDecoded_admitted profile who)) = setup.intendedSourceProfile profile := by
    funext who
    exact (setup.behavioralPolicyEquiv admission who).apply_symm_apply
      (setup.intendedSourceProfile profile who)
  have source := setup.protocol_runBehavioral_eq admission (sourceDecoded profile)
    (sourceDecoded_admitted profile)
  rw [InformationModel.runSingleMoverBehavioralFrom_eq_runBehavioralFrom, encoded] at source
  rw [← source]
  change _ = ((setup.informationModel admission).runBehavioral _
    (instructionCount setup.program + 1)).map _
  rw [← law, PMF.map_comp]
  rfl

theorem first_binding_success (choice : setup.intendedModel.Choice even firstInfo) :
    PublicationResult.success
        ((OwnAction.binding (L := simpleExpr) even 0 .bool choice.1).getD false) =
      OwnAction.binding (L := simpleExpr) even 0 .bool choice.1 := by
  obtain ⟨bit, rfl⟩ := intendedBitChoice_surjective even firstInfo choice
  rw [show (intendedBitChoice bit even firstInfo).1 =
    some (.commit even 0 .bool (.success bit)) from rfl, OwnAction.binding_commit]
  rfl

theorem second_binding_success (choice : setup.intendedModel.Choice odd secondInfo) :
    PublicationResult.success
        ((OwnAction.binding (L := simpleExpr) odd 1 .bool choice.1).getD false) =
      OwnAction.binding (L := simpleExpr) odd 1 .bool choice.1 := by
  obtain ⟨bit, rfl⟩ := intendedBitChoice_surjective odd secondInfo choice
  rw [show (intendedBitChoice bit odd secondInfo).1 =
    some (.commit odd 1 .bool (.success bit)) from rfl, OwnAction.binding_commit]
  rfl

def firstBitLaw (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) : PMF Bool :=
  (profile even firstInfo).map
    (fun choice => (OwnAction.binding (L := simpleExpr) even 0 .bool choice.1).getD false)

def secondBitLaw (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) : PMF Bool :=
  (profile odd secondInfo).map
    (fun choice => (OwnAction.binding (L := simpleExpr) odd 1 .bool choice.1).getD false)

theorem first_commit_bitLaw (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    commitKernel (sourceDecoded profile) firstCommitView =
      (firstBitLaw profile).map PublicationResult.success := by
  rw [first_commit_decoded, firstBitLaw, PMF.map_comp]
  exact map_congr_on_support _ (fun choice _ => (first_binding_success choice).symm)

theorem second_commit_bitLaw (profile : ∀ who, setup.intendedModel.BehavioralPolicy who) :
    commitKernel (afterCommit (sourceDecoded profile)) secondCommitView =
      (secondBitLaw profile).map PublicationResult.success := by
  rw [second_commit_decoded, secondBitLaw, PMF.map_comp]
  exact map_congr_on_support _ (fun choice _ => (second_binding_success choice).symm)

theorem firstBitLaw_uniform : firstBitLaw uniformProfile = PMF.uniformOfFintype Bool := by
  rw [firstBitLaw, uniformProfile, PMF.map_comp]
  have simplified : (fun bit =>
      (OwnAction.binding (L := simpleExpr) even 0 .bool
        (intendedBitChoice bit even firstInfo).1).getD false) = id := by
    funext bit
    rw [show (intendedBitChoice bit even firstInfo).1 =
      some (.commit even 0 .bool (.success bit)) from rfl, OwnAction.binding_commit]
    rfl
  exact (congrArg (fun action : Bool → Bool => (PMF.uniformOfFintype Bool).map action)
    simplified).trans (PMF.map_id _)

theorem secondBitLaw_uniform : secondBitLaw uniformProfile = PMF.uniformOfFintype Bool := by
  rw [secondBitLaw, uniformProfile, PMF.map_comp]
  have simplified : (fun bit =>
      (OwnAction.binding (L := simpleExpr) odd 1 .bool
        (intendedBitChoice bit odd secondInfo).1).getD false) = id := by
    funext bit
    rw [show (intendedBitChoice bit odd secondInfo).1 =
      some (.commit odd 1 .bool (.success bit)) from rfl, OwnAction.binding_commit]
    rfl
  exact (congrArg (fun action : Bool → Bool => (PMF.uniformOfFintype Bool).map action)
    simplified).trans (PMF.map_id _)

end Vegas.Examples.OddsEvens
