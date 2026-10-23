/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.ProposalRecoveryPublicClassProduct
import Vegas.Source.CommitRecoveryOwnedStep
import GameTheoryExtensions.Analysis.Protocol.ContinuationOwnPlay
import GameTheoryExtensions.Analysis.Protocol.OwnPlayReach

/-! # Whole source reach and the public foreign class coefficient -/

noncomputable section

namespace Vegas.SourceProgram.Setup

open GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability
open scoped ENNReal

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L))

omit [Fintype Player] in
private theorem source_player_atom_none
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    (owner : Player) (absent : joint owner = none) :
    setup.proposalRecoveryModel.playerStepProb profile owner before.trace ⟨joint, legal⟩ = 1 := by
  classical
  have inactive : ¬ setup.proposalRecoveryProtocol.active before.state owner := by
    have offered := setup.proposalRecoveryProtocol.legalOption_of_legal legal owner
    simpa only [absent, LegalOption] using offered
  let _ := setup.proposalRecoveryModel.subsingleton_choice_of_not_active before.trace inactive
  unfold InformationModel.playerStepProb
  rw [eq_pure_of_subsingleton (profile owner
    (setup.proposalRecoveryModel.infoOf owner before.trace))
      (setup.proposalRecoveryModel.choicesOfLegal before.trace ⟨joint, legal⟩ owner)]
  simp

private theorem source_opponents_single_actor
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    (focal owner : Player) (foreign : owner ≠ focal)
    (silent : ∀ other, other ≠ owner → joint other = none) :
    setup.proposalRecoveryModel.opponentsStepProb profile focal before.trace ⟨joint, legal⟩ =
      setup.proposalRecoveryModel.playerStepProb profile owner before.trace ⟨joint, legal⟩ := by
  classical
  unfold InformationModel.opponentsStepProb
  apply Finset.prod_eq_single owner
  · intro other _member different
    exact source_player_atom_none setup profile before joint legal other
      (silent other different)
  · intro missing
    exact False.elim (missing (Finset.mem_erase.mpr ⟨foreign, Finset.mem_univ _⟩))

private theorem source_opponents_all_none
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    (focal : Player) (silent : ∀ other, other ≠ focal → joint other = none) :
    setup.proposalRecoveryModel.opponentsStepProb profile focal before.trace
      ⟨joint, legal⟩ = 1 := by
  classical
  unfold InformationModel.opponentsStepProb
  apply Finset.prod_eq_one
  intro other member
  exact source_player_atom_none setup profile before joint legal other
    (silent other (Finset.ne_of_mem_erase member))

omit [Fintype Player] in
private theorem source_joint_none_of_actor_ne
    (current : CommitRecoveryState setup.program)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal (some current) joint)
    (owner : Player) (acting : ProtocolState.actor setup.program current.point = some owner)
    (other : Player) (different : other ≠ owner) : joint other = none := by
  have inactive : ¬ setup.proposalRecoveryProtocol.active (some current) other := by
    intro active
    change ProtocolState.actor setup.program current.point = some other ∧
      other ∉ current.excluded at active
    exact different (Option.some.inj (active.1.symm.trans acting))
  exact LegalOption.eq_none_of_inactive _
    (setup.proposalRecoveryProtocol.legalOption_of_legal legal other) inactive

omit [Fintype Player] in
private theorem source_component_atom
    (prescription : ∀ owner, setup.ProposalRecoveryPrescription owner)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint) (owner : Player) :
    setup.proposalRecoveryPrescribedProfile prescription owner
        (setup.proposalRecoveryModel.infoOf owner before.trace)
        (setup.proposalRecoveryModel.choicesOfLegal before.trace ⟨joint, legal⟩ owner) =
      prescription owner (setup.proposalRecoveryQuery owner
        (setup.proposalRecoveryModel.infoOf owner before.trace))
          (setup.proposalRecoveryComponentChoice owner
            (setup.proposalRecoveryModel.infoOf owner before.trace)
              (setup.proposalRecoveryModel.choicesOfLegal before.trace ⟨joint, legal⟩ owner)) := by
  let information := setup.proposalRecoveryModel.infoOf owner before.trace
  let equivalence := setup.proposalRecoveryComponentChoice owner information
  let choice := setup.proposalRecoveryModel.choicesOfLegal before.trace ⟨joint, legal⟩ owner
  have atom := pmf_map_apply_of_injective (prescription owner
    (setup.proposalRecoveryQuery owner information)) equivalence.symm.injective
      (equivalence choice)
  simpa only [proposalRecoveryPrescribedProfile, Equiv.symm_apply_apply] using atom

omit [Fintype Player] in
private theorem source_available_commit_atCommit (who : Player) :
    ∀ {Γ : SourceCtx Player L} {O : Finset VarId}
      (program : SourceProgram Player L Γ O) (admission : CommitmentInterface program)
      (view : Vegas.SourceProgram.ProtocolView who program)
      (author : Player) (name : VarId) (payload : L.Ty)
      (binding : PublicationResult (L.Val payload)),
      .commit author name payload binding ∈ ProtocolView.available who program admission view →
        ProtocolView.atCommit who program view = true
  | _, _, .ret _, _, _, _, _, _, _, offered => by cases offered
  | _, _, .sample _ _ _ next, admission, view, author, name, payload, binding, offered => by
      cases view with
      | inl _ => cases offered
      | inr view =>
          exact source_available_commit_atCommit who next admission view
            author name payload binding offered
  | _, _, .commit _ _ _ _ next, admission, view, author, name, payload, binding, offered => by
      cases view with
      | inl _ => rfl
      | inr view =>
          exact source_available_commit_atCommit who next (fun site => admission (some site)) view
            author name payload binding offered
  | _, _, .reveal _ _ _ _ _ _ next, admission, view, author, name, payload, binding, offered => by
      cases view with
      | inl _ =>
          obtain ⟨bit, impossible⟩ := offered
          cases impossible
      | inr view =>
          exact source_available_commit_atCommit who next admission view
            author name payload binding offered

omit [Fintype Player] in
private theorem source_component_commit_atCommit
    (owner : Player) (key : setup.ProposalRecoveryComponent owner)
    (choice : setup.ProposalRecoveryComponentChoice owner key)
    (move : ProposalRecoveryMove Player L) (selected : choice.val = some move)
    (author : Player) (name : VarId) (payload : L.Ty)
    (binding : PublicationResult (L.Val payload))
    (action : move.semantic.action = .commit author name payload binding) :
    key.1.1.1.1.elim false (ProtocolView.atCommit owner setup.program) = true := by
  have offered := choice.property.1
  change setup.commitRecoveryMenu owner key.1 (choice.val.map (·.semantic)) at offered
  rw [selected, Option.map_some] at offered
  cases current : key.1.1.1.1 with
  | none =>
      have impossible := offered.2
      change key.1.1.1.1.elim False
        (fun view => move.semantic ∈ ProtocolView.recoveryAvailable owner setup.program view)
        at impossible
      rw [current] at impossible
      exact impossible.elim
  | some view =>
      have available := offered.2
      rw [current] at available
      have actual := available.1
      rw [action] at actual
      exact source_available_commit_atCommit owner setup.program
        (CommitmentInterface.forfeiture setup.program) view author name payload binding actual

omit [Fintype Player] in
private theorem source_acting_step_mass_one
    (current : CommitRecoveryState setup.program) (owner : Player)
    (acting : ProtocolState.actor setup.program current.point = some owner)
    (joint : Player → Option (CommitRecoveryMove Player L))
    (target : CommitRecoveryState setup.program)
    (supported : target ∈ (current.step joint).support) :
    current.step joint target = 1 := by
  classical
  apply (PMF.apply_eq_one_iff _ _).mpr
  ext other
  constructor
  · intro member
    exact Set.mem_singleton_iff.mpr
      (setup.commitRecovery_step_unique_of_actor current owner acting joint
        other target member supported)
  · intro same
    rw [Set.mem_singleton_iff] at same
    simpa only [same] using supported

private theorem source_acting_one_step_opponents
    (profile : ∀ owner, setup.proposalRecoveryModel.BehavioralPolicy owner)
    (focal : Player) (before : setup.proposalRecoveryProtocol.History)
    (current : CommitRecoveryState setup.program) (state : before.state = some current)
    (owner : Player) (acting : ProtocolState.actor setup.program current.point = some owner)
    (foreign : owner ≠ focal) (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    {target : setup.proposalRecoveryProtocol.State}
    (supported : target ∈ (setup.proposalRecoveryProtocol.step before.state
      ⟨joint, legal⟩).support) :
    (setup.proposalRecoveryModel.runBehavioralFrom profile 1 before
      (before.extend legal supported)).toReal =
      setup.proposalRecoveryModel.opponentsStepProb profile focal before.trace ⟨joint, legal⟩ := by
  classical
  rcases before with ⟨beforeState, beforeTrace⟩
  change beforeState = some current at state
  subst beforeState
  let before : setup.proposalRecoveryProtocol.History := ⟨some current, beforeTrace⟩
  have state : before.state = some current := rfl
  have silent : joint focal = none := by
    apply source_joint_none_of_actor_ne setup current joint
      (state ▸ legal) owner acting focal foreign.symm
  have focalMass := source_player_atom_none setup profile before joint legal focal silent
  have transition : setup.proposalRecoveryProtocol.step before.state ⟨joint, legal⟩ target = 1 := by
    have sourceSupported := supported
    rw [setup.proposalRecovery_step] at sourceSupported ⊢
    change target ∈ ((current.step (proposalRecoveryJoint joint)).map some).support
      at sourceSupported
    obtain ⟨next, member, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp sourceSupported
    change ((current.step (proposalRecoveryJoint joint)).map some) (some next) = 1
    rw [pmf_map_apply_of_injective _ (Option.some_injective _)]
    exact source_acting_step_mass_one setup current owner acting _ next member
  rw [setup.proposalRecoveryModel.runBehavioralFrom_one_prob_extend profile before legal.1
    ⟨joint, legal⟩ target supported,
    setup.proposalRecoveryModel.stepProb_eq_player_mul_counterfactual profile focal,
    focalMass, InformationModel.counterfactualStepProb, transition, ENNReal.toReal_one,
    one_mul, mul_one]

theorem proposalRecovery_foreign_row_opponents
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    {target : setup.proposalRecoveryProtocol.State}
    (supported : target ∈ (setup.proposalRecoveryProtocol.step before.state
      ⟨joint, legal⟩).support) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      omission.val omission.property.1 omission.property.2
      bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2 values
    let row := setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
      before joint legal supported
    setup.proposalRecoveryModel.opponentsStepProb profile focal before.trace ⟨joint, legal⟩ =
      row.1.toReal * row.2.1.toReal * row.2.2.toReal := by
  classical
  intro profile row
  rcases before with ⟨source, prior⟩
  cases source with
  | none =>
      let before : setup.proposalRecoveryProtocol.History := ⟨none, prior⟩
      have state : before.state = none := rfl
      have silent (other : Player) : joint other = none := by
        exact LegalOption.eq_none_of_inactive _
          (setup.proposalRecoveryProtocol.legalOption_of_legal legal other)
          (by rw [state]; exact fun impossible => impossible)
      rw [source_opponents_all_none setup profile before joint legal focal
        (fun other _ => silent other)]
      simp only [row, proposalRecoveryForeignRowFactors, ENNReal.toReal_one, mul_one]
  | some current =>
      let before : setup.proposalRecoveryProtocol.History := ⟨some current, prior⟩
      have state : before.state = some current := rfl
      cases acting : ProtocolState.actor setup.program current.point with
      | none =>
          have silent (other : Player) : joint other = none := by
            apply LegalOption.eq_none_of_inactive _
              (setup.proposalRecoveryProtocol.legalOption_of_legal legal other)
            rw [state]
            intro active
            cases (acting.symm.trans active.1)
          rw [source_opponents_all_none setup profile before joint legal focal
            (fun other _ => silent other)]
          simp only [row, proposalRecoveryForeignRowFactors, acting,
            ENNReal.toReal_one, mul_one]
      | some owner =>
          have silent (other : Player) (different : other ≠ owner) : joint other = none :=
            source_joint_none_of_actor_ne setup current joint (state ▸ legal)
              owner acting other different
          by_cases foreign : owner = focal
          · subst owner
            rw [source_opponents_all_none setup profile before joint legal focal silent]
            simp only [row, proposalRecoveryForeignRowFactors, acting, ite_true,
              ENNReal.toReal_one, mul_one]
          · rw [source_opponents_single_actor setup profile before joint legal focal owner
              foreign silent]
            cases selected : joint owner with
            | none =>
                rw [source_player_atom_none setup profile before joint legal owner selected]
                simp only [row, proposalRecoveryForeignRowFactors, acting, foreign,
                  ite_false, selected, ENNReal.toReal_one, mul_one]
            | some move =>
                let information := setup.proposalRecoveryModel.infoOf owner before.trace
                let key := setup.proposalRecoveryQuery owner information
                let choice := setup.proposalRecoveryComponentChoice owner information
                  (setup.proposalRecoveryModel.choicesOfLegal before.trace ⟨joint, legal⟩ owner)
                have picked : choice.val = some move := selected
                have componentMass := source_component_atom setup (fun author coordinate =>
                  setup.proposalRecoveryComponentTrembledLaw author coordinate
                    omission.val omission.property.1 omission.property.2
                    bad.val bad.property.1 bad.property.2
                    delivery.val delivery.property.1 delivery.property.2
                    (values author coordinate)) before joint legal owner
                change (profile owner information
                    (setup.proposalRecoveryModel.choicesOfLegal before.trace
                      ⟨joint, legal⟩ owner)) =
                  setup.proposalRecoveryComponentTrembledLaw owner key
                    omission.val omission.property.1 omission.property.2
                    bad.val bad.property.1 bad.property.2
                    delivery.val delivery.property.1 delivery.property.2
                    (values owner key) choice at componentMass
                cases action : move.semantic.action with
                | commit author name payload binding =>
                    have committing := source_component_commit_atCommit setup owner key
                      choice move picked author name payload binding action
                    have failureIfMissing : move.semantic.missing = true →
                        move.semantic.action.IsFailure := by
                      have offered := choice.property.1
                      change setup.commitRecoveryMenu owner key.1
                        (choice.val.map (·.semantic)) at offered
                      rw [picked, Option.map_some] at offered
                      have available := offered.2
                      cases currentView : key.1.1.1.1 with
                      | none =>
                          simp only [currentView, Option.elim_none] at available
                      | some view =>
                          rw [currentView] at available
                          have flag := available.2
                          have atView : ProtocolView.atCommit owner setup.program view = true := by
                            simpa only [currentView, Option.elim_some] using committing
                          simpa only [atView, ite_true] using flag
                    cases missing : move.semantic.missing with
                    | true =>
                        have failed := failureIfMissing missing
                        cases binding with
                        | success value =>
                            rw [action] at failed
                            cases failed
                        | failure =>
                            have atom :=
                              setup.proposalRecoveryComponentTrembledLaw_failed_commit_atom
                              owner key committing omission bad delivery (values owner key)
                              choice move picked author name payload action
                            rw [missing] at atom
                            change (_ : ℝ≥0∞).toReal = _
                            rw [componentMass, atom]
                            simp only [row, proposalRecoveryForeignRowFactors, acting,
                              foreign, ite_false, selected, action, missing, ite_true,
                              ENNReal.toReal_one, mul_one]
                    | false =>
                        cases binding with
                        | failure =>
                            have atom :=
                              setup.proposalRecoveryComponentTrembledLaw_failed_commit_atom
                              owner key committing omission bad delivery (values owner key)
                              choice move picked author name payload action
                            rw [missing] at atom
                            change (_ : ℝ≥0∞).toReal = _
                            rw [componentMass, atom]
                            simp only [row, proposalRecoveryForeignRowFactors, acting,
                              foreign, ite_false, selected, action, missing, Bool.false_eq_true,
                              ENNReal.toReal_one, mul_one]
                        | success value =>
                            have atom :=
                              setup.proposalRecoveryComponentTrembledLaw_proper_commit_atom
                              owner key committing omission bad delivery (values owner key)
                              choice move picked author name payload value action missing
                            let ordinary := setup.proposalRecoveryNormalizedTrembledProfile
                              0 le_rfl zero_le_one 0 le_rfl zero_le_one
                                0 le_rfl zero_le_one values
                            have ordinaryMass := source_component_atom setup
                              (fun author coordinate =>
                              setup.proposalRecoveryComponentTrembledLaw author coordinate
                                0 le_rfl zero_le_one 0 le_rfl zero_le_one
                                  0 le_rfl zero_le_one (values author coordinate))
                                before joint legal owner
                            change ordinary owner information
                                (setup.proposalRecoveryModel.choicesOfLegal before.trace
                                  ⟨joint, legal⟩ owner) =
                              setup.proposalRecoveryComponentTrembledLaw owner key
                                0 le_rfl zero_le_one 0 le_rfl zero_le_one
                                  0 le_rfl zero_le_one (values owner key) choice at ordinaryMass
                            have rawMass : ((ordinary owner information).map Subtype.val)
                                (some move) =
                              ordinary owner information (setup.proposalRecoveryModel.choicesOfLegal
                                before.trace ⟨joint, legal⟩ owner) := by
                              have mapped := pmf_map_apply_of_injective (ordinary owner information)
                                Subtype.val_injective
                                  (setup.proposalRecoveryModel.choicesOfLegal before.trace
                                    ⟨joint, legal⟩ owner)
                              simpa only [InformationModel.choicesOfLegal, selected] using mapped
                            change (_ : ℝ≥0∞).toReal = _
                            rw [componentMass, atom, ENNReal.toReal_mul]
                            simp only [row, proposalRecoveryForeignRowFactors, acting,
                              foreign, ite_false, selected, action, missing, Bool.false_eq_true,
                              ENNReal.toReal_one, mul_one]
                            rw [rawMass, ordinaryMass]
                | reveal author name disclosed =>
                    have reconstructed :=
                      setup.proposalRecoveryForeignRowFactors_reveal_reconstruct values omission
                        bad delivery focal before joint legal supported current state owner acting
                          foreign move selected author name disclosed action
                    have actual := source_acting_one_step_opponents setup profile focal before
                      current state owner acting foreign joint legal supported
                    have rowEq := congrArg ENNReal.toReal reconstructed
                    rw [ENNReal.toReal_mul] at rowEq
                    have domainOne : row.2.1 = 1 := by
                      simp only [row, proposalRecoveryForeignRowFactors, acting, foreign,
                        ite_false, selected, action]
                    rw [← source_opponents_single_actor setup profile before joint legal
                      focal owner foreign silent, ← actual, ← rowEq, domainOne,
                      ENNReal.toReal_one, mul_one]

/-- The entire literal source History reach is the original intrinsic mass,
its complete focal own-play factor, and the three actual foreign products.
No source density identity or independent initializer factorization is an
assumption. Accepted failed preparations retain their own class factor. -/
theorem proposalRecovery_historyReach_foreign_products
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    (history : setup.proposalRecoveryProtocol.History) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      omission.val omission.property.1 omission.property.2
      bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2 values
    let factors := setup.proposalRecoveryForeignProducts values omission bad delivery focal
      history.trace
    (setup.proposalRecoveryModel.historyReachWeight profile history).toReal =
      history.trace.transitionMass *
        setup.proposalRecoveryModel.ownPlayReachProbability (profile focal)
          (setup.proposalRecoveryModel.ownPlay focal history.trace) *
            factors.1.toReal * factors.2.1.toReal * factors.2.2.toReal := by
  classical
  intro profile factors
  let parts : {state : setup.proposalRecoveryProtocol.State} →
      setup.proposalRecoveryProtocol.Trace state → ℝ≥0∞ × ℝ≥0∞ × ℝ≥0∞ :=
    setup.proposalRecoveryForeignProducts values omission bad delivery focal
  have foreignProduct : ∀ {state} (trace : setup.proposalRecoveryProtocol.Trace state),
      setup.proposalRecoveryModel.counterfactualReachProbability profile focal trace =
        trace.transitionMass *
          (parts trace).1.toReal *
          (parts trace).2.1.toReal *
          (parts trace).2.2.toReal :=
      by
    intro state trace
    induction trace with
    | start =>
        simp only [InformationModel.counterfactualReachProbability_start,
          Trace.transitionMass_start, parts, proposalRecoveryForeignProducts,
          ENNReal.toReal_one, mul_one]
    | @extend source target prior joint legal supported ih =>
        let row := setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
          ⟨source, prior⟩ joint legal supported
        have actualRow := proposalRecovery_foreign_row_opponents setup values omission bad delivery
          focal ⟨source, prior⟩ joint legal supported
        change setup.proposalRecoveryModel.opponentsStepProb profile focal prior
            ⟨joint, legal⟩ = row.1.toReal * row.2.1.toReal * row.2.2.toReal at actualRow
        simp only [InformationModel.counterfactualReachProbability,
          InformationModel.counterfactualStepProb, parts, proposalRecoveryForeignProducts,
          Trace.transitionMass_extend, ENNReal.toReal_mul]
        rw [actualRow, ih]
        ring
  rw [setup.proposalRecoveryModel.historyReachProbability_eq_player_mul_counterfactual
    profile focal history.trace,
    setup.proposalRecoveryModel.playerReachProbability_eq_ownPlayReachProbability]
  rw [foreignProduct history.trace]
  ring

/-- Every coordinate of a literal row is finite, including a zero-mass
publication fiber's totalized posterior. -/
private theorem foreign_row_finite
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    (before : setup.proposalRecoveryProtocol.History)
    (joint : Player → Option (ProposalRecoveryMove Player L))
    (legal : setup.proposalRecoveryProtocol.Legal before.state joint)
    {target : setup.proposalRecoveryProtocol.State}
    (supported : target ∈ (setup.proposalRecoveryProtocol.step before.state
      ⟨joint, legal⟩).support) :
    let row := setup.proposalRecoveryForeignRowFactors values omission bad delivery focal
      before joint legal supported
    row.1 ≠ ⊤ ∧ row.2.1 ≠ ⊤ ∧ row.2.2 ≠ ⊤ := by
  unfold proposalRecoveryForeignRowFactors
  repeat' first | split | constructor
  all_goals first
    | exact ENNReal.one_ne_top
    | exact ENNReal.ofReal_ne_top
    | exact PMF.apply_ne_top _ _

/-- Finiteness of the exact three products permits conversion from the real
reach factorization without discarding any zero source atom. -/
theorem proposalRecoveryForeignProducts_finite
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    {state : setup.proposalRecoveryProtocol.State}
    (trace : setup.proposalRecoveryProtocol.Trace state) :
    let factors := setup.proposalRecoveryForeignProducts values omission bad delivery focal trace
    factors.1 ≠ ⊤ ∧ factors.2.1 ≠ ⊤ ∧ factors.2.2 ≠ ⊤ := by
  induction trace with
  | start => exact ⟨ENNReal.one_ne_top, ENNReal.one_ne_top, ENNReal.one_ne_top⟩
  | @extend source target prior joint legal supported ih =>
      have row := foreign_row_finite setup values omission bad delivery focal
        ⟨source, prior⟩ joint legal supported
      exact ⟨ENNReal.mul_ne_top ih.1 row.1,
        ENNReal.mul_ne_top ih.2.1 row.2.1, ENNReal.mul_ne_top ih.2.2 row.2.2⟩

/-- The actual source reach identity in nonnegative extended scalars. The
original intrinsic mass, including its joint initializer atom, remains a
separate factor from the full focal own word and foreign class products. -/
theorem proposalRecovery_historyReachWeight_foreign_products
    (values : ∀ owner (key : setup.ProposalRecoveryComponent owner),
      PMF (setup.CommitRecoveryValueChoice owner key.1))
    (omission bad delivery : Set.Icc (0 : ℝ) 1) (focal : Player)
    (history : setup.proposalRecoveryProtocol.History) :
    let profile := setup.proposalRecoveryNormalizedTrembledProfile
      omission.val omission.property.1 omission.property.2
      bad.val bad.property.1 bad.property.2
      delivery.val delivery.property.1 delivery.property.2 values
    let factors := setup.proposalRecoveryForeignProducts values omission bad delivery focal
      history.trace
    setup.proposalRecoveryModel.historyReachWeight profile history =
      ENNReal.ofReal history.trace.transitionMass *
        ENNReal.ofReal (setup.proposalRecoveryModel.ownPlayReachProbability (profile focal)
          (setup.proposalRecoveryModel.ownPlay focal history.trace)) *
            factors.1 * factors.2.1 * factors.2.2 := by
  intro profile factors
  have finite := setup.proposalRecoveryForeignProducts_finite values omission bad delivery focal
    history.trace
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (by
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top) finite.1)
        finite.2.1) finite.2.2)).mp
  simp only [ENNReal.toReal_mul,
    ENNReal.toReal_ofReal history.trace.transitionMass_pos.le,
    ENNReal.toReal_ofReal (setup.proposalRecoveryModel.ownPlayReachProbability_nonneg _ _)]
  exact setup.proposalRecovery_historyReach_foreign_products values omission bad delivery focal
    history

end Vegas.SourceProgram.Setup
