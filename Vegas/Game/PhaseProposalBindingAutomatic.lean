/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Game.PhaseProposalBindingKernel

/-! # Actual excluded binding closure preserves the emission potential -/

noncomputable section

namespace Vegas

open SourceProgram EventGraph EventGraphRuntime Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L]
  (setup : Setup (Player := Player) (L := L)) (mode : ExecutionMode)
  (runtime : EventGraphRuntime (serviceGraph setup mode))
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket (serviceGraph setup mode)))
  (plan : RuntimePhasePlan (serviceGraph setup mode))

local notation "app" => phaseApplication runtime leaks
local notation "graph" => serviceGraph setup mode

/-- The actual automatic graph failure of an inherited excluded owner is
the fixed failure kernel of the current binding potential. It adds no native
owner response and does not grow the exclusion record. -/
theorem phaseProposalBindingPotentialProfile_automatic
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (commitment : phase.kind = .commitment)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (state : RecoveryState (graph))
    (excluded : state.excluded = anchor.application.current.excluded)
    (event : (graph).EventId) (inside : event ∈ phase.events)
    (eligible : state.AutomaticReady event) :
    let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor
      phase values
    (graph).canonicalContinuation profile (state.completeAutomatic event eligible).native.config =
      (graph).canonicalContinuation profile state.native.config := by
  intro profile
  obtain ⟨owner, actor, inactive⟩ := eligible.owned
  have fields := phase.fields event ((phase.mem_events event).mp inside).1
    ((phase.mem_events event).mp inside).2
  rw [commitment] at fields
  obtain ⟨bindingOwner, bindingType, bindingKind⟩ := fields
  cases node : nodeView (graph) event with
  | bind actual payload outputEq codeEq =>
      have acting : (graph).actor? event = some actual := nodeView_bind_actor outputEq codeEq
      have same : actual = owner := Option.some.inj (acting.symm.trans actor)
      have excludedActual : actual ∈ anchor.application.current.excluded := by
        rw [same, ← excluded]
        exact inactive
      let failed : (graph).Action event := cast (congrArg EventField.Action outputEq.symm)
        (PublicationResult.failure : PublicationResult (L.Val payload))
      have law : (graph).normalizePolicy actual (profile actual) event acting
          ((graph).playerObserve actual state.native.config) = PMF.pure failed := by
        rw [phaseProposalBindingPotentialProfile_normalize]
        simp only [phaseProposalBindingPotentialProfile, node]
        rw [dite_eq_left True.intro,
          ite_eq_right (show ¬ (event ∈ phase.events ∧
            actual ∉ anchor.application.current.excluded) from fun valid =>
              valid.2 excludedActual), PMF.pure_map]
      have step : (graph).normalizedPolicyStep profile state.native.config event eligible.1 =
          PMF.pure (state.completeAutomatic event eligible).native.config := by
        have owned : (graph).normalizedPolicyStep profile state.native.config event eligible.1 =
            ((graph).normalizePolicy actual (profile actual) event acting
              ((graph).playerObserve actual state.native.config)).bind
                (state.native.config.step event eligible.1) := by
          unfold normalizedPolicyStep
          split
          · rename_i selected selectedActor
            have equal : selected = actual := Option.some.inj (selectedActor.symm.trans acting)
            subst selected
            rfl
          · rename_i absent
            rw [absent] at acting
            cases acting
        rw [owned, law, PMF.pure_bind]
        rw [state.native.config.step_eq_map_of_code event eligible.1 outputEq (.bind actual payload)
          codeEq PublicationResult.failure (PMF.pure PublicationResult.failure) rfl,
          PMF.pure_map]
        simp only [RecoveryState.completeAutomatic, State.completeFailure, node, State.complete]
      have harmonic := phaseProposalBindingPotentialProfile_harmonic setup mode runtime leaks plan
        anchor phase values state.native.config event eligible.1
      rw [normalizedThenCanonical, step, PMF.pure_bind] at harmonic
      exact harmonic
  | resolve actor payload binding checks outputEq codeEq =>
      cases outputEq.symm.trans bindingKind
  | sample payload law outputEq codeEq =>
      cases outputEq.symm.trans bindingKind

/-- The SAME finite automatic closure already used by the actual application
preserves the potential, including a chain of inherited excluded coordinates.
No separate source runner or distributional assumption is introduced. -/
theorem phaseProposalBindingPotentialProfile_drainFuel
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (commitment : phase.kind = .commitment)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1)) :
    ∀ fuel (state : RecoveryState (graph)),
      state.excluded = anchor.application.current.excluded →
      let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor
        phase values
      (graph).canonicalContinuation profile (phase.drainFuel fuel state).native.config =
        (graph).canonicalContinuation profile state.native.config := by
  intro fuel
  induction fuel with
  | zero => intro state _excluded; rfl
  | succ fuel ih =>
      intro state excluded
      unfold RuntimePhase.drainFuel
      split
      · rename_i pending
        let event := Classical.choose pending
        have inside := (Classical.choose_spec pending).1
        have eligible := (Classical.choose_spec pending).2
        exact (ih (state.completeAutomatic event eligible) excluded).trans
          (phaseProposalBindingPotentialProfile_automatic setup mode runtime leaks plan anchor
            phase commitment values state excluded event inside eligible)
      · rfl

/-- Automatic closure may be performed immediately after retaining an actual
SEND. Its intermediate graph failures remain inherited automatic NONE source
positions rather than new player emissions. -/
theorem phaseProposalBindingPotentialProfile_drain
    (anchor : (app).Execution) (phase : RuntimePhase (graph))
    (commitment : phase.kind = .commitment)
    (values : ∀ who (key : setup.ProposalRecoveryComponent who),
      PMF (setup.CommitRecoveryValueChoice who key.1))
    (state : RecoveryState (graph))
    (excluded : state.excluded = anchor.application.current.excluded) :
    let profile := phaseProposalBindingPotentialProfile setup mode runtime leaks plan anchor
      phase values
    (graph).canonicalContinuation profile (phase.drain state).native.config =
      (graph).canonicalContinuation profile state.native.config :=
  phaseProposalBindingPotentialProfile_drainFuel setup mode runtime leaks plan anchor phase
    commitment values state.native.config.remaining state excluded

end Vegas
