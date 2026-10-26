/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketCounterpartDomination

/-! # Irregular step bounds from response masses

The mass of a response step is the mass the responder's policy, at its recall
and view, gives the response (`Vegas.responseMass`,
`Vegas.stepProb_eq_responseMass`); it reads the responder's state and the joint
action only. So wherever an irregular response of positive mass has positive
operational mass, the response mass divided by the operational mass is an
irregular step bound (`Vegas.IrregularStepBound.ofResponseMass`). Under a
slot-trembled component, a response outside its main, alternative and slot
tiers has response mass at most the cube of the scale
(`Vegas.responseMass_le_of_slotTrembled`), so that bound is at most the cube of
the scale divided by the operational mass.
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Math.Probability Interaction EventGraphRuntime

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L] {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}

variable (setup runtime leaks bounds horizon scheduler) in
/-- **The response mass** of a joint action at a control state: the mass the
acting player's policy, at its recall and view, gives its response; one when
nobody acts. -/
def responseMass (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (control : (application setup runtime leaks).Control)
    (joint : Player → Option (application setup runtime leaks).Action) : ℝ :=
  match control.actor with
  | some actor => (((profile actor (some (control.execution.recall actor,
      control.execution.observe (application setup runtime leaks) actor))).map Subtype.val)
        (joint actor)).toReal
  | none => 1

theorem responseMass_nonneg (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (control : (application setup runtime leaks).Control)
    (joint : Player → Option (application setup runtime leaks).Action) :
    0 ≤ responseMass setup runtime leaks bounds horizon scheduler profile control joint := by
  unfold responseMass
  split
  · exact ENNReal.toReal_nonneg
  · exact zero_le_one

/-- **A response step has its response mass.** -/
theorem stepProb_eq_responseMass (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    {before after : (application setup runtime leaks).ProtocolState}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      before
      ⟨joint, legal⟩).support) (control : (application setup runtime leaks).Control)
    (initialized : before = some control) {actor : Player} (acting : control.actor = some actor) :
    InformationModel.stepProb (onePacketInformation setup runtime leaks bounds horizon scheduler)
        profile prior ⟨joint, legal⟩ after =
      responseMass setup runtime leaks bounds horizon scheduler profile control joint := by
  rw [response_stepProb (runtime := runtime) profile prior joint legal realized control
    initialized acting]
  unfold responseMass
  rw [acting]
  have general : ∀ info (_ : info = some (control.execution.recall actor,
      control.execution.observe (application setup runtime leaks) actor))
      (choice : (onePacketInformation setup runtime leaks bounds horizon scheduler).Choice actor
        info),
      choice.1 = joint actor →
      (profile actor info choice).toReal =
        (((profile actor (some (control.execution.recall actor,
          control.execution.observe (application setup runtime leaks) actor))).map Subtype.val)
            (joint actor)).toReal := by
    rintro info rfl choice value
    rw [← value, pmf_map_apply_of_injective _ Subtype.val_injective]
  apply general
  · rw [onePacket_infoOf]
    subst initialized
    simp only [ReactiveApplication.observe, acting, ↓reduceIte]
  · rfl

variable {sequence : ℕ → setup.intendedModel.BehavioralAssessment}
  {profiles : ℕ → ∀ player,
    (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player}
  {who : Player}

open Classical in
/-- **Irregular step bounds from response masses.** If every irregular response
of positive response mass has positive operational mass, the response mass
divided by the operational mass bounds every irregular response. -/
def IrregularStepBound.ofResponseMass
    (steps : OperationalSteps setup runtime leaks bounds horizon scheduler sequence profiles who)
    (positive : ∀ n {before after : (application setup runtime leaks).ProtocolState}
      (_ : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before) joint
        legal
      (_ : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step before
        ⟨joint, legal⟩).support) (control next : (application setup runtime leaks).Control),
      before = some control → after = some next →
      ¬ RegularStep setup runtime leaks bounds horizon scheduler (sequence n) who before joint
        after →
      0 < responseMass setup runtime leaks bounds horizon scheduler (profiles n) control joint →
      0 < steps.mass n (operationalState setup runtime leaks before)
        (operationalState setup runtime leaks after)) :
    IrregularStepBound setup runtime leaks bounds horizon scheduler steps where
  bound n control joint next :=
    responseMass setup runtime leaks bounds horizon scheduler (profiles n) control joint /
      steps.mass n (operationalState setup runtime leaks (some control))
        (operationalState setup runtime leaks (some next))
  bound_nonneg n control joint next :=
    div_nonneg (responseMass_nonneg (runtime := runtime) _ _ _) (steps.mass_nonneg _ _ _)
  step_le n {before after} prior joint legal realized control next
    initialized reached
      irregular := by
    subst initialized reached
    have acting : ∃ actor, control.actor = some actor := by
      by_contra none_
      apply irregular
      intro actor acting
      exact (none_ ⟨actor, acting⟩).elim
    obtain ⟨actor, acting⟩ := acting
    rw [stepProb_eq_responseMass (runtime := runtime) (profiles n) prior joint legal realized
      control rfl acting]
    rcases (responseMass_nonneg (runtime := runtime) (profiles n) control joint).lt_or_eq with
      massPos | zero
    · have opPos := positive n prior joint legal realized control next rfl rfl irregular massPos
      rw [div_mul_cancel₀ _ opPos.ne']
    · rw [← zero]
      exact mul_nonneg (div_nonneg le_rfl (steps.mass_nonneg _ _ _))
        (steps.mass_nonneg _ _ _)

/-- **A response outside every prescribed tier is in the full-menu tremble.**
If the acting player's policy at its recall and view is a slot-trembled
component whose main, alternative and slot-tier laws give the response no
mass, its response mass is at most the cube of the scale. -/
theorem responseMass_le_of_slotTrembled
    (profile : ∀ player,
      (onePacketInformation setup runtime leaks bounds horizon scheduler).BehavioralPolicy player)
    (control : (application setup runtime leaks).Control) {actor : Player}
    (acting : control.actor = some actor)
    (joint : Player → Option (application setup runtime leaks).Action) {scale : ℝ}
    (nonnegative : 0 ≤ scale) (le_one : scale ≤ 1)
    (main alternative slot : PMF ((onePacketInformation setup runtime leaks bounds horizon
      scheduler).Choice actor (some (control.execution.recall actor,
        control.execution.observe (application setup runtime leaks) actor))))
    (component : profile actor (some (control.execution.recall actor,
        control.execution.observe (application setup runtime leaks) actor)) =
      slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler scale
        nonnegative le_one actor _ main alternative slot)
    (outside : ∀ choice : (onePacketInformation setup runtime leaks bounds horizon
        scheduler).Choice actor (some (control.execution.recall actor,
          control.execution.observe (application setup runtime leaks) actor)),
      choice.1 = joint actor → main choice = 0 ∧ alternative choice = 0 ∧ slot choice = 0) :
    responseMass setup runtime leaks bounds horizon scheduler profile control joint ≤ scale ^ 3 :=
      by
  unfold responseMass
  rw [acting]
  simp only
  by_cases found : ∃ choice : (onePacketInformation setup runtime leaks bounds horizon
      scheduler).Choice actor (some (control.execution.recall actor,
        control.execution.observe (application setup runtime leaks) actor)), choice.1 = joint actor
  · obtain ⟨choice, value⟩ := found
    rw [← value, pmf_map_apply_of_injective _ Subtype.val_injective, component]
    obtain ⟨mainZero, alternativeZero, slotZero⟩ := outside choice value
    exact slotTrembledChoice_le_of_unprescribed setup runtime leaks bounds (initialLaw setup)
      horizon
      scheduler nonnegative le_one actor _ main alternative slot choice mainZero alternativeZero
      slotZero
  · have zero : ((profile actor (some (control.execution.recall actor,
        control.execution.observe (application setup runtime leaks) actor))).map Subtype.val)
          (joint actor) = 0 := by
      rw [PMF.map_apply]
      refine ENNReal.tsum_eq_zero.mpr fun choice => ?_
      split_ifs with same
      · exact (found ⟨choice, same.symm⟩).elim
      · rfl
    rw [zero, ENNReal.toReal_zero]
    exact pow_nonneg nonnegative 3

end Vegas
