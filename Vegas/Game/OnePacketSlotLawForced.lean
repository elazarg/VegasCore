/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

import Vegas.Game.OnePacketSlotLawDischarge
import Vegas.Game.OnePacketDisclosureResolves

/-! # Operational steps of the certificate's profile

For a well-formed setup, every other player's canonical disclosure is canonical
at states forced for the observer (`Vegas.disclosureCanonical_of_resolves`,
`Vegas.disclosureResolves_of_forced`). So the slot law of the certificate's
profile holds at every response from a state forced for the observer, with no
further hypothesis on disclosures (`Vegas.certificate_slotLaw_forced`), and the
certificate's profile, with any pool weights, has the operational steps of the
factorization (`Vegas.certificateOperationalSteps`).
-/

noncomputable section

namespace Vegas

open SourceProgram

open GameTheory GameTheory.Protocol GameTheory.Protocol.ExecutionProtocol
  GameTheory.Protocol.InformationModel GameTheory.Math.Probability Interaction
  EventGraphRuntime Filter

variable {Player : Type} [DecidableEq Player] [Fintype Player] {L : IExpr}
  [IExpr.ResultTypes L]
  {setup : Setup (Player := Player) (L := L)}
  {runtime : EventGraphRuntime (graph setup)}
  {leaks : MessageNetwork.ObservationRule Player (WitnessedPacket (graph setup))}
  {bounds : MessageBounds (graph setup)} {horizon : Nat}
  {scheduler : (application setup runtime leaks).Scheduler}
  [(application setup runtime leaks).FiniteNature (initialLaw setup) scheduler]
  [∀ who, DecidableEq ((onePacketModel setup runtime leaks bounds (initialLaw setup) horizon
    scheduler).InfoState who)]

/-- **The slot law of the certificate's profile, from forcedness.** For a
well-formed setup, at every response step of the one-packet game by a forced
player other than the observer, from a state forced for the observer, with
positive content, the certificate's profile at the responder's information is
a slot-trembled component whose laws give the realized choice its content
factor times factors whose slot combination is the step response, and the cube
of the scale stays within the error. -/
theorem certificate_slotLaw_forced (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]
    (floored : ∀ n, floor n ≤ contentFloor setup runtime leaks bounds horizon scheduler (sequence
      n))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (who : Player) (n : ℕ) {before after : (application setup runtime leaks).ProtocolState}
    (prior : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Trace before)
    (joint : Player → Option (application setup runtime leaks).Action)
    (legal : (onePacketProtocol setup runtime leaks bounds horizon scheduler).Legal before joint)
    (realized : after ∈ ((onePacketProtocol setup runtime leaks bounds horizon scheduler).step
      before
      ⟨joint, legal⟩).support) (control next : (application setup runtime leaks).Control)
    (actor : Player) (initialized : before = some control) (reached : after = some next)
    (acting : control.actor = some actor) (other : actor ≠ who)
    (forced : forcedAgent (runtime := runtime) (bounds.onePacketMenu runtime leaks) (initialLaw
      setup) horizon
      scheduler actor ((application setup runtime leaks).observe actor (some control)))
    (observerForced : ForcedState setup runtime leaks who (some control))
    (positive : 0 < contentFactor setup runtime leaks (sequence n) actor control.execution
      next.execution
      ((joint actor).getD ⟨none⟩)) :
    ∃ (main alternative slot : PMF ((onePacketInformation setup runtime leaks bounds horizon
        scheduler).Choice actor
          ((onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf actor prior)))
      (mainFactor' alternativeFactor slotFactor : ℝ),
      certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
          scale_le_one weights n actor
          ((onePacketInformation setup runtime leaks bounds horizon scheduler).infoOf actor prior) =
        slotTrembledChoice setup runtime leaks bounds (initialLaw setup) horizon scheduler (scale n)
          (scale_pos n).le (scale_le_one n) actor _ main alternative slot ∧
      (main (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor)).toReal =
        contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) * mainFactor' ∧
      (alternative (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor)).toReal =
        contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) * alternativeFactor ∧
      (slot (InformationModel.choicesOfLegal _ prior ⟨joint, legal⟩ actor)).toReal =
        contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) * slotFactor ∧
      slotCombination (scale n) mainFactor' alternativeFactor slotFactor =
        stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks bounds horizon
          scheduler (weights n))
          (scale n) (operationalState setup runtime leaks before) (operationalState setup runtime
            leaks after) ∧
      scale n ^ 3 ≤ slotError (scale n) (floor n) (trembleSlots setup bounds).card *
        (contentFactor setup runtime leaks (sequence n) actor control.execution next.execution
          ((joint actor).getD ⟨none⟩) *
        stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks bounds horizon
          scheduler (weights n))
          (scale n) (operationalState setup runtime leaks before)
          (operationalState setup runtime leaks after)) :=
  certificate_slotLaw (runtime := runtime) sequence scale scale_pos scale_le_one small floor
    floor_pos floored covers
    capacity weights who
    (fun trace responder forcedState different => disclosureCanonical_of_resolves (runtime :=
      runtime) trace
      responder (disclosureResolves_of_forced (runtime := runtime) wellFormed trace who responder
        forcedState
        different))
    n prior joint legal realized control next actor initialized reached acting other forced
    positive (initialized ▸ observerForced)

/-- **The operational steps of the certificate's profile.** For a well-formed
setup, under bounds adequacy, a tremble scale at most a quarter and an
error-vanishing floor sequence below the content floor, the certificate's
profile with any pool weights has the operational steps of the factorization. -/
def certificateOperationalSteps (wellFormed : setup.WellFormed)
    (sequence : ℕ → setup.intendedModel.BehavioralAssessment)
    (scale : ℕ → ℝ) (scale_pos : ∀ n, 0 < scale n) (scale_le_one : ∀ n, scale n ≤ 1)
    (small : ∀ n, scale n ≤ 1 / 4) (floor : ℕ → ℝ) (floor_pos : ∀ n, 0 < floor n)
    [Finite (onePacketProtocol setup runtime leaks bounds horizon scheduler).History]
    (floored : ∀ n, floor n ≤ contentFloor setup runtime leaks bounds horizon scheduler (sequence
      n))
    (covers : bounds.CoversOutputValues)
    (capacity : ∀ who, bindingEventCount (graph setup) who < bounds.candidateCount)
    {slots : Nat}
    (weights : ℕ → ∀ p, PMF (OnePacketPart setup runtime leaks bounds horizon scheduler slots p))
    (who : Player)
    (error_tendsto : Tendsto (fun n => slotError (scale n) (floor n)
      (trembleSlots setup bounds).card) atTop (nhds 0)) :
    OperationalSteps setup runtime leaks bounds horizon scheduler sequence
      (certificateProfile setup runtime leaks bounds horizon scheduler sequence scale scale_pos
        scale_le_one weights) who :=
  OperationalSteps.ofSlotComponents (runtime := runtime)
    (fun n => stepResponse (runtime := runtime) bounds (keyWeights setup runtime leaks bounds
      horizon scheduler (weights n))
      (scale n))
    (fun n => slotError (scale n) (floor n) (trembleSlots setup bounds).card)
    (fun n => stepResponse_nonneg (runtime := runtime) bounds _ (scale_pos n).le (scale_le_one n))
    (fun n => slotError_nonneg (scale_pos n).le (floor_pos n) _) error_tendsto
    fun n _ _ prior joint legal realized control next actor initialized reached acting other
      forced observerForced positive =>
      ⟨scale n, (scale_pos n).le, scale_le_one n,
        certificate_slotLaw_forced (runtime := runtime) wellFormed sequence scale scale_pos
          scale_le_one small floor
          floor_pos floored covers capacity weights who n prior joint legal realized control next
          actor initialized reached acting other forced observerForced positive⟩

end Vegas
