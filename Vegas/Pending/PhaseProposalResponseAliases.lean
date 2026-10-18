/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Pending.PhaseCountMenu
import GameTheoryExtensions.Math.Probability.ActionSplitting

/-! # Full-support splitting over actual counted response preimages

The class of a response records its typed binding preparation, when there is
one, and its actual emitted packet. Private evidence-request menus need not
agree between different catalogues. Splitting uses the finite preimage in the
current literal local menu and preserves its aggregate class law exactly.
These are local action laws, not assertions about conditional beliefs.
-/

noncomputable section

namespace Vegas.EventGraphRuntime.PhaseProposal

open Interaction GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] [Fintype Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}
  (runtime : EventGraphRuntime graph)
  (leaks : MessageNetwork.ObservationRule Player (CommitAttemptPacket graph))
  (bounds : MessageBounds graph) (who : Player)
  (past : List (phaseApplication runtime leaks).PlayerEntry)
  (view : (phaseApplication runtime leaks).PlayerView)

local notation "app" => phaseApplication runtime leaks

/-- Counted response syntax available at this exact ordinary input. -/
abbrev Response :=
  { response : (app).Action // response ∈ PhaseCount.onePacketActions runtime leaks bounds
    who past view }

/-- Missing and mistyped binding preparations have the same source failure
class. Other packet constructors introduce no binding meaning. -/
def bindingPreparation (material : WitnessedSubmission graph) : Option (Raw L) :=
  match material.call.packet with
  | .commitment event _ =>
      match graph.outputLayout event with
      | .binding _ payload => (material.call.opening.bind (fun raw => raw.as? payload)).map
          fun value => ⟨payload, value⟩
      | .publication .. | .privateInput .. | .publicData .. => none
  | .opening .. | .malformed .. => none

/-- The source binding class and actual public packet, before arbitrary aliases
are split. Wrong-type catalogues are not claimed operationally identical. -/
def responseClass (response : Response runtime leaks bounds who past view) :
    Option (Raw L) × Option (CommitAttemptPacket graph) :=
  (response.1.transmission.bind bindingPreparation,
    response.1.transmission.map fun material =>
      (PhaseCount.localEnvelope runtime leaks who past view material).payload)

/-- Only classes with a real response in this local menu are sampled. -/
abbrev ResponseClass := Set.range (responseClass runtime leaks bounds who past view)

def projectResponse (response : Response runtime leaks bounds who past view) :
    ResponseClass runtime leaks bounds who past view :=
  ⟨responseClass runtime leaks bounds who past view response, response, rfl⟩

def canonicalResponse (chosen : ResponseClass runtime leaks bounds who past view) :
    Response runtime leaks bounds who past view := Classical.choose chosen.2

theorem project_canonicalResponse (chosen : ResponseClass runtime leaks bounds who past view) :
    projectResponse runtime leaks bounds who past view
        (canonicalResponse runtime leaks bounds who past view chosen) = chosen := by
  apply Subtype.ext
  exact Classical.choose_spec chosen.2

/-- Positive alias noise reaches every actual preimage, without adding a
response unavailable in this player's catalogue or evidence menu. -/
def splitResponseLaw (law : PMF (ResponseClass runtime leaks bounds who past view))
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    PMF (Response runtime leaks bounds who past view) :=
  law.bind (PMF.splitKernel (projectResponse runtime leaks bounds who past view)
    (canonicalResponse runtime leaks bounds who past view)
    (project_canonicalResponse runtime leaks bounds who past view)
    weight nonnegative atMostOne)

theorem splitResponseLaw_project (law : PMF (ResponseClass runtime leaks bounds who past view))
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) :
    (splitResponseLaw runtime leaks bounds who past view law weight nonnegative atMostOne).map
        (projectResponse runtime leaks bounds who past view) = law :=
  PMF.split_project _ _ _ law weight nonnegative atMostOne

theorem splitResponseLaw_fullSupport
    (law : PMF (ResponseClass runtime leaks bounds who past view)) (mixed : FullSupport law)
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1) (positive : 0 < weight) :
    FullSupport (splitResponseLaw runtime leaks bounds who past view
      law weight nonnegative atMostOne) :=
  PMF.split_fullSupport _ _ _ law mixed weight nonnegative atMostOne positive

/-- The exact local probability factor after summing submission aliases. -/
theorem splitResponseLaw_probability
    (law : PMF (ResponseClass runtime leaks bounds who past view))
    (weight : ℝ) (nonnegative : 0 ≤ weight) (atMostOne : weight ≤ 1)
    (response : Response runtime leaks bounds who past view) :
    ((splitResponseLaw runtime leaks bounds who past view law weight nonnegative atMostOne)
        response).toReal =
      (law (projectResponse runtime leaks bounds who past view response)).toReal *
        ((PMF.splitKernel (projectResponse runtime leaks bounds who past view)
          (canonicalResponse runtime leaks bounds who past view)
          (project_canonicalResponse runtime leaks bounds who past view)
          weight nonnegative atMostOne
          (projectResponse runtime leaks bounds who past view response))
            response).toReal :=
  PMF.split_prob _ _ _ law weight nonnegative atMostOne response

end Vegas.EventGraphRuntime.PhaseProposal
