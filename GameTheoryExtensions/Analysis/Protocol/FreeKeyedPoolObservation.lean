/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.FreeKeyedPools

/-! # Common observations of nonfree pooled components -/

noncomputable section

namespace GameTheory.Protocol.InformationModel

variable {Player : Type} {T : ExecutionProtocol Player} {N : InformationModel T}
  [Fintype T.History] [∀ who, DecidableEq (N.InfoState who)]
  {Key : Type*} {Opt Outcome : Type}
  {free keyed : N.InformationAgent N.playedInformation → Prop}
  {key : N.InformationAgent N.playedInformation → Key}

/-- One dependent pool plan selects the same operational option at two
keyed nonfree agents in the same pool. -/
theorem ownedKeyedIdentify_at_eq
    (parts : (p : FreeKeyedPool free keyed key) → FreeKeyedPart free keyed key Opt p)
    (first second : N.InformationAgent N.playedInformation)
    (firstOwned : ownedKeyed free keyed first) (secondOwned : ownedKeyed free keyed second)
    (samePool : freeKeyedPool free keyed key first = freeKeyedPool free keyed key second) :
    ownedKeyedIdentify firstOwned (parts (freeKeyedPool free keyed key first)) =
      ownedKeyedIdentify secondOwned (parts (freeKeyedPool free keyed key second)) := by
  change cast _ (parts (freeKeyedPool free keyed key first)) =
    cast _ (parts (freeKeyedPool free keyed key second))
  have sameParts : HEq (parts (freeKeyedPool free keyed key first))
      (parts (freeKeyedPool free keyed key second)) := by rw [samePool]
  exact eq_of_heq ((cast_heq _ _).trans (sameParts.trans (cast_heq _ _).symm))

/-- The same actual pool weights give the same observed mixture at two
nonfree agents whenever the prescribed and each keyed law have the same
observation. All parts retain their original weights. -/
theorem bind_freeKeyedComponent_map_eq_of_not_free
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (weights : (p : FreeKeyedPool free keyed key) → PMF (FreeKeyedPart free keyed key Opt p))
    (observe : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → Outcome)
    (first second : N.InformationAgent N.playedInformation)
    (notFree : ¬ free first)
    (samePool : freeKeyedPool free keyed key first = freeKeyedPool free keyed key second)
    (prescribedSame : (prescribed first).map (observe first) =
      (prescribed second).map (observe second))
    (keyedSame : ∀ option, (keyedLaw first option).map (observe first) =
      (keyedLaw second option).map (observe second)) :
    ((weights (freeKeyedPool free keyed key first)).bind
        (freeKeyedComponent freeLaw prescribed keyedLaw first)).map (observe first) =
      ((weights (freeKeyedPool free keyed key second)).bind
        (freeKeyedComponent freeLaw prescribed keyedLaw second)).map (observe second) := by
  have compareAt (p : FreeKeyedPool free keyed key)
      (left : freeKeyedPool free keyed key first = p)
      (_right : freeKeyedPool free keyed key second = p) :
      ((weights p).bind (freeKeyedComponentAt freeLaw prescribed keyedLaw first p)).map
          (observe first) =
        ((weights p).bind (freeKeyedComponentAt freeLaw prescribed keyedLaw second p)).map
          (observe second) := by
    rw [PMF.map_bind, PMF.map_bind]
    cases p with
    | inl owner =>
      rw [freeKeyedPool_of_not_free notFree] at left
      cases left
    | inr p =>
      apply congrArg (fun kernel => (weights (.inr p)).bind kernel)
      funext part
      cases p with
      | none => exact prescribedSame
      | some value => exact keyedSame part
  exact (compareAt _ rfl samePool.symm).trans
    (congrArg (fun p => ((weights p).bind
      (freeKeyedComponentAt freeLaw prescribed keyedLaw second p)).map (observe second)) samePool)

end GameTheory.Protocol.InformationModel
