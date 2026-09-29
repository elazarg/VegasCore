/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheory.Protocol.PolicyRandomization
import GameTheory.Protocol.Strategic
import GameTheoryExtensions.Protocol.FiniteInformation
import GameTheoryExtensions.Math.Probability.Support

/-! # The finite agent normal form uses the original protocol evaluator

An agent chooses one legal action at one covered information value. Independent
mixed agent choices induce exactly ordinary behavioral execution when an
information value cannot be visited twice with a consequential choice.
This is an analysis of the existing protocol, not another execution layer.
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open GameTheory.Math.Probability

variable {ι : Type} {E : ExecutionProtocol ι} (M : InformationModel E)

abbrev InformationAgent (sites : (who : ι) → Finset (M.InfoState who)) :=
  Σ who, {info // info ∈ sites who}

def informationAgentForm (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who) (fuel : Nat) :
    GameForm (M.InformationAgent sites) where
  sig := {
    Strategy := fun agent => M.Choice agent.1 agent.2.1
    Outcome := E.History }
  play actions := by
    classical
    exact M.runFrom (fun who => FiniteAssignment.resolve (fallback who) (sites who)
      (fun info => actions ⟨who, info⟩)) fuel E.initHistory

def agentBehavior (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who)
    (laws : (agent : M.InformationAgent sites) → PMF (M.Choice agent.1 agent.2.1)) :
    Profile M.behavioralSignature := by
  classical
  exact fun who info =>
    if present : info ∈ sites who then laws ⟨who, ⟨info, present⟩⟩
    else PMF.pure (fallback who info)

@[simp] theorem agentBehavior_at (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who)
    (laws : (agent : M.InformationAgent sites) → PMF (M.Choice agent.1 agent.2.1))
    (agent : M.InformationAgent sites) :
    M.agentBehavior sites fallback laws agent.1 agent.2.1 = laws agent := by
  simp only [agentBehavior, dite_eq_left agent.2.2]

private theorem pi_sigma [Fintype ι] {Index : ι → Type*} [∀ who, Fintype (Index who)]
    {Value : (Σ who, Index who) → Type*}
    (laws : (agent : Σ who, Index who) → PMF (Value agent)) :
    (independentProduct laws).map (fun actions who info => actions ⟨who, info⟩) =
      independentProduct (fun who => independentProduct (fun info => laws ⟨who, info⟩)) := by
  classical
  have injective : Function.Injective
      (fun (actions : (agent : Σ who, Index who) → Value agent) who info =>
        actions ⟨who, info⟩) := by
    intro first second same
    funext agent
    exact congrFun (congrFun same agent.1) agent.2
  ext actions
  refine (pmf_map_apply_of_injective (independentProduct laws) injective
    (fun agent => actions agent.1 agent.2)).trans ?_
  simp only [independentProduct_apply, Fintype.prod_sigma]

/-- The mixed agent game and behavioral play have the same complete history
law, with no conditioning or equilibrium premise. -/
theorem informationAgentForm_mixed_play [Fintype ι]
    (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who) (fuel : Nat)
    (once : M.ActsOnceWhereItMatters) (covered : M.CoversInformationSites sites fuel)
    (laws : (agent : M.InformationAgent sites) → PMF (M.Choice agent.1 agent.2.1)) :
    (M.informationAgentForm sites fallback fuel).mixed.play laws =
      M.runBehavioral (M.agentBehavior sites fallback laws) fuel := by
  classical
  let assemble : ((agent : M.InformationAgent sites) → M.Choice agent.1 agent.2.1) →
      Profile M.strategicSignature := fun actions who =>
    FiniteAssignment.resolve (fallback who) (sites who) (fun info => actions ⟨who, info⟩)
  have policyLaw : (independentProduct laws).map assemble = independentProduct (fun who =>
      (M.agentBehavior sites fallback laws who).toMixedWithin M (sites who) (fallback who)) := by
    calc
      _ = ((independentProduct laws).map (fun actions who info => actions ⟨who, info⟩)).map
          (fun plans who => FiniteAssignment.resolve (fallback who) (sites who) (plans who)) := by
            rw [PMF.map_comp]
            rfl
      _ = (independentProduct (fun who => independentProduct (fun info => laws ⟨who, info⟩))).map
          (fun plans who => FiniteAssignment.resolve (fallback who) (sites who) (plans who)) := by
            exact congrArg
              (PMF.map (fun plans who =>
                FiniteAssignment.resolve (fallback who) (sites who) (plans who)))
              (pi_sigma (Index := fun who => {info // info ∈ sites who})
                (Value := fun agent => M.Choice agent.1 agent.2.1) laws)
      _ = independentProduct (fun who => (independentProduct (fun info => laws ⟨who, info⟩)).map
          (FiniteAssignment.resolve (fallback who) (sites who))) :=
            (independentProduct_map (fun who => independentProduct fun info => laws ⟨who, info⟩)
              (fun who => FiniteAssignment.resolve (fallback who) (sites who)))
      _ = _ := by
        congr 1
        funext who
        rw [BehavioralPolicy.toMixedWithin_eq_sampleOn, FiniteAssignment.sampleOn]
        congr 1
        congr 1
        funext info
        exact (M.agentBehavior_at sites fallback laws ⟨who, info⟩).symm
  calc
    _ = ((independentProduct laws).map assemble).bind (fun profile => M.runFrom profile fuel
        E.initHistory)
        := by rw [PMF.bind_map]; rfl
    _ = M.runMixed (fun who =>
        (M.agentBehavior sites fallback laws who).toMixedWithin M (sites who) (fallback who))
          fuel :=
      congrArg (fun distribution => distribution.bind
        (fun profile => M.runFrom profile fuel E.initHistory)) policyLaw
    _ = _ := M.runMixed_toMixedWithin once sites _ fallback fuel covered

/-- A unilateral information-agent deviation changes exactly one local law
of the original player's behavioral policy. -/
theorem agentBehavior_update [DecidableEq ι]
    [∀ who, DecidableEq (M.InfoState who)]
    (sites : (who : ι) → Finset (M.InfoState who))
    (fallback : (who : ι) → M.Policy who)
    (laws : (agent : M.InformationAgent sites) → PMF (M.Choice agent.1 agent.2.1))
    (agent : M.InformationAgent sites) (replacement : PMF (M.Choice agent.1 agent.2.1)) :
    M.agentBehavior sites fallback
        (Profile.update (sig := (M.informationAgentForm sites fallback 0).sig.mixed)
          laws agent replacement) =
      Profile.update (sig := M.behavioralSignature) (M.agentBehavior sites fallback laws)
        agent.1 ((M.agentBehavior sites fallback laws agent.1).withLaw agent.2.1 replacement) := by
  classical
  funext who info
  by_cases samePlayer : who = agent.1
  · subst who
    rw [Profile.update_same]
    by_cases sameInfo : info = agent.2.1
    · subst info
      rw [M.agentBehavior_at sites fallback _ agent, Profile.update_same,
        BehavioralPolicy.withLaw_self]
    · rw [BehavioralPolicy.withLaw_of_ne _ _ _ sameInfo]
      unfold agentBehavior
      split
      · rename_i present
        apply Profile.update_of_ne
        intro equal
        have same := eq_of_heq (Sigma.mk.inj equal).2
        exact sameInfo (congrArg Subtype.val same)
      · rfl
  · rw [Profile.update_of_ne _ _ samePlayer]
    unfold agentBehavior
    split
    · rename_i present
      apply Profile.update_of_ne
      intro equal
      exact samePlayer (congrArg Sigma.fst equal)
    · rfl

end GameTheory.Protocol.InformationModel
