/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.KeyedPools

/-! # Free agents beside keyed pools

Agents are split into free agents, keyed agents and the rest. A free agent sits
alone in its pool, whose parts are its choices; its component of a choice is a
free law of that choice, typically the choice trembled toward a fixed
reference. The other agents are pooled as in
`GameTheory.Protocol.InformationModel.keyedPool`
(`GameTheory.Protocol.InformationModel.freeKeyedPool`,
`GameTheory.Protocol.InformationModel.FreeKeyedPart`,
`GameTheory.Protocol.InformationModel.freeKeyedComponent`).

When the free laws converge to the pure choices, the limit components of a free
agent span all its local laws (`GameTheory.Protocol.InformationModel.freeKeyedSpanning`).
A free agent alone in its pool is rational among its component mixtures, so the
member-rationality obligation of a pooled limit certificate reduces to the
keyed pools (`GameTheory.Protocol.InformationModel.freeKeyedMemberRational`),
and the local comparisons are required only away from the free agents
(`GameTheory.Protocol.InformationModel.freeKeyedLocalComparisons`).
-/

noncomputable section

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol Math.Probability Filter

variable {Player : Type} {T : ExecutionProtocol Player} {N : InformationModel T}
  [Fintype T.History] [∀ who, DecidableEq (N.InfoState who)]

section Structure

variable {Key : Type*} (free keyed : N.InformationAgent N.playedInformation → Prop)
  (key : N.InformationAgent N.playedInformation → Key) (Opt : Type)

/-- The keyed agents that are not free. -/
def ownedKeyed (agent : N.InformationAgent N.playedInformation) : Prop :=
  keyed agent ∧ ¬ free agent

/-- The pools: one per free agent, and the keyed pools of the other agents. -/
abbrev FreeKeyedPool :=
  {agent : N.InformationAgent N.playedInformation // free agent} ⊕
    KeyedPool (ownedKeyed free keyed) key

open Classical in
/-- The pool of an agent: its own pool if it is free, its keyed pool otherwise. -/
def freeKeyedPool (agent : N.InformationAgent N.playedInformation) :
    FreeKeyedPool free keyed key :=
  if isFree : free agent then .inl ⟨agent, isFree⟩
  else .inr (keyedPool (ownedKeyed free keyed) key agent)

/-- The parts of a free agent's pool are its choices; the parts of a keyed pool
are its options. -/
def FreeKeyedPart : FreeKeyedPool free keyed key → Type
  | .inl agent => N.Choice agent.1.1 agent.1.2.1
  | .inr p => KeyedPart (ownedKeyed free keyed) key Opt p

instance [Finite Opt] (p : FreeKeyedPool free keyed key) :
    Finite (FreeKeyedPart free keyed key Opt p) := by
  cases p with
  | inl agent => exact N.finite_choice_of_played agent.1.2.2
  | inr p => unfold FreeKeyedPart; infer_instance

instance [Nonempty Opt] (p : FreeKeyedPool free keyed key) :
    Nonempty (FreeKeyedPart free keyed key Opt p) := by
  cases p with
  | inl agent => exact N.nonempty_choice_of_played agent.1.2.2
  | inr p => unfold FreeKeyedPart; infer_instance

variable {free keyed key Opt}

open Classical in
/-- A component at a pool: the free law of a free agent's choice, and the keyed
component otherwise. -/
def freeKeyedComponentAt
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (agent : N.InformationAgent N.playedInformation) :
    (p : FreeKeyedPool free keyed key) → FreeKeyedPart free keyed key Opt p →
      PMF (N.Choice agent.1 agent.2.1)
  | .inl owner, choice =>
      if same : owner.1 = agent then same ▸ freeLaw owner.1 choice else prescribed agent
  | .inr p, part => keyedComponentAt prescribed keyedLaw agent p part

/-- **The free and keyed components.** -/
def freeKeyedComponent
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (agent : N.InformationAgent N.playedInformation) :
    FreeKeyedPart free keyed key Opt (freeKeyedPool free keyed key agent) →
      PMF (N.Choice agent.1 agent.2.1) :=
  freeKeyedComponentAt freeLaw prescribed keyedLaw agent (freeKeyedPool free keyed key agent)

theorem freeKeyedPool_of_free {agent : N.InformationAgent N.playedInformation}
    (isFree : free agent) : freeKeyedPool free keyed key agent = .inl ⟨agent, isFree⟩ := by
  classical
  unfold freeKeyedPool
  simp only [isFree, ↓reduceDIte]

theorem freeKeyedPool_of_not_free {agent : N.InformationAgent N.playedInformation}
    (notFree : ¬ free agent) :
    freeKeyedPool free keyed key agent = .inr (keyedPool (ownedKeyed free keyed) key agent) := by
  classical
  unfold freeKeyedPool
  simp only [notFree, ↓reduceDIte]

/-- Only the free agent itself sits in its pool. -/
theorem eq_of_freeKeyedPool_eq_inl {agent : N.InformationAgent N.playedInformation}
    {owner : {agent : N.InformationAgent N.playedInformation // free agent}}
    (same : freeKeyedPool free keyed key agent = .inl owner) : agent = owner.1 := by
  classical
  by_cases isFree : free agent
  · rw [freeKeyedPool_of_free isFree] at same
    exact congrArg Subtype.val (Sum.inl.inj same)
  · rw [freeKeyedPool_of_not_free isFree] at same
    cases same

/-- The identification of a free agent's parts with its choices. -/
def freeIdentify {agent : N.InformationAgent N.playedInformation} (isFree : free agent) :
    FreeKeyedPart free keyed key Opt (freeKeyedPool free keyed key agent) ≃
      N.Choice agent.1 agent.2.1 :=
  Equiv.cast (congrArg (FreeKeyedPart free keyed key Opt) (freeKeyedPool_of_free isFree))

/-- A free agent's components are its free laws, read through the
identification of its parts with its choices. -/
theorem freeKeyedComponent_of_free
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    {agent : N.InformationAgent N.playedInformation} (isFree : free agent)
    (part : FreeKeyedPart free keyed key Opt (freeKeyedPool free keyed key agent)) :
    freeKeyedComponent freeLaw prescribed keyedLaw agent part =
      freeLaw agent (freeIdentify isFree part) := by
  have general : ∀ (p : FreeKeyedPool free keyed key) (same : p = .inl ⟨agent, isFree⟩)
      (part : FreeKeyedPart free keyed key Opt p),
      freeKeyedComponentAt freeLaw prescribed keyedLaw agent p part =
        freeLaw agent (cast (congrArg (FreeKeyedPart free keyed key Opt) same) part) := by
    intro p same part
    subst same
    simp [freeKeyedComponentAt]
  exact general _ (freeKeyedPool_of_free isFree) part

/-- A non-free agent's components are its keyed components. -/
theorem freeKeyedComponent_of_not_free
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    {agent : N.InformationAgent N.playedInformation} (notFree : ¬ free agent) :
    ∃ identify : FreeKeyedPart free keyed key Opt (freeKeyedPool free keyed key agent) ≃
        KeyedPart (ownedKeyed free keyed) key Opt (keyedPool (ownedKeyed free keyed) key agent),
      ∀ part, freeKeyedComponent freeLaw prescribed keyedLaw agent part =
        keyedComponent prescribed keyedLaw agent (identify part) := by
  unfold freeKeyedComponent
  rw [freeKeyedPool_of_not_free notFree]
  exact ⟨Equiv.refl _, fun _ => rfl⟩

/-- Fully supported free, prescribed and keyed laws make every component fully
supported. -/
theorem freeKeyedComponent_fullSupport
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (freeFull : ∀ agent choice, FullSupport (freeLaw agent choice))
    (prescribedFull : ∀ agent, FullSupport (prescribed agent))
    (keyedFull : ∀ agent option, FullSupport (keyedLaw agent option))
    (agent : N.InformationAgent N.playedInformation) :
    ∀ part, FullSupport (freeKeyedComponent (free := free) (keyed := keyed) (key := key)
      freeLaw prescribed keyedLaw agent part) := by
  by_cases isFree : free agent
  · intro part
    rw [freeKeyedComponent_of_free (key := key) freeLaw prescribed keyedLaw isFree]
    exact freeFull agent _
  · obtain ⟨identify, componentEq⟩ := freeKeyedComponent_of_not_free (key := key) freeLaw
      prescribed keyedLaw isFree
    intro part
    rw [componentEq]
    exact keyedComponent_fullSupport prescribed keyedLaw prescribedFull keyedFull agent _

end Structure

section Obligations

variable {Key : Type*} {free keyed : N.InformationAgent N.playedInformation → Prop}
  {key : N.InformationAgent N.playedInformation → Key} {Opt : Type}

/-- A non-free agent's component at its pool's part is its keyed component at
the corresponding keyed part, for any family of parts. -/
theorem freeKeyedComponent_at_not_free
    (freeLaw : ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (parts : ∀ p, FreeKeyedPart free keyed key Opt p)
    {agent : N.InformationAgent N.playedInformation} (notFree : ¬ free agent) :
    freeKeyedComponent freeLaw prescribed keyedLaw agent
        (parts (freeKeyedPool free keyed key agent)) =
      keyedComponent prescribed keyedLaw agent
        (parts (.inr (keyedPool (ownedKeyed free keyed) key agent))) := by
  change (fun p => freeKeyedComponentAt freeLaw prescribed keyedLaw agent p (parts p))
    (freeKeyedPool free keyed key agent) = _
  rw [freeKeyedPool_of_not_free notFree]
  rfl

variable (free keyed key Opt) in
/-- The best part of each pool: an arbitrary choice of a free agent, and the
keyed best part otherwise. -/
def freeKeyedBest [Nonempty Opt] (bestOf : Key → Opt) :
    (p : FreeKeyedPool free keyed key) → FreeKeyedPart free keyed key Opt p
  | .inl _ => Classical.arbitrary _
  | .inr p => keyedBest bestOf p

/-- **The free agents span their laws.** When each free law of a choice
converges to that choice, the limit components of a free agent are its pure
choices, which span all its local laws. -/
theorem freeKeyedSpanning [Fintype Player]
    (freeLaw : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (converges : ∀ agent choice,
      PMFConvergesPointwise (fun n => freeLaw n agent choice) (PMF.pure choice))
    [DecidablePred free] :
    ∀ who (site : N.InformationSite who), N.agentAt site ∈ Finset.univ.filter free →
      ∃ limitComponent : FreeKeyedPart free keyed key Opt
          (freeKeyedPool free keyed key (N.agentAt site)) → PMF (N.Choice who site.1),
        (∀ part, PMFConvergesPointwise (fun n => freeKeyedComponent (freeLaw n) (prescribed n)
          (keyedLaw n) (N.agentAt site) part) (limitComponent part)) ∧
        ∀ law : PMF (N.Choice who site.1), ∃ weights : PMF (FreeKeyedPart free keyed key Opt
          (freeKeyedPool free keyed key (N.agentAt site))),
          weights.bind limitComponent = law := by
  intro who site member
  have isFree : free (N.agentAt site) := (Finset.mem_filter.mp member).2
  let identify := freeIdentify (keyed := keyed) (key := key) (Opt := Opt) isFree
  refine ⟨fun part => PMF.pure (identify part), fun part => ?_, fun law =>
    ⟨law.map identify.symm, ?_⟩⟩
  · simp only [freeKeyedComponent_of_free (key := key) _ _ _ isFree]
    exact converges _ _
  · rw [PMF.bind_map]
    have : (fun part => PMF.pure (identify part)) ∘ identify.symm = PMF.pure := by
      funext choice
      simp
    rw [this, PMF.bind_pure]

end Obligations

section Certificate

variable [Fintype Player] [DecidableEq Player] {Outcome : Type*} {Key : Type*}
  (fuel : Nat) (bounded : T.BoundedHorizon fuel) (targetRecall : N.DecisionRecall)
  (observe : T.History → Outcome) (utility : Outcome → Player → ℝ)
  (fallback : ∀ who, N.Policy who)
  (free keyed : N.InformationAgent N.playedInformation → Prop) [DecidablePred free]
  (key : N.InformationAgent N.playedInformation → Key) {Opt : Type} [Nonempty Opt]

omit [DecidablePred free] in
include bounded in
open Classical in
/-- **Member rationality with free agents.** As
`GameTheory.Protocol.InformationModel.keyedMemberRational`, for the keyed
agents that are not free; a free agent alone in its pool is rational among its
component mixtures, and every other agent has one component. -/
theorem freeKeyedMemberRational [Finite Opt]
    (freeLaw : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (failed : N.InformationAgent N.playedInformation → Set T.History) (excluded : Player → ℝ)
    (pays : ∀ agent, ∀ history ∈ failed agent, utility (observe history) agent.1 =
      excluded agent.1)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (oneDimensional : ∀ (weights : ℕ → ∀ p, PMF (FreeKeyedPart free keyed key Opt p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (freeKeyedPool free keyed key agent)).bind
          (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → N.InformationAgent N.playedInformation → ℝ)
        (score : ℕ → Key → Opt → ℝ) (error drift : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧
        ∀ n (agent : N.InformationAgent N.playedInformation), ownedKeyed free keyed agent →
          ∀ decision : N.IsDecisionInfo agent.1 agent.2.1,
          excluded agent.1 ≤ continuation n agent + error n ∧
          continuation n agent - excluded agent.1 ≤ bound ∧
          (∀ option, |localSuccessValue fuel observe utility (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩ (failed agent) (keyedLaw n agent option) -
            (1 - localFailure fuel (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent) (keyedLaw n agent option)) * continuation n agent| ≤ error n) ∧
          ∀ option, |localFailure fuel (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent) (keyedLaw n agent option) - (1 - score n (key agent) option)| ≤
            drift n) :
    ∀ (weights : ℕ → ∀ p, PMF (FreeKeyedPart free keyed key Opt p))
      (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (freeKeyedPool free keyed key agent)).bind
          (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (FreeKeyedPart free keyed key Opt p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => freeKeyedPool free keyed key agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (freeKeyedPool free keyed key agent)).bind
                  (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who)
          (alternative : PMF (FreeKeyedPart free keyed key Opt
            (freeKeyedPool free keyed key (N.agentAt site)))),
          let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
            observe (targetSequence n) who
            (site, ((targetSequence n).strategy who).withLaw site.1
              (alternative.bind (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n)
                (N.agentAt site))))
          expect comparison.alternative (utility · who) -
            expect comparison.prescribed (utility · who) ≤ memberError n :=
  memberRational_of_success fuel bounded targetRecall observe utility fallback
    (freeKeyedPool free keyed key) (fun n => freeKeyedComponent (freeLaw n) (prescribed n)
      (keyedLaw n))
    {p | ∃ k, p = .inr (some k)} failed excluded pays bound bound_nonneg
    (fun weights targetSequence played mixed bayes => by
      let := Fintype.ofFinite Opt
      obtain ⟨continuation, score, error, drift, errorVanishes, driftVanishes, drift_nonneg,
        facts⟩ := oneDimensional weights targetSequence played mixed bayes
      refine ⟨continuation, fun n => freeKeyedBest free keyed key Opt
          (fun k => scoreArgmax (score n k)), error,
        fun n => 2 * drift n, errorVanishes, by simpa using driftVanishes.const_mul 2,
        fun n => by linarith [drift_nonneg n], fun n agent inDelivery decision => ?_⟩
      obtain ⟨k, poolEq⟩ := inDelivery
      have notFree : ¬ free agent := fun isFree => by
        rw [freeKeyedPool_of_free isFree] at poolEq
        cases poolEq
      have isKeyed : ownedKeyed free keyed agent := by
        rw [freeKeyedPool_of_not_free notFree] at poolEq
        exact (isSome_keyedPool_iff agent).mp (by rw [Sum.inr.inj poolEq]; rfl)
      obtain ⟨excluded_le, gap_le, near, common⟩ := facts n agent isKeyed decision
      obtain ⟨identify, componentEq⟩ := freeKeyedComponent_of_not_free (key := key)
        (freeLaw n) (prescribed n) (keyedLaw n) notFree
      have best := freeKeyedComponent_at_not_free (freeLaw n) (prescribed n) (keyedLaw n)
        (freeKeyedBest free keyed key Opt (fun k => scoreArgmax (score n k))) notFree
      rw [show freeKeyedBest free keyed key Opt (fun k => scoreArgmax (score n k))
          (.inr (keyedPool (ownedKeyed free keyed) key agent)) =
        keyedBest (fun k => scoreArgmax (score n k))
          (keyedPool (ownedKeyed free keyed) key agent) from rfl,
        keyedComponent_best_of_keyed (prescribed n) (keyedLaw n) _ isKeyed] at best
      refine ⟨excluded_le, gap_le, fun part => ?_, fun part => ?_⟩
      · obtain ⟨option, equal⟩ := keyedComponent_of_keyed (key := key) (prescribed n)
          (keyedLaw n) isKeyed (identify part)
        rw [componentEq, equal]
        exact near option
      · obtain ⟨option, equal⟩ := keyedComponent_of_keyed (key := key) (prescribed n)
          (keyedLaw n) isKeyed (identify part)
        change localFailure fuel (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
          (failed agent) (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) agent
            (freeKeyedBest free keyed key Opt (fun k => scoreArgmax (score n k))
              (freeKeyedPool free keyed key agent))) ≤ _
        rw [best, componentEq, equal]
        exact localFailure_scoreArgmax_le fuel (targetSequence n) (who := agent.1)
          ⟨agent.2.1, decision⟩ (failed agent) (score n (key agent)) (drift n)
          (keyedLaw n agent) common (keyedLaw n agent option) option (common option))
    (fun weights targetSequence played _ _ pooled => ⟨fun _ => 0, tendsto_const_nhds,
      fun n who site outside alternative => by
        change localGain fuel observe utility (targetSequence n) site _ ≤ 0
        by_cases isFree : free (N.agentAt site)
        · have single : Finset.univ.filter (fun agent =>
              freeKeyedPool free keyed key agent = freeKeyedPool free keyed key (N.agentAt site)) =
              {N.agentAt site} := by
            ext agent
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
            constructor
            · intro same
              rw [freeKeyedPool_of_free isFree] at same
              exact eq_of_freeKeyedPool_eq_inl same
            · intro same
              rw [same]
          have bound := pooled n (Function.update (weights n)
            (freeKeyedPool free keyed key (N.agentAt site)) alternative)
            (freeKeyedPool free keyed key (N.agentAt site))
          rw [single, Finset.sum_singleton, dite_eq_left site.2] at bound
          simp only [Function.update_self] at bound
          exact bound
        · have unkeyed : ¬ ownedKeyed free keyed (N.agentAt site) := fun isKeyed => by
            apply outside
            refine ⟨⟨key (N.agentAt site), ⟨N.agentAt site, isKeyed⟩, rfl⟩, ?_⟩
            rw [freeKeyedPool_of_not_free isFree, keyedPool_of_keyed isKeyed]
          obtain ⟨identify, componentEq⟩ := freeKeyedComponent_of_not_free (key := key)
            (freeLaw n) (prescribed n) (keyedLaw n) isFree
          have constant (law : PMF (FreeKeyedPart free keyed key Opt
              (freeKeyedPool free keyed key (N.agentAt site)))) :
              law.bind (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n)
                (N.agentAt site)) = prescribed n (N.agentAt site) := by
            have same : freeKeyedComponent (free := free) (keyed := keyed) (key := key)
                (freeLaw n) (prescribed n) (keyedLaw n) (N.agentAt site) =
                fun _ => prescribed n (N.agentAt site) := by
              funext part
              rw [componentEq]
              exact keyedComponent_of_not_keyed (prescribed n) (keyedLaw n) unkeyed _
            rw [same, PMF.bind_const]
          have current : alternative.bind (freeKeyedComponent (freeLaw n) (prescribed n)
              (keyedLaw n) (N.agentAt site)) = (targetSequence n).strategy who site.1 := by
            rw [constant, played]
            exact ((N.agentBehavior_at N.playedInformation fallback _ (N.agentAt site)).trans
              (constant _)).symm
          rw [current, localGain_self]⟩)

include bounded in
open Classical in
/-- **Local comparisons with free agents.** As
`GameTheory.Protocol.InformationModel.keyedLocalComparisons`, required at the
sites of agents that are not free. -/
theorem freeKeyedLocalComparisons [Finite Opt] {E : ExecutionProtocol Player}
    {M : InformationModel E} (sourceObserve : E.History → Outcome) (sourceFuel : Nat)
    (sourceSequence : ℕ → M.BehavioralAssessment)
    (freeLaw : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      N.Choice agent.1 agent.2.1 → PMF (N.Choice agent.1 agent.2.1))
    (prescribed : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (compared : ∀ who (site : N.InformationSite who), N.Choice who site.1 → Prop)
    (failed : N.InformationAgent N.playedInformation → Set T.History) (excluded : Player → ℝ)
    (pays : ∀ agent, ∀ history ∈ failed agent, utility (observe history) agent.1 =
      excluded agent.1)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (ranking : ∀ (weights : ℕ → ∀ p, PMF (FreeKeyedPart free keyed key Opt p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (freeKeyedPool free keyed key agent)).bind
          (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → N.InformationAgent N.playedInformation → ℝ)
        (score : ℕ → Key → Opt → ℝ) (error drift slack : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧
        Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧ (∀ n, 0 ≤ slack n) ∧
        ∀ n who (site : N.InformationSite who) (choice : N.Choice who site.1),
          ¬ free (N.agentAt site) → compared who site choice →
          ((excluded who ≤ continuation n (N.agentAt site) + error n ∧
              continuation n (N.agentAt site) - excluded who ≤ bound) ∨
            failed (N.agentAt site) = ∅) ∧
          |localSuccessValue fuel observe utility (targetSequence n) site (failed (N.agentAt site))
              (PMF.pure choice) -
            (1 - localFailure fuel (targetSequence n) site
              (failed (N.agentAt site)) (PMF.pure choice)) *
              continuation n (N.agentAt site)| ≤ error n ∧
          (ownedKeyed free keyed (N.agentAt site) →
            (∀ option, |localSuccessValue fuel observe utility (targetSequence n) site
                (failed (N.agentAt site)) (keyedLaw n (N.agentAt site) option) -
              (1 - localFailure fuel (targetSequence n) site (failed (N.agentAt site))
                (keyedLaw n (N.agentAt site) option)) * continuation n (N.agentAt site)| ≤
              error n) ∧
            (∀ option, |localFailure fuel (targetSequence n) site (failed (N.agentAt site))
                (keyedLaw n (N.agentAt site) option) -
              (1 - score n (key (N.agentAt site)) option)| ≤ drift n) ∧
            ((∃ option, |localFailure fuel (targetSequence n) site (failed (N.agentAt site))
                (PMF.pure choice) - (1 - score n (key (N.agentAt site)) option)| ≤ drift n) ∨
              localFailure fuel (targetSequence n) site
                (failed (N.agentAt site)) (PMF.pure choice) = 1)) ∧
          (¬ ownedKeyed free keyed (N.agentAt site) →
            |localSuccessValue fuel observe utility (targetSequence n) site
              (failed (N.agentAt site))
                (prescribed n (N.agentAt site)) -
              (1 - localFailure fuel (targetSequence n) site (failed (N.agentAt site))
                (prescribed n (N.agentAt site))) * continuation n (N.agentAt site)| ≤ error n ∧
            (localFailure fuel (targetSequence n) site (failed (N.agentAt site))
                (prescribed n (N.agentAt site)) ≤
              localFailure fuel (targetSequence n) site
                (failed (N.agentAt site)) (PMF.pure choice) + slack n ∨
              localFailure fuel (targetSequence n) site
                (failed (N.agentAt site)) (PMF.pure choice) = 1)))
    (otherComparisons : ∀ (weights : ℕ → ∀ p, PMF (FreeKeyedPart free keyed key Opt p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (freeKeyedPool free keyed key agent)).bind
          (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (FreeKeyedPart free keyed key Opt p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => freeKeyedPool free keyed key agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (freeKeyedPool free keyed key agent)).bind
                  (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ otherError : ℕ → ℝ, Tendsto otherError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who), N.agentAt site ∉ Finset.univ.filter free →
          ∀ choice : N.Choice who site.1, ¬ compared who site choice →
          let gain := fun law : PMF (N.Choice who site.1) =>
            let comparison := N.assessmentComparisonWith (N.truncatedRunner
                fuel) observe (targetSequence n)
              who (site, ((targetSequence n).strategy who).withLaw site.1 law)
            expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who)
          gain (PMF.pure choice) ≤ otherError n ∨
            (∃ alternative : PMF (FreeKeyedPart free keyed key Opt
                (freeKeyedPool free keyed key (N.agentAt site))),
              gain (PMF.pure choice) ≤
                gain (alternative.bind (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n)
                  (N.agentAt site))) + otherError n) ∨
            ∃ mixture : PMF (M.AssessmentDeviation who),
              gain (PMF.pure choice) ≤
                expect mixture (fun deviation =>
                  let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                      sourceFuel) sourceObserve
                    (sourceSequence n) who deviation
                  expect sourceComparison.alternative (utility · who) -
                    expect sourceComparison.prescribed (utility · who)) + otherError n) :
    ∀ (weights : ℕ → ∀ p, PMF (FreeKeyedPart free keyed key Opt p))
      (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (freeKeyedPool free keyed key agent)).bind
          (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (FreeKeyedPart free keyed key Opt p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => freeKeyedPool free keyed key agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (freeKeyedPool free keyed key agent)).bind
                  (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ comparisonError : ℕ → ℝ, Tendsto comparisonError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who), N.agentAt site ∉ Finset.univ.filter free →
          ∀ choice : N.Choice who site.1,
          let gain := fun law : PMF (N.Choice who site.1) =>
            let comparison := N.assessmentComparisonWith (N.truncatedRunner
                fuel) observe (targetSequence n)
              who (site, ((targetSequence n).strategy who).withLaw site.1 law)
            expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who)
          gain (PMF.pure choice) ≤ comparisonError n ∨
            (∃ alternative : PMF (FreeKeyedPart free keyed key Opt
                (freeKeyedPool free keyed key (N.agentAt site))),
              gain (PMF.pure choice) ≤
                gain (alternative.bind (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n)
                  (N.agentAt site))) + comparisonError n) ∨
            ∃ mixture : PMF (M.AssessmentDeviation who),
              gain (PMF.pure choice) ≤
                expect mixture (fun deviation =>
                  let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                      sourceFuel) sourceObserve
                    (sourceSequence n) who deviation
                  expect sourceComparison.alternative (utility · who) -
                    expect sourceComparison.prescribed (utility · who)) + comparisonError n :=
  localComparisons_of_success sourceObserve sourceFuel sourceSequence fuel bounded targetRecall
    observe utility fallback (freeKeyedPool free keyed key)
    (fun n => freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n))
    (Finset.univ.filter free) compared failed excluded pays bound bound_nonneg
    (fun weights targetSequence played mixed bayes => by
      let := Fintype.ofFinite Opt
      obtain ⟨continuation, score, error, drift, slack, errorVanishes, driftVanishes,
        slackVanishes, drift_nonneg, slack_nonneg, facts⟩ :=
        ranking weights targetSequence played mixed bayes
      refine ⟨continuation, fun n => freeKeyedBest free keyed key Opt
          (fun k => scoreArgmax (score n k)), error,
        fun n => 2 * drift n + slack n, errorVanishes,
        by simpa using (driftVanishes.const_mul 2).add slackVanishes,
        fun n => by linarith [drift_nonneg n, slack_nonneg n],
        fun n who site choice notFree marked => ?_⟩
      have isNotFree : ¬ free (N.agentAt site) := fun isFree =>
        notFree (Finset.mem_filter.mpr ⟨Finset.mem_univ _, isFree⟩)
      obtain ⟨lowGap, choiceNear, keyedFacts, unkeyedFacts⟩ :=
        facts n who site choice isNotFree marked
      refine ⟨lowGap, choiceNear, ?_⟩
      have best := freeKeyedComponent_at_not_free (freeLaw n) (prescribed n) (keyedLaw n)
        (freeKeyedBest free keyed key Opt (fun k => scoreArgmax (score n k))) isNotFree
      rw [show freeKeyedBest free keyed key Opt (fun k => scoreArgmax (score n k))
          (.inr (keyedPool (ownedKeyed free keyed) key (N.agentAt site))) =
        keyedBest (fun k => scoreArgmax (score n k))
          (keyedPool (ownedKeyed free keyed) key (N.agentAt site)) from rfl] at best
      change |localSuccessValue fuel observe utility (targetSequence n) site
          (failed (N.agentAt site)) (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n)
            (N.agentAt site) (freeKeyedBest free keyed key Opt
              (fun k => scoreArgmax (score n k)) (freeKeyedPool free keyed key
                (N.agentAt site)))) - _| ≤ _ ∧
        localFailure fuel (targetSequence n) site (failed (N.agentAt site))
          (freeKeyedComponent (freeLaw n) (prescribed n) (keyedLaw n) (N.agentAt site)
            (freeKeyedBest free keyed key Opt (fun k => scoreArgmax (score n k))
              (freeKeyedPool free keyed key (N.agentAt site)))) ≤ _
      rw [best]
      by_cases isKeyed : ownedKeyed free keyed (N.agentAt site)
      · obtain ⟨near, common, choiceRanked⟩ := keyedFacts isKeyed
        rw [keyedComponent_best_of_keyed (key := key) (prescribed n) (keyedLaw n)
          (fun k => scoreArgmax (score n k)) isKeyed]
        refine ⟨near _, ?_⟩
        rcases choiceRanked with ⟨option, choiceCommon⟩ | sure
        · have ranked := localFailure_scoreArgmax_le fuel (targetSequence n) site
            (failed (N.agentAt site)) (score n (key (N.agentAt site))) (drift n)
            (keyedLaw n (N.agentAt site)) common (PMF.pure choice) option choiceCommon
          linarith [slack_nonneg n]
        · have := localFailure_le_of_sure_failure fuel (targetSequence n) site
            (failed (N.agentAt site))
            (keyedLaw n (N.agentAt site) (scoreArgmax (score n (key (N.agentAt site)))))
            (PMF.pure choice) sure
          linarith [slack_nonneg n, drift_nonneg n]
      · obtain ⟨near, ranked⟩ := unkeyedFacts isKeyed
        rw [keyedComponent_of_not_keyed (key := key) (prescribed n) (keyedLaw n) isKeyed]
        refine ⟨near, ?_⟩
        rcases ranked with ranked | sure
        · linarith [drift_nonneg n]
        · have := localFailure_le_of_sure_failure fuel (targetSequence n) site
            (failed (N.agentAt site)) (prescribed n (N.agentAt site)) (PMF.pure choice) sure
          linarith [slack_nonneg n, drift_nonneg n])
    otherComparisons

end Certificate

end GameTheory.Protocol.InformationModel
