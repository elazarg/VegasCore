/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import GameTheoryExtensions.Analysis.Protocol.SuccessRanking

/-! # Pools keyed by what a move may depend on

Some agents are keyed: they choose among finitely many options, and the
choice may depend on a key of the agent only, so that a move reveals nothing
the key does not. Keyed agents with a common key share one pool whose parts
are the options; every other agent sits in a single pool with one part
(`GameTheory.Protocol.InformationModel.keyedPool`,
`GameTheory.Protocol.InformationModel.KeyedPart`). A keyed agent's component
of an option is its keyed law of that option, and every other agent's single
component is its prescribed law
(`GameTheory.Protocol.InformationModel.keyedComponent`).

Given a score of each option at each key, the best part of a keyed pool is an
option of greatest score at the pool's key
(`GameTheory.Math.Probability.scoreArgmax`,
`GameTheory.Protocol.InformationModel.keyedBest`). If at every keyed site the
keyed laws fail with probability within a drift of one minus their scores at
the site's key, the best option fails least at every member up to twice the
drift. With the value of every keyed site one-dimensional in its success
probability, this gives the member-rationality obligation of a pooled limit
certificate (`GameTheory.Protocol.InformationModel.keyedMemberRational`); the
unkeyed pool has one part, so its members are rational outright. Marking
single choices to compare with the best part gives the local-comparison
obligation (`GameTheory.Protocol.InformationModel.keyedLocalComparisons`): a
marked choice at a keyed site realizes some option, and one at an unkeyed site
fails at least as often as the prescribed law up to a vanishing slack.
-/

noncomputable section

namespace GameTheory.Math.Probability

/-- An option of greatest score, chosen by a fixed rule from the score. -/
def scoreArgmax {Option : Type*} [Fintype Option] [Nonempty Option] (score : Option → ℝ) :
    Option :=
  (Finset.univ.exists_max_image score Finset.univ_nonempty).choose

theorem le_scoreArgmax {Option : Type*} [Fintype Option] [Nonempty Option]
    (score : Option → ℝ) (option : Option) : score option ≤ score (scoreArgmax score) :=
  (Finset.univ.exists_max_image score Finset.univ_nonempty).choose_spec.2 option
    (Finset.mem_univ option)

end GameTheory.Math.Probability

namespace GameTheory.Protocol.InformationModel

open ExecutionProtocol Math.Probability Filter

variable {Player : Type} {T : ExecutionProtocol Player} {N : InformationModel T}
  [Fintype T.History] [∀ who, DecidableEq (N.InfoState who)]

section Structure

variable {Key : Type*} (keyed : N.InformationAgent N.playedInformation → Prop)
  (key : N.InformationAgent N.playedInformation → Key) (Opt : Type)

/-- The keyed pools: one per key of a keyed agent, and `none` for every other
agent. -/
abbrev KeyedPool := Option (Set.range fun agent : {agent // keyed agent} => key agent.1)

open Classical in
/-- The pool of an agent: its key if it is keyed, `none` otherwise. -/
def keyedPool (agent : N.InformationAgent N.playedInformation) : KeyedPool keyed key :=
  if isKeyed : keyed agent then some ⟨key agent, ⟨agent, isKeyed⟩, rfl⟩ else none

/-- The parts of a keyed pool are the options; the other pool has one part. -/
def KeyedPart : KeyedPool keyed key → Type
  | none => Unit
  | some _ => Opt

instance [Finite Opt] (p : KeyedPool keyed key) : Finite (KeyedPart keyed key Opt p) := by
  cases p <;> unfold KeyedPart <;> infer_instance

instance [Nonempty Opt] (p : KeyedPool keyed key) : Nonempty (KeyedPart keyed key Opt p) := by
  cases p <;> unfold KeyedPart <;> infer_instance

variable {keyed key Opt}

/-- A component at a pool: the prescribed law in the unkeyed pool, the keyed
law of the option in a keyed pool. -/
def keyedComponentAt
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (agent : N.InformationAgent N.playedInformation) :
    (p : KeyedPool keyed key) → KeyedPart keyed key Opt p → PMF (N.Choice agent.1 agent.2.1)
  | none, _ => prescribed agent
  | some _, option => keyedLaw agent option

/-- **The keyed components.** A keyed agent's component of an option is its
keyed law of the option; every other agent's single component is its
prescribed law. -/
def keyedComponent
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (agent : N.InformationAgent N.playedInformation) :
    KeyedPart keyed key Opt (keyedPool keyed key agent) → PMF (N.Choice agent.1 agent.2.1) :=
  keyedComponentAt prescribed keyedLaw agent (keyedPool keyed key agent)

/-- The best part of each pool: the best option of a keyed pool's key. -/
def keyedBest (bestOf : Key → Opt) : (p : KeyedPool keyed key) → KeyedPart keyed key Opt p
  | none => ()
  | some k => bestOf k.1

theorem keyedPool_of_keyed {agent : N.InformationAgent N.playedInformation}
    (isKeyed : keyed agent) :
    keyedPool keyed key agent = some ⟨key agent, ⟨agent, isKeyed⟩, rfl⟩ := by
  classical
  unfold keyedPool
  simp only [isKeyed, ↓reduceDIte]

theorem keyedPool_of_not_keyed {agent : N.InformationAgent N.playedInformation}
    (unkeyed : ¬ keyed agent) : keyedPool keyed key agent = none := by
  classical
  unfold keyedPool
  simp only [unkeyed, ↓reduceDIte]

theorem isSome_keyedPool_iff (agent : N.InformationAgent N.playedInformation) :
    (keyedPool keyed key agent).isSome ↔ keyed agent := by
  by_cases isKeyed : keyed agent
  · simp [keyedPool_of_keyed isKeyed, isKeyed]
  · simp [keyedPool_of_not_keyed isKeyed, isKeyed]

/-- Every component of a keyed agent is its keyed law of some option. -/
theorem keyedComponent_of_keyed
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    {agent : N.InformationAgent N.playedInformation} (isKeyed : keyed agent) :
    ∀ part, ∃ option, keyedComponent (keyed := keyed) (key := key) prescribed keyedLaw agent part =
      keyedLaw agent option := by
  unfold keyedComponent
  rw [keyedPool_of_keyed isKeyed]
  exact fun option => ⟨option, rfl⟩

/-- The component of the best part of a keyed agent is its keyed law of the
best option of its key. -/
theorem keyedComponent_best_of_keyed
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1)) (bestOf : Key → Opt)
    {agent : N.InformationAgent N.playedInformation} (isKeyed : keyed agent) :
    keyedComponent prescribed keyedLaw agent (keyedBest bestOf (keyedPool keyed key agent)) =
      keyedLaw agent (bestOf (key agent)) := by
  change (fun p => keyedComponentAt prescribed keyedLaw agent p (keyedBest bestOf p))
    (keyedPool keyed key agent) = _
  rw [keyedPool_of_keyed isKeyed]
  rfl

/-- Every component of an unkeyed agent is its prescribed law. -/
theorem keyedComponent_of_not_keyed
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    {agent : N.InformationAgent N.playedInformation} (unkeyed : ¬ keyed agent) :
    ∀ part, keyedComponent (keyed := keyed) (key := key) prescribed keyedLaw agent part =
      prescribed agent := by
  unfold keyedComponent
  rw [keyedPool_of_not_keyed unkeyed]
  exact fun _ => rfl

/-- A mixture of an unkeyed agent's components is its prescribed law. -/
theorem bind_keyedComponent_of_not_keyed
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    {agent : N.InformationAgent N.playedInformation} (unkeyed : ¬ keyed agent)
    (weights : PMF (KeyedPart keyed key Opt (keyedPool keyed key agent))) :
    weights.bind (keyedComponent prescribed keyedLaw agent) = prescribed agent := by
  have constant : keyedComponent (keyed := keyed) (key := key) prescribed keyedLaw agent =
      fun _ => prescribed agent :=
    funext (keyedComponent_of_not_keyed prescribed keyedLaw unkeyed)
  rw [constant, PMF.bind_const]

/-- Fully supported prescribed and keyed laws make every keyed component
fully supported. -/
theorem keyedComponent_fullSupport
    (prescribed : ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (prescribedFull : ∀ agent, FullSupport (prescribed agent))
    (keyedFull : ∀ agent option, FullSupport (keyedLaw agent option))
    (agent : N.InformationAgent N.playedInformation) :
    ∀ part, FullSupport (keyedComponent (keyed := keyed) (key := key) prescribed keyedLaw agent
      part) := by
  unfold keyedComponent
  cases keyedPool keyed key agent with
  | none => exact fun _ => prescribedFull agent
  | some _ => exact fun option => keyedFull agent option

end Structure

section Obligations

variable [Fintype Player] [DecidableEq Player] {Outcome : Type*} {Key : Type*}
  (fuel : Nat) (bounded : T.BoundedHorizon fuel) (targetRecall : N.DecisionRecall)
  (observe : T.History → Outcome) (utility : Outcome → Player → ℝ)
  (fallback : ∀ who, N.Policy who)
  (keyed : N.InformationAgent N.playedInformation → Prop)
  (key : N.InformationAgent N.playedInformation → Key) {Opt : Type} [Nonempty Opt]

omit [Fintype T.History] in
/-- At a keyed site whose options fail with probability within `drift` of one
minus their scores, the option of greatest score fails least up to twice the
drift. -/
theorem localFailure_scoreArgmax_le [Fintype Opt] {who : Player}
    (assessment : N.BehavioralAssessment)
    (site : N.InformationSite who) (failed : Set T.History) (score : Opt → ℝ) (drift : ℝ)
    (law : Opt → PMF (N.Choice who site.1))
    (near : ∀ option, |localFailure fuel assessment site failed (law option) -
      (1 - score option)| ≤ drift) (other : PMF (N.Choice who site.1)) (option : Opt)
    (otherNear : |localFailure fuel assessment site failed other - (1 - score option)| ≤ drift) :
    localFailure fuel assessment site failed (law (scoreArgmax score)) ≤
      localFailure fuel assessment site failed other + 2 * drift := by
  have best := (abs_le.mp (near (scoreArgmax score))).2
  have low := (abs_le.mp otherNear).1
  linarith [le_scoreArgmax score option]

include bounded in
open Classical in
/-- **Member rationality for keyed pools.** Suppose that, for every weights
family the pooled completion may choose, at every keyed decision site: failure
pays the player a fixed payoff at most the site's continuation value up to
`error n`, with gap at most `bound`; the successful part of each option's keyed
law is its success probability times that continuation value up to `error n`;
and each option's keyed law fails, at the site level, with probability within
`drift n` of one minus the option's score at the site's key. If `error` and
`drift` vanish, the member-rationality obligation of a pooled limit
certificate holds for the keyed pools, with the keyed components. -/
theorem keyedMemberRational [Finite Opt]
    (prescribed : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (failed : Player → Set T.History) (excluded : Player → ℝ)
    (pays : ∀ who, ∀ history ∈ failed who, utility (observe history) who = excluded who)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (oneDimensional : ∀ (weights : ℕ → ∀ p, PMF (KeyedPart keyed key Opt p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (keyedPool keyed key agent)).bind
          (keyedComponent (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → N.InformationAgent N.playedInformation → ℝ)
        (score : ℕ → Key → Opt → ℝ) (error drift : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧
        ∀ n (agent : N.InformationAgent N.playedInformation), keyed agent →
          ∀ decision : N.IsDecisionInfo agent.1 agent.2.1,
          excluded agent.1 ≤ continuation n agent + error n ∧
          continuation n agent - excluded agent.1 ≤ bound ∧
          (∀ option, |localSuccessValue fuel observe utility (targetSequence n)
              (who := agent.1) ⟨agent.2.1, decision⟩ (failed agent.1) (keyedLaw n agent option) -
            (1 - localFailure fuel (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent.1) (keyedLaw n agent option)) * continuation n agent| ≤ error n) ∧
          ∀ option, |localFailure fuel (targetSequence n) (who := agent.1) ⟨agent.2.1, decision⟩
              (failed agent.1) (keyedLaw n agent option) - (1 - score n (key agent) option)| ≤
            drift n) :
    ∀ (weights : ℕ → ∀ p, PMF (KeyedPart keyed key Opt p))
      (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (keyedPool keyed key agent)).bind
          (keyedComponent (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (KeyedPart keyed key Opt p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => keyedPool keyed key agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (keyedPool keyed key agent)).bind
                  (keyedComponent (prescribed n) (keyedLaw n) agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ memberError : ℕ → ℝ, Tendsto memberError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who)
          (alternative : PMF (KeyedPart keyed key Opt (keyedPool keyed key (N.agentAt site)))),
          let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
            observe (targetSequence n) who
            (site, ((targetSequence n).strategy who).withLaw site.1
              (alternative.bind (keyedComponent (prescribed n) (keyedLaw n) (N.agentAt site))))
          expect comparison.alternative (utility · who) -
            expect comparison.prescribed (utility · who) ≤ memberError n :=
  memberRational_of_success fuel bounded targetRecall observe utility fallback
    (keyedPool keyed key) (fun n => keyedComponent (prescribed n) (keyedLaw n))
    {p | p.isSome} failed excluded pays bound bound_nonneg
    (fun weights targetSequence played mixed bayes => by
      let := Fintype.ofFinite Opt
      obtain ⟨continuation, score, error, drift, errorVanishes, driftVanishes, drift_nonneg,
        facts⟩ := oneDimensional weights targetSequence played mixed bayes
      refine ⟨continuation, fun n => keyedBest fun k => scoreArgmax (score n k), error,
        fun n => 2 * drift n, errorVanishes, by simpa using driftVanishes.const_mul 2,
        fun n => by linarith [drift_nonneg n], fun n agent inDelivery decision => ?_⟩
      have isKeyed : keyed agent := (isSome_keyedPool_iff agent).mp inDelivery
      obtain ⟨excluded_le, gap_le, near, common⟩ := facts n agent isKeyed decision
      have best := keyedComponent_best_of_keyed (key := key) (prescribed n) (keyedLaw n)
        (fun k => scoreArgmax (score n k)) isKeyed
      refine ⟨excluded_le, gap_le, fun part => ?_, fun part => ?_⟩
      · obtain ⟨option, equal⟩ :=
          keyedComponent_of_keyed (key := key) (prescribed n) (keyedLaw n) isKeyed part
        rw [equal]
        exact near option
      · obtain ⟨option, equal⟩ :=
          keyedComponent_of_keyed (key := key) (prescribed n) (keyedLaw n) isKeyed part
        rw [equal, best]
        exact localFailure_scoreArgmax_le fuel (targetSequence n) (who := agent.1)
          ⟨agent.2.1, decision⟩ (failed agent.1) (score n (key agent)) (drift n)
          (keyedLaw n agent) common (keyedLaw n agent option) option (common option))
    (fun weights targetSequence played _ _ _ => ⟨fun _ => 0, tendsto_const_nhds,
      fun n who site outside alternative => by
        have unkeyed : ¬ keyed (N.agentAt site) := fun isKeyed =>
          outside ((isSome_keyedPool_iff _).mpr isKeyed)
        have current : alternative.bind (keyedComponent (prescribed n) (keyedLaw n)
            (N.agentAt site)) = (targetSequence n).strategy who site.1 := by
          rw [bind_keyedComponent_of_not_keyed _ _ unkeyed, played]
          exact ((N.agentBehavior_at N.playedInformation fallback _ (N.agentAt site)).trans
            (bind_keyedComponent_of_not_keyed _ _ unkeyed _)).symm
        change localGain fuel observe utility (targetSequence n) site _ ≤ 0
        rw [current, localGain_self]⟩)

include bounded in
open Classical in
/-- **Local comparisons for keyed pools.** Mark, at each site, the single
choices to compare with the best part of the site's pool. Suppose that, for
every weights family the pooled completion may choose, at every marked choice
of a compared site: failure pays the player a fixed payoff at most the site's
continuation value up to `error n`, with gap at most `bound`; the successful
part of the choice is its success probability times that continuation value
up to `error n`; at a keyed site, the same holds for every option's keyed law,
each option's keyed law fails, at the site level, with probability within
`drift n` of one minus the option's score at the site's key, and so does the
choice for some option, unless the choice fails surely; at an unkeyed site,
the same holds for the prescribed law, which fails at most as often as the
choice up to `slack n`, unless the choice fails surely. A surely failing
choice, such as a packet the contract cannot accept spending the one packet of
an event, or any choice of an owner whose event is doomed, ranks last
(`GameTheory.Protocol.InformationModel.localFailure_le_of_sure_failure`). If `error`,
`drift` and `slack` vanish and the unmarked choices meet the comparisons on
their own, the local-comparison obligation of a pooled limit certificate holds
for the keyed pools, with the keyed components. -/
theorem keyedLocalComparisons [Finite Opt] {E : ExecutionProtocol Player}
    {M : InformationModel E} (sourceObserve : E.History → Outcome) (sourceFuel : Nat)
    (sourceSequence : ℕ → M.BehavioralAssessment)
    (prescribed : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      PMF (N.Choice agent.1 agent.2.1))
    (keyedLaw : ℕ → ∀ agent : N.InformationAgent N.playedInformation,
      Opt → PMF (N.Choice agent.1 agent.2.1))
    (free : Finset (N.InformationAgent N.playedInformation))
    (compared : ∀ who (site : N.InformationSite who), N.Choice who site.1 → Prop)
    (failed : Player → Set T.History) (excluded : Player → ℝ)
    (pays : ∀ who, ∀ history ∈ failed who, utility (observe history) who = excluded who)
    (bound : ℝ) (bound_nonneg : 0 ≤ bound)
    (ranking : ∀ (weights : ℕ → ∀ p, PMF (KeyedPart keyed key Opt p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (keyedPool keyed key agent)).bind
          (keyedComponent (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      ∃ (continuation : ℕ → N.InformationAgent N.playedInformation → ℝ)
        (score : ℕ → Key → Opt → ℝ) (error drift slack : ℕ → ℝ),
        Tendsto error atTop (nhds 0) ∧ Tendsto drift atTop (nhds 0) ∧
        Tendsto slack atTop (nhds 0) ∧ (∀ n, 0 ≤ drift n) ∧ (∀ n, 0 ≤ slack n) ∧
        ∀ n who (site : N.InformationSite who) (choice : N.Choice who site.1),
          N.agentAt site ∉ free → compared who site choice →
          excluded who ≤ continuation n (N.agentAt site) + error n ∧
          continuation n (N.agentAt site) - excluded who ≤ bound ∧
          |localSuccessValue fuel observe utility (targetSequence n) site (failed who)
              (PMF.pure choice) -
            (1 - localFailure fuel (targetSequence n) site (failed who) (PMF.pure choice)) *
              continuation n (N.agentAt site)| ≤ error n ∧
          (keyed (N.agentAt site) →
            (∀ option, |localSuccessValue fuel observe utility (targetSequence n) site
                (failed who) (keyedLaw n (N.agentAt site) option) -
              (1 - localFailure fuel (targetSequence n) site (failed who)
                (keyedLaw n (N.agentAt site) option)) * continuation n (N.agentAt site)| ≤
              error n) ∧
            (∀ option, |localFailure fuel (targetSequence n) site (failed who)
                (keyedLaw n (N.agentAt site) option) -
              (1 - score n (key (N.agentAt site)) option)| ≤ drift n) ∧
            ((∃ option, |localFailure fuel (targetSequence n) site (failed who)
                (PMF.pure choice) - (1 - score n (key (N.agentAt site)) option)| ≤ drift n) ∨
              localFailure fuel (targetSequence n) site (failed who) (PMF.pure choice) = 1)) ∧
          (¬ keyed (N.agentAt site) →
            |localSuccessValue fuel observe utility (targetSequence n) site (failed who)
                (prescribed n (N.agentAt site)) -
              (1 - localFailure fuel (targetSequence n) site (failed who)
                (prescribed n (N.agentAt site))) * continuation n (N.agentAt site)| ≤ error n ∧
            (localFailure fuel (targetSequence n) site (failed who)
                (prescribed n (N.agentAt site)) ≤
              localFailure fuel (targetSequence n) site (failed who) (PMF.pure choice) + slack n ∨
              localFailure fuel (targetSequence n) site (failed who) (PMF.pure choice) = 1)))
    (otherComparisons : ∀ (weights : ℕ → ∀ p, PMF (KeyedPart keyed key Opt p))
        (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (keyedPool keyed key agent)).bind
          (keyedComponent (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (KeyedPart keyed key Opt p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => keyedPool keyed key agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (keyedPool keyed key agent)).bind
                  (keyedComponent (prescribed n) (keyedLaw n) agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ otherError : ℕ → ℝ, Tendsto otherError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who), N.agentAt site ∉ free →
          ∀ choice : N.Choice who site.1, ¬ compared who site choice →
          let gain := fun law : PMF (N.Choice who site.1) =>
            let comparison := N.assessmentComparisonWith (N.truncatedRunner
                fuel) observe (targetSequence n)
              who (site, ((targetSequence n).strategy who).withLaw site.1 law)
            expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who)
          gain (PMF.pure choice) ≤ otherError n ∨
            (∃ alternative : PMF (KeyedPart keyed key Opt (keyedPool keyed key (N.agentAt site))),
              gain (PMF.pure choice) ≤
                gain (alternative.bind (keyedComponent (prescribed n) (keyedLaw n)
                  (N.agentAt site))) + otherError n) ∨
            ∃ mixture : PMF (M.AssessmentDeviation who),
              gain (PMF.pure choice) ≤
                expect mixture (fun deviation =>
                  let sourceComparison := M.assessmentComparisonWith (M.truncatedRunner
                      sourceFuel) sourceObserve
                    (sourceSequence n) who deviation
                  expect sourceComparison.alternative (utility · who) -
                    expect sourceComparison.prescribed (utility · who)) + otherError n) :
    ∀ (weights : ℕ → ∀ p, PMF (KeyedPart keyed key Opt p))
      (targetSequence : ℕ → N.BehavioralAssessment),
      (∀ n, (targetSequence n).strategy = N.agentBehavior N.playedInformation fallback
        fun agent => (weights n (keyedPool keyed key agent)).bind
          (keyedComponent (prescribed n) (keyedLaw n) agent)) →
      (∀ n, (targetSequence n).IsFullyMixed) →
      (∀ n, BehavioralAssessment.IsBayesConsistent N (targetSequence n)
        targetRecall.decisionInformationAntichain) →
      (∀ n (alternative : ∀ p, PMF (KeyedPart keyed key Opt p)) p,
        ∑ agent ∈ Finset.univ.filter (fun agent => keyedPool keyed key agent = p),
          (if decision : N.IsDecisionInfo agent.1 agent.2.1 then
            let comparison := N.assessmentComparisonWith (N.truncatedRunner fuel)
              observe (targetSequence n) agent.1
              (⟨agent.2.1, decision⟩, ((targetSequence n).strategy agent.1).withLaw agent.2.1
                ((alternative (keyedPool keyed key agent)).bind
                  (keyedComponent (prescribed n) (keyedLaw n) agent)))
            expect comparison.alternative (utility · agent.1) -
              expect comparison.prescribed (utility · agent.1)
          else 0) ≤ 0) →
      ∃ comparisonError : ℕ → ℝ, Tendsto comparisonError atTop (nhds 0) ∧
        ∀ n who (site : N.InformationSite who), N.agentAt site ∉ free →
          ∀ choice : N.Choice who site.1,
          let gain := fun law : PMF (N.Choice who site.1) =>
            let comparison := N.assessmentComparisonWith (N.truncatedRunner
                fuel) observe (targetSequence n)
              who (site, ((targetSequence n).strategy who).withLaw site.1 law)
            expect comparison.alternative (utility · who) -
              expect comparison.prescribed (utility · who)
          gain (PMF.pure choice) ≤ comparisonError n ∨
            (∃ alternative : PMF (KeyedPart keyed key Opt (keyedPool keyed key (N.agentAt site))),
              gain (PMF.pure choice) ≤
                gain (alternative.bind (keyedComponent (prescribed n) (keyedLaw n)
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
    observe utility fallback (keyedPool keyed key)
    (fun n => keyedComponent (prescribed n) (keyedLaw n)) free compared failed excluded pays
    bound bound_nonneg
    (fun weights targetSequence played mixed bayes => by
      let := Fintype.ofFinite Opt
      obtain ⟨continuation, score, error, drift, slack, errorVanishes, driftVanishes,
        slackVanishes, drift_nonneg, slack_nonneg, facts⟩ :=
        ranking weights targetSequence played mixed bayes
      refine ⟨continuation, fun n => keyedBest fun k => scoreArgmax (score n k), error,
        fun n => 2 * drift n + slack n, errorVanishes,
        by simpa using (driftVanishes.const_mul 2).add slackVanishes,
        fun n => by linarith [drift_nonneg n, slack_nonneg n],
        fun n who site choice notFree marked => ?_⟩
      obtain ⟨excluded_le, gap_le, choiceNear, keyedFacts, unkeyedFacts⟩ :=
        facts n who site choice notFree marked
      refine ⟨excluded_le, gap_le, choiceNear, ?_⟩
      by_cases isKeyed : keyed (N.agentAt site)
      · obtain ⟨near, common, choiceRanked⟩ := keyedFacts isKeyed
        rw [keyedComponent_best_of_keyed (key := key) (prescribed n) (keyedLaw n)
          (fun k => scoreArgmax (score n k)) isKeyed]
        refine ⟨near _, ?_⟩
        rcases choiceRanked with ⟨option, choiceCommon⟩ | sure
        · have ranked := localFailure_scoreArgmax_le fuel (targetSequence n) site (failed who)
            (score n (key (N.agentAt site))) (drift n) (keyedLaw n (N.agentAt site)) common
            (PMF.pure choice) option choiceCommon
          linarith [slack_nonneg n]
        · have := localFailure_le_of_sure_failure fuel (targetSequence n) site (failed who)
            (keyedLaw n (N.agentAt site) (scoreArgmax (score n (key (N.agentAt site)))))
            (PMF.pure choice) sure
          linarith [slack_nonneg n, drift_nonneg n]
      · obtain ⟨near, ranked⟩ := unkeyedFacts isKeyed
        rw [keyedComponent_of_not_keyed (key := key) (prescribed n) (keyedLaw n) isKeyed]
        refine ⟨near, ?_⟩
        rcases ranked with ranked | sure
        · linarith [drift_nonneg n]
        · have := localFailure_le_of_sure_failure fuel (targetSequence n) site (failed who)
            (prescribed n (N.agentAt site)) (PMF.pure choice) sure
          linarith [slack_nonneg n, drift_nonneg n])
    otherComparisons

end Obligations

end GameTheory.Protocol.InformationModel
