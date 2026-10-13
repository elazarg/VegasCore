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

end GameTheory.Protocol.InformationModel
