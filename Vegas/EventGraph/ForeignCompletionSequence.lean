/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.EventGraph.StateCongruence

import Vegas.EventGraph.NormalizedPolicy

/-! # Normalized policy stability through semantic foreign completions -/

noncomputable section
namespace Vegas.EventGraph
open GameTheory.Math.Probability
variable {Player : Type} [DecidableEq Player]
  {L : IExpr} [IExpr.ResultTypes L] {graph : Vegas.EventGraph Player L}

/-- A proof-only sequence of supported semantic completions by other owners.
The relation adds no execution state and does not choose an evaluation law. -/
inductive ForeignCompletionSequence (who : Player) : graph.Config → graph.Config → Prop
  | refl (config : graph.Config) : ForeignCompletionSequence who config config
  | snoc {first before : graph.Config}
      (previous : ForeignCompletionSequence who first before)
      (other : graph.EventId) (ready : before.cut.Ready other)
      (owner : Player) (actor : graph.actor? other = some owner) (foreign : owner ≠ who)
      (action : graph.Action other) (value : (graph.outputLayout other).Value)
      (supported : before.complete other ready action value ∈
        (before.step other ready action).support) :
      ForeignCompletionSequence who first (before.complete other ready action value)

omit [DecidableEq Player] in
/-- Semantic pending completions preserve genuine reachability. -/
theorem ForeignCompletionSequence.reachable {who : Player} {first last : graph.Config}
    (sequence : ForeignCompletionSequence who first last) {inputs : graph.Inputs}
    (reachable : first.Reachable inputs) : last.Reachable inputs := by
  induction sequence with
  | refl => exact reachable
  | snoc previous other ready owner actor foreign action value supported ih =>
      exact Config.Reachable.step ih other ready action _ supported

/-- The exact normalized decision law at a retained ready event is unchanged
through every pending foreign completion. This uses the graph's barrier
information discipline rather than assuming the desired kernel equality. -/
theorem ForeignCompletionSequence.normalizePolicy_eq
    {who : Player} {first last : graph.Config}
    (sequence : ForeignCompletionSequence who first last)
    (ordered : graph.BarrierOrdered) (policy : graph.BehavioralPolicy who)
    (event : graph.EventId) (ready : first.cut.Ready event)
    (actor : graph.actor? event = some who) :
    last.cut.Ready event ∧
      graph.normalizePolicy who policy event actor (graph.playerObserve who last) =
        graph.normalizePolicy who policy event actor (graph.playerObserve who first) := by
  induction sequence with
  | refl => exact ⟨ready, rfl⟩
  | snoc previous other otherReady owner otherActor foreign action value supported ih =>
      obtain ⟨retainedReady, same⟩ := ih
      have advanced := ordered.normalizePolicy_complete_foreign policy _ event other
        retainedReady otherReady actor owner otherActor foreign action value
      exact ⟨advanced.1, advanced.2.trans same⟩


omit [DecidableEq Player] in
/-- Equal local evaluator laws replay the selected action and output through
the existing semantic executor. -/
theorem Config.complete_supported_of_eval_eq
    (left right : graph.Config) (event : graph.EventId)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (same : (graph.nodes event).eval? action left.store =
      (graph.nodes event).eval? action right.store)
    (supported : left.complete event leftReady action value ∈
      (left.step event leftReady action).support) :
    right.complete event rightReady action value ∈
      (right.step event rightReady action).support := by
  obtain ⟨law, evaluates⟩ := Option.isSome_iff_exists.mp
    (EventCode.eval?_isSome_of_reads (graph.nodes event) action left.store
      (fun _ member => left.read_available leftReady member))
  have evaluatesRight := same.symm.trans evaluates
  rw [left.step_eq_map_of_eval event leftReady action law evaluates, PMF.support_map] at supported
  obtain ⟨output, member, equal⟩ := supported
  have valueEq : output = value := by
    have out := congrArg (fun config : graph.Config => config.outputs event) equal
    simpa only [Config.complete_output_same, Option.some.injEq] using out
  subst output
  rw [right.step_eq_map_of_eval event rightReady action law evaluatesRight, PMF.support_map]
  exact ⟨value, member, rfl⟩

/-- Independent completions commute in cut, full store, and every owner's
ordered completion recall. -/
theorem semanticKey_complete_comm (config : graph.Config)
    (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right)
    (actorsDiffer : ∀ who, graph.actor? left = some who → graph.actor? right ≠ some who)
    (leftAction : graph.Action left) (rightAction : graph.Action right)
    (leftValue : (graph.outputLayout left).Value)
    (rightValue : (graph.outputLayout right).Value) :
    graph.semanticKey ((config.complete left leftReady leftAction leftValue).complete right
      (rightReady.after_complete leftReady different.symm) rightAction rightValue) =
    graph.semanticKey ((config.complete right rightReady rightAction rightValue).complete left
      (leftReady.after_complete rightReady different) leftAction leftValue) := by
  apply Prod.ext
  · exact config.cut.complete_comm leftReady rightReady different
  · apply Prod.ext
    · exact store_complete_comm leftReady rightReady different leftAction rightAction
        leftValue rightValue
    · simpa only [semanticKey, storeRecall, Config.complete, List.append_assoc,
        List.singleton_append] using
        ownCompletions_complete_comm config actorsDiffer leftAction rightAction

/-- Exchange an actual supported pair of independent graph completions,
retaining the sampled actions and outputs rather than redrawing them. -/
theorem supported_completions_exchange (config : graph.Config)
    (left right : graph.EventId)
    (leftReady : config.cut.Ready left) (rightReady : config.cut.Ready right)
    (different : left ≠ right)
    (actorsDiffer : ∀ who, graph.actor? left = some who → graph.actor? right ≠ some who)
    (leftAction : graph.Action left) (rightAction : graph.Action right)
    (leftValue : (graph.outputLayout left).Value)
    (rightValue : (graph.outputLayout right).Value)
    (leftSupported : config.complete left leftReady leftAction leftValue ∈
      (config.step left leftReady leftAction).support)
    (rightSupported : (config.complete left leftReady leftAction leftValue).complete right
        (rightReady.after_complete leftReady different.symm) rightAction rightValue ∈
      ((config.complete left leftReady leftAction leftValue).step right
        (rightReady.after_complete leftReady different.symm) rightAction).support) :
    config.complete right rightReady rightAction rightValue ∈
        (config.step right rightReady rightAction).support ∧
      (config.complete right rightReady rightAction rightValue).complete left
          (leftReady.after_complete rightReady different) leftAction leftValue ∈
        ((config.complete right rightReady rightAction rightValue).step left
          (leftReady.after_complete rightReady different) leftAction).support ∧
      graph.semanticKey ((config.complete left leftReady leftAction leftValue).complete right
          (rightReady.after_complete leftReady different.symm) rightAction rightValue) =
        graph.semanticKey ((config.complete right rightReady rightAction rightValue).complete left
          (leftReady.after_complete rightReady different) leftAction leftValue) := by
  refine ⟨?_, ?_, semanticKey_complete_comm config left right leftReady rightReady different
    actorsDiffer leftAction rightAction leftValue rightValue⟩
  · exact Config.complete_supported_of_eval_eq _ config right _ rightReady rightAction rightValue
      (eval?_after_complete leftReady rightReady leftAction leftValue rightAction) rightSupported
  · exact Config.complete_supported_of_eval_eq config _ left leftReady _ leftAction leftValue
      (eval?_after_complete rightReady leftReady rightAction rightValue leftAction).symm
      leftSupported

/-- Rebuild a supported semantic completion at an equivalent configuration
without replacing its selected action or its sampled output. -/
theorem Config.complete_supported_of_semanticKey_eq
    (left right : graph.Config) (same : graph.semanticKey left = graph.semanticKey right)
    (event : graph.EventId) (leftReady : left.cut.Ready event)
    (rightReady : right.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value)
    (supported : left.complete event leftReady action value ∈
      (left.step event leftReady action).support) :
    right.complete event rightReady action value ∈
      (right.step event rightReady action).support := by
  apply Config.complete_supported_of_eval_eq left right event leftReady rightReady action value
    _ supported
  rw [semanticKey_store_eq same]

/-- A pending foreign completion trace can be replayed at an equivalent
semantic state while retaining its exact original sampled actions and outputs. -/
theorem ForeignCompletionSequence.congr_start {who : Player} {first last : graph.Config}
    (sequence : graph.ForeignCompletionSequence who first last)
    (otherFirst : graph.Config) (same : graph.semanticKey first = graph.semanticKey otherFirst) :
    ∃ otherLast, graph.ForeignCompletionSequence who otherFirst otherLast ∧
      graph.semanticKey last = graph.semanticKey otherLast := by
  induction sequence generalizing otherFirst with
  | refl => exact ⟨otherFirst, .refl _, same⟩
  | snoc previous other ready owner actor foreign action value supported ih =>
      obtain ⟨otherBefore, rebuilt, beforeSame⟩ := ih otherFirst same
      have otherReady : otherBefore.cut.Ready other := by
        rw [← semanticKey_cut_eq beforeSame]
        exact ready
      have supportedOther := Config.complete_supported_of_semanticKey_eq _ otherBefore
        beforeSame other ready otherReady action value supported
      exact ⟨otherBefore.complete other otherReady action value,
        .snoc rebuilt other otherReady owner actor foreign action value supportedOther,
        semanticKey_complete_congr beforeSame other ready otherReady action value⟩
omit [DecidableEq Player] in
/-- Foreign sampled completions preserve readiness of the retained actor event. -/
theorem ForeignCompletionSequence.ready {who : Player} {first last : graph.Config}
    (sequence : graph.ForeignCompletionSequence who first last)
    (event : graph.EventId) (ready : first.cut.Ready event)
    (actor : graph.actor? event = some who) : last.cut.Ready event := by
  induction sequence with
  | refl => exact ready
  | snoc previous other otherReady owner otherActor foreign action value supported ih =>
      have different : other ≠ event := by
        intro same
        rw [same, actor, Option.some.injEq] at otherActor
        exact foreign otherActor.symm
      exact ih.after_complete otherReady different.symm

/-- Move an actual supported sampled step before the pending foreign trace,
keeping all sampled values, reachability, and each owner's ordered recall. -/
theorem ForeignCompletionSequence.exchange_step {who : Player} {first last : graph.Config}
    (sequence : graph.ForeignCompletionSequence who first last)
    (event : graph.EventId) (ready : first.cut.Ready event)
    (actor : graph.actor? event = some who)
    (action : graph.Action event) (value : (graph.outputLayout event).Value)
    (supported : last.complete event (sequence.ready event ready actor) action value ∈
      (last.step event (sequence.ready event ready actor) action).support) :
    first.complete event ready action value ∈ (first.step event ready action).support ∧
      ∃ rebuilt, graph.ForeignCompletionSequence who
          (first.complete event ready action value) rebuilt ∧
        graph.semanticKey (last.complete event (sequence.ready event ready actor) action value) =
          graph.semanticKey rebuilt := by
  induction sequence with
  | refl => exact ⟨supported, _, .refl _, rfl⟩
  | @snoc before previous other otherReady owner otherActor foreign otherAction otherValue
      otherSupported ih =>
      have retainedReady := previous.ready event ready actor
      have different : other ≠ event := by
        intro same
        rw [same, actor, Option.some.injEq] at otherActor
        exact foreign otherActor.symm
      have actorsDiffer : ∀ player, graph.actor? other = some player →
          graph.actor? event ≠ some player := by
        intro player owned sameActor
        have ownerEq : owner = player := Option.some.inj (otherActor.symm.trans owned)
        have whoEq : who = player := Option.some.inj (actor.symm.trans sameActor)
        exact foreign (ownerEq.trans whoEq.symm)
      have swapped := supported_completions_exchange before other event otherReady retainedReady
        different actorsDiffer otherAction action otherValue value otherSupported supported
      obtain ⟨firstSupported, rebuilt, rebuiltTrace, same⟩ := ih swapped.1
      have otherReadyAfter : (before.complete event retainedReady action value).cut.Ready other :=
        otherReady.after_complete retainedReady different
      have rebuiltReady : rebuilt.cut.Ready other := by
        rw [← semanticKey_cut_eq same]
        exact otherReadyAfter
      have rebuiltSupported := Config.complete_supported_of_semanticKey_eq
        (before.complete event retainedReady action value) rebuilt same other otherReadyAfter
          rebuiltReady otherAction otherValue swapped.2.1
      refine ⟨firstSupported, rebuilt.complete other rebuiltReady otherAction otherValue,
        .snoc rebuiltTrace other rebuiltReady owner otherActor foreign otherAction otherValue
          rebuiltSupported, ?_⟩
      exact swapped.2.2.trans
        (semanticKey_complete_congr same other otherReadyAfter rebuiltReady otherAction otherValue)

omit [DecidableEq Player] in
/-- A supported foreign completion trace retains every earlier completed event. -/
theorem ForeignCompletionSequence.completed_subset {who : Player} {first last : graph.Config}
    (sequence : graph.ForeignCompletionSequence who first last) :
    first.cut.completed ⊆ last.cut.completed := by
  induction sequence with
  | refl => exact fun _ member => member
  | snoc previous other ready owner actor foreign action value supported ih =>
      intro event member
      exact Finset.mem_insert.mpr (Or.inr (ih member))

omit [DecidableEq Player] in
/-- A ready target remains ready through a foreign trace when it is still
unfinished at the end, independently of its owner. -/
theorem ForeignCompletionSequence.ready_of_unfinished
    {who : Player} {first last : graph.Config}
    (sequence : graph.ForeignCompletionSequence who first last)
    (event : graph.EventId) (ready : first.cut.Ready event)
    (unfinished : event ∉ last.cut.completed) : last.cut.Ready event := by
  refine ⟨unfinished, ?_⟩
  exact fun predecessor dependency => sequence.completed_subset (ready.2 dependency)

/-- Barrier ordering makes every intervening completion foreign to any
still-ready target's owner, while preserving the actual trace unchanged. -/
theorem ForeignCompletionSequence.retag {who : Player} {first last : graph.Config}
    (sequence : graph.ForeignCompletionSequence who first last)
    (ordered : graph.BarrierOrdered) (event : graph.EventId) (ready : first.cut.Ready event)
    (unfinished : event ∉ last.cut.completed) (owner : Player)
    (actor : graph.actor? event = some owner) :
    graph.ForeignCompletionSequence owner first last := by
  induction sequence with
  | refl => exact .refl _
  | @snoc before previous other otherReady otherOwner otherActor foreign action value
      supported ih =>
      have unfinishedBefore : event ∉ before.cut.completed := by
        intro completed
        exact unfinished (Finset.mem_insert.mpr (Or.inr completed))
      have targetReady := previous.ready_of_unfinished event ready unfinishedBefore
      have ownersDiffer : otherOwner ≠ owner := by
        intro equal
        have same := ordered.ready_actor_unique before.cut targetReady otherReady actor
          (equal ▸ otherActor)
        subst other
        exact unfinished (Finset.mem_insert.mpr (Or.inl rfl))
      exact .snoc (ih unfinishedBefore) other otherReady otherOwner otherActor ownersDiffer
        action value supported

/-- No owned foreign completion can intervene while a public chance target
remains ready and unfinished under the compiler's barrier discipline. -/
theorem ForeignCompletionSequence.eq_of_ready_actor_none
    {who : Player} {first last : graph.Config}
    (sequence : graph.ForeignCompletionSequence who first last)
    (ordered : graph.BarrierOrdered) (event : graph.EventId) (ready : first.cut.Ready event)
    (unfinished : event ∉ last.cut.completed) (actor : graph.actor? event = none) :
    first = last := by
  cases sequence with
  | refl => rfl
  | @snoc before previous other otherReady owner otherActor foreign action value supported =>
      have unfinishedBefore : event ∉ before.cut.completed := by
        intro completed
        exact unfinished (Finset.mem_insert.mpr (Or.inr completed))
      have targetReady := previous.ready_of_unfinished event ready unfinishedBefore
      have same := ordered.ready_public_unique _
        (EventCode.output_public_of_actor_none (graph.nodes event) actor) targetReady otherReady
      subst other
      exact (unfinished (Finset.mem_insert.mpr (Or.inl rfl))).elim


omit [DecidableEq Player] in
/-- The actual completion domain suffices to retag a trace when every newly
completed owner is foreign to the selected player. -/
theorem ForeignCompletionSequence.retag_of_completed_diff
    {who : Player} {first last : graph.Config}
    (sequence : graph.ForeignCompletionSequence who first last) (owner : Player)
    (foreignOwners : ∀ event ∈ last.cut.completed, event ∉ first.cut.completed →
      graph.actor? event ≠ some owner) : graph.ForeignCompletionSequence owner first last := by
  induction sequence with
  | refl => exact .refl _
  | @snoc before previous other ready otherOwner actor foreign action value supported ih =>
      have foreignEarlier : ∀ event ∈ before.cut.completed, event ∉ first.cut.completed →
          graph.actor? event ≠ some owner := by
        intro event completed absent
        exact foreignOwners event (Finset.mem_insert.mpr (Or.inr completed)) absent
      have new : other ∉ first.cut.completed := by
        intro member
        exact ready.1 (previous.completed_subset member)
      have different : otherOwner ≠ owner := by
        intro equal
        exact foreignOwners other (Finset.mem_insert.mpr (Or.inl rfl)) new (equal ▸ actor)
      exact .snoc (ih foreignEarlier) other ready otherOwner actor different action value supported

end Vegas.EventGraph
