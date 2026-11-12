module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.EventGraph.LastSchedulerErasure
public import Vegas.EventGraph.DecisionTwin
public import Vegas.EventGraph.PolicyPatch

@[expose] public section

/-! # The last-served law of erased keys

The erased key of a configuration is the order-free key of its erasure: the
cut, the store and the completion record of each event, with the decisions of
defaulted players wiped. It is read from the order-free key, and completing an
event maps configurations with one erased key to configurations with one erased
key.

The last-served law of erased keys is the law of the final erased key when one
player is served last. It is the image of the last-served key law, so it is
read from the erased key of the starting configuration for every ready
independent profile away from that player. When the event the scheduler serves
first is the only event two profiles disagree at, the run of the first profile
takes that event's step and then follows the second.
-/

noncomputable section

namespace Vegas.EventGraph

open GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player]
variable {L : IExpr} [IExpr.ResultTypes L]
variable {graph : Vegas.EventGraph Player L}

/-- The order-free key of a configuration with the decisions of its defaulted
players erased. -/
def erasedKey (config : graph.Config) := runKey config.erase

omit [DecidableEq Player] in
/-- A law mapped by a readout of a key is read from the law of the key. -/
theorem map_eq_of_map_key_eq {α β γ : Type} (key : α → β) (read : α → γ)
    (factors : ∀ left right, key left = key right → read left = read right)
    {left right : PMF α} (same : left.map key = right.map key) :
    left.map read = right.map read := by
  have bound := bind_eq_of_map_key_eq key Set.univ left right (Set.subset_univ _)
    (Set.subset_univ _) same (fun item => PMF.pure (read item))
    (fun first _ second _ keys => by rw [factors first second keys])
  change left.bind (PMF.pure ∘ read) = right.bind (PMF.pure ∘ read) at bound
  rwa [PMF.bind_pure_comp, PMF.bind_pure_comp] at bound

/-- Completing one event maps configurations with one key to configurations
with one key. -/
theorem runKey_complete_congr {left right : graph.Config} (same : runKey left = runKey right)
    (event : graph.EventId) (leftReady : left.cut.Ready event)
    (rightReady : right.cut.Ready event) (action : graph.Action event)
    (value : (graph.outputLayout event).Value) :
    runKey (left.complete event leftReady action value) =
      runKey (right.complete event rightReady action value) := by
  have cut : left.cut = right.cut := congrArg Prod.fst same
  have store : left.store = right.store := congrArg (fun key => key.2.1) same
  have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
  have defaulted := defaulted_eq_of_completionOf_eq records
  have decision : left.actualDecision event action = right.actualDecision event action := by
    simp only [Config.actualDecision, defaulted]
  simp only [runKey, storeRecall]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · ext member
    simp only [Config.complete_cut, EventOrder.Cut.mem_complete, cut]
  · simp only [store_complete, store]
  · simp only [completionOf_complete, records, decision]

/-- The erased key is read from the key. -/
theorem erasedKey_congr {left right : graph.Config} (same : runKey left = runKey right) :
    erasedKey left = erasedKey right := by
  have records : completionOf left = completionOf right := congrArg (fun key => key.2.2) same
  have defaulted := defaulted_eq_of_completionOf_eq records
  have store : left.store = right.store := congrArg (fun key => key.2.1) same
  have cut : left.cut = right.cut := congrArg Prod.fst same
  simp only [erasedKey, runKey, storeRecall]
  refine Prod.ext cut (Prod.ext store ?_)
  funext event
  change completionOf left.erase event = completionOf right.erase event
  rw [completionOf_erase, completionOf_erase, records, defaulted]

theorem erasedKey_erase (config : graph.Config) : erasedKey config.erase = erasedKey config := by
  unfold erasedKey
  rw [Config.erase_erase]

/-- Configurations with one erased key have the same defaulted players. -/
theorem defaulted_eq_of_erasedKey_eq {left right : graph.Config}
    (same : erasedKey left = erasedKey right) : left.defaulted = right.defaulted := by
  have records : completionOf left.erase = completionOf right.erase :=
    congrArg (fun key => key.2.2) same
  rw [← Config.erase_defaulted left, ← Config.erase_defaulted right]
  exact defaulted_eq_of_completionOf_eq records

theorem cut_eq_of_erasedKey_eq {left right : graph.Config}
    (same : erasedKey left = erasedKey right) : left.cut = right.cut :=
  congrArg Prod.fst same

/-- Completing one event maps configurations with one erased key to
configurations with one erased key. -/
theorem erasedKey_complete_congr {left right : graph.Config}
    (same : erasedKey left = erasedKey right) (event : graph.EventId)
    (leftReady : left.cut.Ready event) (rightReady : right.cut.Ready event)
    (action : graph.Action event) (value : (graph.outputLayout event).Value) :
    erasedKey (left.complete event leftReady action value) =
      erasedKey (right.complete event rightReady action value) := by
  unfold erasedKey
  rw [← Config.erase_complete_erase left event leftReady action value,
    ← Config.erase_complete_erase right event rightReady action value]
  exact erasedKey_congr (runKey_complete_congr same event leftReady rightReady action value)

/-- The run when `who` is served last, from a configuration with its remaining
fuel. -/
def lastRun (profile : graph.BehavioralProfile) (who : Player) (config : graph.Config) :=
  graph.runPlan (graph.policyPlan profile (graph.lastScheduler who)) config.remaining config

/-- The law of the final erased key when `who` is served last. -/
def lastErasedLaw (profile : graph.BehavioralProfile) (who : Player) (config : graph.Config) :=
  (lastRun profile who config).map erasedKey

/-- The last-served run takes the step of the event the scheduler picks. -/
theorem lastRun_step (profile : graph.BehavioralProfile) (who : Player) (config : graph.Config)
    (notTerminal : ¬ config.cut.Terminal) (event : graph.EventId) (ready : config.cut.Ready event)
    (picked : event = graph.lastPick who config.cut.enabled
      (enabled_nonempty_of_not_terminal config notTerminal)) :
    lastRun profile who config =
      (eventStep profile config event ready).bind (lastRun profile who) := by
  obtain ⟨rest, restEq⟩ : ∃ rest, config.remaining = rest + 1 := by
    have positive : config.remaining ≠ 0 :=
      fun zero => notTerminal ((config.terminal_iff_remaining_zero).mpr zero)
    exact ⟨config.remaining - 1, by omega⟩
  unfold lastRun
  rw [restEq, runPlan_policyPlan_succ profile _ rest config notTerminal]
  simp only [EventGraph.lastScheduler, PMF.pure_bind]
  rw [eventStep_congr_event profile config picked.symm _ ready]
  apply bind_congr_on_support _
  intro next member
  have consumed : next.remaining + 1 = config.remaining := by
    unfold eventStep at member
    rw [PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨action, _, stepped⟩ := member
    exact config.remaining_step event ready action next stepped
  rw [(by omega : next.remaining = rest)]

/-- The last-served key law is the key image of the last-served run. -/
theorem lastLaw_eq_map_lastRun (profile : graph.BehavioralProfile) (who : Player)
    (config : graph.Config) :
    lastLaw profile who config = (lastRun profile who config).map runKey :=
  rfl

/-- Equal last-served key laws give equal last-served erased-key laws. -/
theorem lastErasedLaw_eq_of_lastLaw_eq {left right : graph.BehavioralProfile} {who : Player}
    {leftConfig rightConfig : graph.Config}
    (same : lastLaw left who leftConfig = lastLaw right who rightConfig) :
    lastErasedLaw left who leftConfig = lastErasedLaw right who rightConfig :=
  map_eq_of_map_key_eq runKey erasedKey (fun _ _ keys => erasedKey_congr keys) same

/-- A configuration and its erasure have one last-served erased-key law. -/
theorem lastErasedLaw_erase (profile : graph.BehavioralProfile) (who : Player)
    (config : graph.Config) :
    lastErasedLaw profile who config.erase = lastErasedLaw profile who config := by
  have commuted := runPlan_map_erase profile (graph.lastScheduler who) config.remaining config
  have erasedRead : (erasedKey : graph.Config → _) = erasedKey ∘ Config.erase := by
    funext current
    exact (erasedKey_erase current).symm
  unfold lastErasedLaw lastRun
  change (graph.runPlan _ config.remaining config.erase).map erasedKey = _
  rw [erasedRead, ← PMF.map_comp, ← PMF.map_comp, commuted]

/-- **The last-served erased-key law is read from the erased key.** -/
theorem LastIndependent.lastErasedLaw_congr {profile : graph.BehavioralProfile} {who : Player}
    (independent : LastIndependent profile who) {left right : graph.Config}
    (same : erasedKey left = erasedKey right) :
    lastErasedLaw profile who left = lastErasedLaw profile who right := by
  rw [← lastErasedLaw_erase profile who left, ← lastErasedLaw_erase profile who right]
  exact lastErasedLaw_eq_of_lastLaw_eq
    (independent.lastLaw_congr _ left.erase right.erase rfl same)

/-- **Patching the first served event.** When two profiles agree away from an
event that the last scheduler serves first, the run of the first takes that
event's step and then follows the second. -/
theorem lastErasedLaw_patch_step {build tail : graph.BehavioralProfile} {who : Player}
    (event : graph.EventId)
    (agree : ∀ config other, other ≠ event →
      actionLaw build config other = actionLaw tail config other)
    (config : graph.Config) (ready : config.cut.Ready event)
    (picked : event = graph.lastPick who config.cut.enabled
      (enabled_nonempty_of_not_terminal config ready.not_terminal)) :
    lastErasedLaw build who config =
      (eventStep build config event ready).bind (lastErasedLaw tail who) := by
  unfold lastErasedLaw
  rw [lastRun_step build who config ready.not_terminal event ready picked,
    PMF.map_bind]
  apply bind_congr_on_support _
  intro next member
  have completed : event ∈ next.cut.completed := by
    unfold eventStep at member
    rw [PMF.support_bind] at member
    simp only [Set.mem_iUnion] at member
    obtain ⟨action, _, stepped⟩ := member
    rw [config.step_cut event ready action next stepped, EventOrder.Cut.mem_complete]
    exact Or.inl rfl
  unfold lastRun
  rw [runPlan_congr_of_actionLaw (graph.lastScheduler who) (fun other => other = event)
    (fun current other different => agree current other different) next.remaining next
    (fun other same => same ▸ completed)]

/-- When an event already completed is the only one two profiles disagree at,
they have one last-served erased-key law. -/
theorem lastErasedLaw_patch_completed {build tail : graph.BehavioralProfile} {who : Player}
    (event : graph.EventId)
    (agree : ∀ config other, other ≠ event →
      actionLaw build config other = actionLaw tail config other)
    (config : graph.Config) (completed : event ∈ config.cut.completed) :
    lastErasedLaw build who config = lastErasedLaw tail who config := by
  unfold lastErasedLaw lastRun
  rw [runPlan_congr_of_actionLaw (graph.lastScheduler who) (fun other => other = event)
    (fun current other different => agree current other different) config.remaining config
    (fun other same => same ▸ completed)]

/-- A terminal configuration has the point law of its erased key. -/
theorem lastErasedLaw_terminal (profile : graph.BehavioralProfile) (who : Player)
    (config : graph.Config) (terminal : config.cut.Terminal) :
    lastErasedLaw profile who config = PMF.pure (erasedKey config) := by
  have zero : config.remaining = 0 := (config.terminal_iff_remaining_zero).mp terminal
  unfold lastErasedLaw lastRun
  rw [zero]
  simp only [EventGraph.runPlan, PMF.pure_map]

end Vegas.EventGraph
