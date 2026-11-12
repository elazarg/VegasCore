module

/- Copyright (c) 2026 VegasCore contributors. Released under the MIT license (see LICENSE). -/

public import Vegas.Compile.EventGraphReadout
public import Vegas.EventGraph.ConcurrentRevealNash
public import Vegas.EventGraph.SequentialNormalization
public import Vegas.EventGraph.SequentialLaw
public import Vegas.EventGraph.PublicationDecision
public import Vegas.Compile.EventGraphPolicy
public import Vegas.Source.Disclosure
public import Vegas.EventGraph.SchedulerReplay

@[expose] public section

/-! # The compiled graph with concurrent reveals

Relaxing the reveal dependencies of the compiled graph makes independent
reveals concurrent and keeps every other event in source order. Sequentializing
the relaxed graph recovers the compiled graph exactly. A source policy that
never refuses a disclosure compiles to a kernel that opens, as a point mass,
at every active publication of its owner, whatever it observes.
-/

noncomputable section

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The compiled graph of a setup with independent reveals concurrent. -/
abbrev concurrentRevealGraph (setup : Setup (Player := Player) (L := L)) :
    Vegas.EventGraph Player L :=
  setup.eventGraph.withMode .concurrentReveals

theorem concurrentRevealGraph_sequentialize (setup : Setup (Player := Player) (L := L)) :
    setup.concurrentRevealGraph.sequentialize = setup.eventGraph := rfl

/-- A law on booleans that never yields `false` is the point mass at `true`. -/
theorem pmf_bool_eq_pure_true (law : PMF Bool) (never : false ∉ law.support) :
    law = PMF.pure true := by
  have falseZero : law false = 0 := (PMF.apply_eq_zero_iff law false).mpr never
  have total := law.tsum_coe
  rw [tsum_bool, falseZero, zero_add] at total
  ext choice
  cases choice
  · simp [falseZero]
  · simp [total]

end Vegas.SourceProgram.Setup

namespace Vegas

open Vegas.EventGraph SourceProgram

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- A disclosing policy's compiled table opens at every active own publication. -/
theorem compilePolicyTable_publication {Field : Type}
    {layout : Field → Vegas.EventGraph.EventField Player L} :
    ∀ {Γ : SourceCtx Player L} {openNames : Finset VarId}
      (program : SourceProgram Player L Γ openNames) (refs : ContextRefs layout Γ)
      (outputs : ∀ event, Vegas.EventGraph.FieldRef layout (outputLayout program event))
      (who : Player) (policy : BehavioralPolicy who program)
      (_disclosing : Disclosing program policy)
      (event : Fin (eventCount program))
      (publication : (outputLayout program event).IsPublication)
      (_owned : eventOwner? program event = some who) (store : Vegas.EventGraph.Store layout)
      (defaults : DefaultHistory Player) (history : List (OwnAction Player L))
      (_active : who ∉ defaults.defaulted),
      compilePolicyTable program refs outputs who policy event store defaults history =
        PMF.pure (EventField.openAction _ publication)
  | _, _, .ret _, _, _, _, _, _, event, _, _, _, _, _, _ => nomatch event
  | _, _, .sample _ _ _ next, refs, outputs, who, policy, disclosing, event, publication, owned,
      store, defaults, history, active => by
      cases event using Fin.cases with
      | zero => exact publication.elim
      | succ tail =>
          exact compilePolicyTable_publication next _ _ who policy disclosing tail publication
            owned store defaults history active
  | _, _, .commit _ _ _ _ next, refs, outputs, who, policy, disclosing, event, publication, owned,
      store, defaults, history, active => by
      cases event using Fin.cases with
      | zero => exact publication.elim
      | succ tail =>
          exact compilePolicyTable_publication next _ _ who policy.2 disclosing tail publication
            owned store defaults history active
  | _, _, .reveal _ owner _ _ _ _ next, refs, outputs, who, policy, disclosing, event,
      publication, owned, store, defaults, history, active => by
      cases event using Fin.cases with
      | zero =>
          have same : owner = who := Option.some.inj owned
          cases decoded : decodeObservation? who refs store with
          | some observation =>
              exact (compilePolicyTable_reveal_of_decode refs outputs policy same store defaults
                active history observation decoded).trans
                  (Setup.pmf_bool_eq_pure_true _
                    (disclosing.1 same ⟨observation, defaults, history⟩ active))
          | none =>
              exact compilePolicyTable_reveal_of_decode_none refs outputs policy same store defaults
                active history decoded
      | succ tail =>
          exact compilePolicyTable_publication next _ _ who policy.2 disclosing.2 tail
            publication owned store defaults history active

/-- A disclosing source policy compiles to a kernel that opens, as a point mass,
at every active publication of its owner. -/
theorem compileEventPolicy_publication {Γ : SourceCtx Player L} {openNames : Finset VarId}
    (program : SourceProgram Player L Γ openNames) (who : Player)
    (policy : BehavioralPolicy who program) (disclosing : Disclosing program policy)
    (event : (toEventGraph program).EventId)
    (actor : (toEventGraph program).actor? event = some who)
    (publication : ((toEventGraph program).outputLayout event).IsPublication)
    (observation : (toEventGraph program).PlayerObservation who)
    (active : who ∉ observation.defaulted) :
    compileEventPolicy program who policy event actor observation active =
      PMF.pure (EventField.openAction _ publication) :=
  compilePolicyTable_publication program _ _ who policy disclosing event publication
    ((eventOwner?_eq_actor program event).trans actor) _ _ _ active

end Vegas

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

/-- The completions of a configuration listed in event rank, one per completed event. -/
def rankedHistory {graph : Vegas.EventGraph Player L} (config : graph.Config) :
    List graph.Completion :=
  (List.finRange graph.order.eventCount).filterMap (completionOf config)

omit [DecidableEq Player] in
theorem rankedHistory_events {graph : Vegas.EventGraph Player L} (config : graph.Config) :
    (rankedHistory config).map EventCompletion.event =
      (List.finRange graph.order.eventCount).filter fun event =>
        (completionOf config event).isSome := by
  unfold rankedHistory
  rw [List.map_filterMap]
  have tagged (event : graph.EventId) :
      (completionOf config event).map EventCompletion.event =
        if (completionOf config event).isSome then some event else none := by
    cases found : completionOf config event with
    | none => rfl
    | some completion =>
        simp [((completionOf_eq_some_iff config event completion).mp found).2]
  rw [List.filterMap_congr fun event _ => tagged event]
  induction (List.finRange graph.order.eventCount) with
  | nil => rfl
  | cons head tail ih =>
      cases present : (completionOf config head).isSome <;> simp [present, ih]

/-- A terminal configuration of the concurrent graph, as a configuration of the
compiled graph whose history lists completions in source order. -/
def rankedConfig (setup : Setup (Player := Player) (L := L))
    (config : setup.concurrentRevealGraph.Config) (terminal : config.cut.Terminal) :
    setup.eventGraph.Config where
  inputs := config.inputs
  cut := { completed := Finset.univ, predecessor_closed := fun _ _ _ => Finset.mem_univ _ }
  outputs := config.outputs
  output_available event := by
    rw [config.output_available, terminal]
  history := rankedHistory (graph := setup.concurrentRevealGraph) config
  history_nodup := by
    have events : ((rankedHistory (graph := setup.concurrentRevealGraph) config).map
        EventCompletion.event).Nodup := by
      rw [rankedHistory_events]
      exact (List.nodup_finRange _).filter _
    exact events
  history_exact event := by
    have events : event ∈ (rankedHistory (graph := setup.concurrentRevealGraph) config).map
        EventCompletion.event := by
      rw [rankedHistory_events, List.mem_filter, ← mem_completed_iff_completionOf, terminal]
      simp
    exact ⟨fun _ => Finset.mem_univ _, fun _ => events⟩

theorem rankedConfig_terminal (setup : Setup (Player := Player) (L := L))
    (config : setup.concurrentRevealGraph.Config) (terminal : config.cut.Terminal) :
    (setup.rankedConfig config terminal).cut.Terminal := rfl

end Vegas.SourceProgram.Setup

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem find?_filterMap_tagged {graph : Vegas.EventGraph Player L}
    (read : graph.EventId → Option graph.Completion)
    (tagged : ∀ event completion, read event = some completion → completion.event = event)
    (event : graph.EventId) :
    ∀ events : List graph.EventId, events.Nodup →
      (events.filterMap read).find? (fun completion => completion.event = event) =
        if event ∈ events then read event else none
  | [], _ => rfl
  | head :: tail, nodup => by
      obtain ⟨headFresh, tailNodup⟩ := List.nodup_cons.mp nodup
      have rest := find?_filterMap_tagged read tagged event tail tailNodup
      cases found : read head with
      | none =>
          simp only [List.filterMap_cons, found, rest, List.mem_cons]
          by_cases same : event = head
          · subst same
            simp [headFresh, found]
          · simp [same]
      | some completion =>
          have headTag := tagged head completion found
          by_cases same : event = head
          · subst same
            simp [found, headTag]
          · have miss : ¬ completion.event = event := fun hit => same (hit.symm.trans headTag)
            simp [found, miss, rest, same]

/-- Recasting in source order keeps every completion record. -/
theorem completionOf_rankedConfig (setup : Setup (Player := Player) (L := L))
    (config : setup.concurrentRevealGraph.Config) (terminal : config.cut.Terminal) :
    completionOf (setup.rankedConfig config terminal) = completionOf config := by
  funext event
  have found := find?_filterMap_tagged (completionOf config)
    (fun event completion found => ((completionOf_eq_some_iff config event completion).mp found).2)
    event _ (List.nodup_finRange _)
  rw [ite_eq_left (List.mem_finRange _)] at found
  exact found

/-- Recasting in source order keeps the defaulted players. -/
theorem defaulted_rankedConfig (setup : Setup (Player := Player) (L := L))
    (config : setup.concurrentRevealGraph.Config) (terminal : config.cut.Terminal) :
    (setup.rankedConfig config terminal).defaulted = config.defaulted := by
  ext who
  rw [mem_defaulted_iff_completionOf, mem_defaulted_iff_completionOf,
    completionOf_rankedConfig]
  exact Iff.rfl

end Vegas.SourceProgram.Setup

namespace Vegas.SourceProgram.Setup

open Vegas.EventGraph

variable {Player : Type} [DecidableEq Player] {L : IExpr} [IExpr.ResultTypes L]

omit [DecidableEq Player] in
private theorem config_eq_of_data_eq {graph : Vegas.EventGraph Player L}
    {left right : graph.Config} (inputs : left.inputs = right.inputs)
    (cut : left.cut = right.cut) (outputs : left.outputs = right.outputs)
    (history : left.history = right.history) : left = right := by
  cases left
  cases right
  simp_all

omit [DecidableEq Player] in
private theorem map_val_finRange (count : Nat) :
    (List.finRange count).map Fin.val = List.range count := by
  apply List.ext_getElem <;> simp

/-- The compiled graph is totally ordered. -/
theorem eventGraph_total (setup : Setup (Player := Player) (L := L))
    (prior event : setup.eventGraph.EventId) (earlier : prior.val < event.val) :
    prior ∈ setup.eventGraph.order.predecessors event :=
  (EventOrder.sequential.mem_predecessors prior event).mpr earlier

/-- A terminal configuration reached by the compiled graph is its own source-order
recasting, viewed in the concurrent graph. -/
theorem rankedConfig_fromSequentialConfig (setup : Setup (Player := Player) (L := L))
    {inputs : setup.eventGraph.Inputs} {config : setup.eventGraph.Config}
    (reach : Config.Reachable inputs config)
    (terminal : (setup.concurrentRevealGraph.fromSequentialConfig config).cut.Terminal) :
    setup.rankedConfig (setup.concurrentRevealGraph.fromSequentialConfig config) terminal =
      config := by
  have complete : config.cut.Terminal := terminal
  have lengthEq : config.history.length = setup.eventGraph.order.eventCount := by
    have exact : config.cut.completed = (config.history.map EventCompletion.event).toFinset := by
      ext event
      rw [List.mem_toFinset, config.history_exact]
    have card := congrArg Finset.card exact
    rw [complete, Finset.card_univ, Fintype.card_fin,
      List.toFinset_card_of_nodup config.history_nodup, List.length_map] at card
    exact card.symm
  have events : config.history.map EventCompletion.event =
      List.finRange setup.eventGraph.order.eventCount := by
    apply List.map_injective_iff.mpr Fin.val_injective
    rw [List.map_map, map_val_finRange]
    have values := history_map_val_of_reachable (setup.eventGraph_total) reach
    rw [lengthEq] at values
    exact values
  have records : ∀ completion ∈ config.history,
      completionOf config completion.event = some completion := fun completion member =>
    (completionOf_eq_some_iff config completion.event completion).mpr ⟨member, rfl⟩
  apply config_eq_of_data_eq
  · rfl
  · ext event
    change event ∈ Finset.univ ↔ event ∈ config.cut.completed
    rw [complete]
  · rfl
  · change (List.finRange _).filterMap (completionOf config) = config.history
    rw [← events, List.filterMap_map]
    calc _ = config.history.filterMap some :=
          List.filterMap_congr fun completion member => records completion member
      _ = config.history := List.filterMap_some

end Vegas.SourceProgram.Setup
