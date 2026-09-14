/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionPolicy
import Interaction.SealedResolutionEvents

/-! # Public terminal reconstruction for sealed resolution

Public settlement replays only public initial fields and opening events.
Acceptance events remain opaque: their values are never recovered from the
ideal commitment service.  Compiled payoff evaluation is one projection of
this public store, not a definition of utility.
-/

noncomputable section

namespace Vegas.EventGraph.Graph

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}

/-- Initial graph fields whose ownership metadata marks them public. -/
def initialPublicStore (G : Graph Player L) : Store L := fun field =>
  match G.field? field with
  | none => none
  | some spec => if spec.owner = none then spec.initialValue? else none

/-- Replay public openings without inspecting accepted commitment handles. -/
def replayPublicOpenings (G : Graph Player L) (ty : L.Ty) (store : Store L) :
    List (SealedProgram.Event Player (L.Val ty)) → Store L
  | [] => store
  | .accepted _ _ :: rest => G.replayPublicOpenings ty store rest
  | .opened node value :: rest =>
      G.replayPublicOpenings ty (store.set (G.nodeTarget node) ⟨ty, value⟩) rest

/-- Store observable from public initial data and the public event log alone. -/
def publicSealedStore (G : Graph Player L) (ty : L.Ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) : Store L :=
  G.replayPublicOpenings ty G.initialPublicStore events

end Vegas.EventGraph.Graph

namespace Vegas.EventGraph.SealedFragment

open Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty} [DecidableEq (L.Val ty)]

omit [DecidableEq (L.Val ty)] in
private theorem replayPublicOpenings_agrees
    (supported : SealedFragment G ty)
    (service : IdealCommitments Player Nat (L.Val ty))
    (allEvents events : List (SealedProgram.Event Player (L.Val ty)))
    (hsub : ∀ event, event ∈ events → event ∈ allEvents)
    (haccepted : ∀ node handle, .accepted node handle ∈ allEvents →
      ∃ owner value rule,
        supported.compile.rules[node]? = some rule ∧ rule.kind = .commit owner ∧
          handle = (owner, node) ∧ service.lookup handle = some value)
    (publicStore : Store L) (cfg result : Config G)
    (hagrees : ∀ field spec, G.field? field = some spec → spec.owner = none →
      publicStore field = cfg.store field)
    (hdecode : G.decodeSealedFrom ty service cfg events = some result) :
    ∀ field spec, G.field? field = some spec → spec.owner = none →
      G.replayPublicOpenings ty publicStore events field = result.store field := by
  induction events generalizing publicStore cfg with
  | nil =>
      cases Option.some.inj hdecode
      exact hagrees
  | cons event rest ih =>
      have htail : ∀ prior, prior ∈ rest → prior ∈ allEvents := by
        intro prior hprior
        exact hsub prior (List.mem_cons_of_mem event hprior)
      unfold Graph.decodeSealedFrom at hdecode
      unfold Graph.decodeSealedEvent at hdecode
      split at hdecode
      · rename_i hnode
        cases event with
        | accepted node handle =>
            cases hlookup : service.lookup handle with
            | none => simp [hlookup] at hdecode
            | some value =>
                simp only [hlookup, Option.map_some, Option.bind_some] at hdecode
                dsimp only [Graph.replayPublicOpenings]
                apply ih htail _ _ ?_ hdecode
                intro field spec hfield hpublic
                by_cases heq : field = G.nodeTarget node
                · subst field
                  obtain ⟨owner, stored, rule, hrule, hkind, hhandle, _⟩ :=
                    haccepted node handle (hsub _ (List.mem_cons_self ..))
                  obtain ⟨index, guard, hindex, hsem⟩ :=
                    supported.ruleAt_commit hrule hkind
                  have htarget := G.field?_nodeTarget
                    (G.nodes_get?_nodeRow index)
                  rw [hindex] at htarget
                  rw [hfield] at htarget
                  have hwf := supported.graphWF index (G.nodeRow index)
                    (G.nodes_get?_nodeRow index)
                  unfold Graph.nodeWFAt at hwf
                  rw [hsem] at hwf
                  have howner : spec.owner = some owner := by
                    rw [Option.some.inj htarget]
                    exact hwf.2.2.1
                  rw [hpublic] at howner
                  contradiction
                · simp only [Config.completeNode, SealedProgram.Event.node]
                  rw [Store.set_ne _ heq]
                  exact hagrees field spec hfield hpublic
        | opened node value =>
            simp only [Option.bind_some] at hdecode
            dsimp only [Graph.replayPublicOpenings]
            apply ih htail _ _ ?_ hdecode
            intro field spec hfield hpublic
            by_cases heq : field = G.nodeTarget node
            · subst field
              simp [Config.completeNode, SealedProgram.Event.node]
            · simp only [Config.completeNode, SealedProgram.Event.node]
              rw [Store.set_ne _ heq, Store.set_ne _ heq]
              exact hagrees field spec hfield hpublic
      · simp at hdecode

omit [DecidableEq (L.Val ty)] in
/-- Public reconstruction agrees with proof-side decoding on every typed
public graph field.  The result does not inspect the ideal service. -/
theorem publicSealedStore_agrees
    (supported : SealedFragment G ty) (nullValue : L.Val ty) (window : Nat)
    (state : SealedResolution.ApplicationState Player (L.Val ty))
    (hinvariant : SealedResolution.EventInvariant
      (supported.resolvingRuntime nullValue window) state)
    (cfg : Config G)
    (hdecode : G.decodeSealedFrom ty state.service (Config.initial G)
      state.visible.events = some cfg)
    (ref : FieldRef L) (hpublic : G.fieldRefPublic ref) :
    Store.getAs (G.publicSealedStore ty state.visible.events) ref.field ref.ty =
      Store.getAs cfg.store ref.field ref.ty := by
  obtain ⟨spec, hfield, hty, howner⟩ := hpublic
  have hagrees := supported.replayPublicOpenings_agrees state.service
    state.visible.events state.visible.events (fun _ h => h)
    hinvariant.acceptedBinding.accepted G.initialPublicStore (Config.initial G) cfg
    (by
      intro field initialSpec hinitial hpublic
      simp only [Graph.initialPublicStore, hinitial, if_pos hpublic,
        Config.initial, Graph.initialStore]) hdecode ref.field spec hfield howner
  unfold Store.getAs Graph.publicSealedStore
  rw [hagrees]

end Vegas.EventGraph.SealedFragment

namespace Vegas.SealedCompilation

open EventGraph Interaction

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {source : WFProgram Player L} {ty : L.Ty}

/-- The compiled source payout evaluated solely from public native data.
Applications may instead apply any utility or outcome map to `publicSealedStore`.
-/
def publicPayout? (_compilation : SealedCompilation source ty)
    (events : List (SealedProgram.Event Player (L.Val ty))) : Option (Payout Player) :=
  evalPayoffs? (ToEventGraph.compile source.core).payoffs
    ((ToEventGraph.compile source.core).graph.publicSealedStore ty events)

end Vegas.SealedCompilation
