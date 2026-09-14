/- Copyright (c) 2026 VegasCore contributors. All rights reserved. -/

import Vegas.Compile.SealedResolutionReplay
import Vegas.EventGraph.PublicPrefix
import Vegas.EventGraph.KernelRealization

/-! # Graph policies from earlier public disclosures

The graph's explicit public-prefix information condition makes every input of
disclosure-based replay available in the decision's declared reads. Extraction
returns an ordinary graph policy. Neither construction nor its realization
law refers to source syntax, source strategies, or a source/graph roundtrip.
-/

noncomputable section

namespace Vegas.EventGraph.SealedFragment

open Interaction Interaction.MessageApplication GameTheory GameTheory.Math.Probability

variable {Player : Type} [DecidableEq Player] {L : IExpr}
variable {G : Graph Player L} {ty : L.Ty}
variable (supported : SealedFragment G ty)

private def priorOpening (focal : Player)
    (decision : Fin G.nodeCount)
    (coordinate : supported.priorHonestCoordinates focal decision) :
    Fin G.nodeCount :=
  Classical.choose (supported.priorHonestCoordinates_opening focal
    decision coordinate.val coordinate.property)

private theorem priorOpening_spec (focal : Player)
    (decision : Fin G.nodeCount)
    (coordinate : supported.priorHonestCoordinates focal decision) :
    (supported.priorOpening focal decision coordinate).val < decision.val ∧
      (G.nodeRow (supported.priorOpening focal decision coordinate)).sem =
          .reveal (G.nodeTarget coordinate.val) :=
  Classical.choose_spec (supported.priorHonestCoordinates_opening focal
    decision coordinate.val coordinate.property)

variable (hinfo : G.PublicPrefixReadable)

include hinfo in
private theorem priorOpening_mem_reads (focal : Player)
    (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (coordinate : supported.priorHonestCoordinates focal decision) :
    { field := G.nodeTarget
        (supported.priorOpening focal decision coordinate), ty := ty } ∈ guard.choiceReads := by
  let opening := supported.priorOpening focal decision coordinate
  have hspec := supported.priorOpening_spec focal decision coordinate
  have hwf := supported.graphWF opening _ (G.nodes_get?_nodeRow opening)
  simp only [Graph.nodeWFAt, opening, hspec.2] at hwf
  obtain ⟨_, _, _, _, hpublic⟩ := hwf.2
  have hread := hinfo focal decision opening guard hdecision hspec.1 hpublic
  simpa only [supported.rowType] using hread

/-- Read one earlier public opening for each honest assignment coordinate
needed by replay. Public-prefix readability supplies every field through the
decision's declared information; no runtime history is an input. -/
def disclosureInputs (focal : Player)
    (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (reads : ReadEnv L guard.choiceReads) :
    supported.priorHonestCoordinates focal decision → L.Val ty :=
  fun coordinate => reads.read _
    (supported.priorOpening_mem_reads hinfo focal decision guard hdecision coordinate)

/-- In a complete reachable graph, the extracted policy's actual
disclosure inputs are the corresponding commitment values. This follows from
the graph's reveal semantics, not an assumed source/native input equation. -/
theorem disclosureInputs_eq_nodeValues (focal : Player)
    (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard)
    (cfg : ReachableConfig G)
    (hterminal : Terminal G cfg.1)
    (reads : ReadEnv L guard.choiceReads)
    (hreads : ReadEnv.ofStore? cfg.1.store guard.choiceReads = some reads)
    (fallback : L.Val ty) :
    supported.disclosureInputs hinfo focal decision guard hdecision reads =
      fun coordinate => cfg.1.nodeValues fallback coordinate.val := by
  funext coordinate
  let opening := supported.priorOpening focal decision coordinate
  have hspec := supported.priorOpening_spec focal decision coordinate
  have hread := ReadEnv.ofStore?_read hreads
    (supported.priorOpening_mem_reads hinfo focal decision guard hdecision coordinate)
  obtain ⟨row, hrow, hvalid⟩ := reachable_validDoneValues supported.graphWF
    cfg.2 opening (hterminal opening)
  have hrowEq : row = G.nodeRow opening :=
    Option.some.inj (hrow.symm.trans (G.nodes_get?_nodeRow opening))
  subst row
  rw [hspec.2] at hvalid
  change ∃ value : L.Val (G.nodeRow opening).ty,
    Store.getAs cfg.1.store (G.nodeTarget opening)
        (G.nodeRow opening).ty = some value ∧
      Store.getAs cfg.1.store (G.nodeTarget coordinate.val)
        (G.nodeRow opening).ty = some value at hvalid
  rw [supported.rowType opening] at hvalid
  obtain ⟨value, htarget, hproducer⟩ := hvalid
  have hvalue : reads.read _
      (supported.priorOpening_mem_reads hinfo focal decision guard hdecision coordinate) = value :=
    Option.some.inj (hread.symm.trans htarget)
  change reads.read _
    (supported.priorOpening_mem_reads hinfo focal decision guard hdecision coordinate) =
      (Store.getAs cfg.1.store
        (G.nodeTarget coordinate.val) ty).getD fallback
  rw [hproducer, Option.getD_some, hvalue]

/-- Build a legal graph policy from functions of earlier honest
disclosures. The admitted fragment's guards accept every resulting value. -/
def commitPolicyOfDisclosures (focal : Player)
    (choose : (decision : Fin G.nodeCount) →
      (supported.priorHonestCoordinates focal decision → L.Val ty) → L.Val ty) :
    CommitPolicy G focal :=
  fun decision guard hdecision reads => FinDist.pure
    ⟨cast (congrArg L.Val (supported.commitType decision focal guard hdecision).symm)
      (choose decision (supported.disclosureInputs hinfo focal decision guard hdecision reads)),
      supported.commitGuard decision focal guard hdecision _ reads⟩
variable [Fintype Player] (hguards : GuardLive G) (focal : Player)
variable (choose : (decision : Fin G.nodeCount) →
  (supported.priorHonestCoordinates focal decision → L.Val ty) → L.Val ty)
variable (profile : CommitPolicyProfile G)

/-- Execute the graph with one disclosure-based replacement. Opponents are
arbitrary graph policies and retain exactly their original kernels. -/
def runOfDisclosures : FinDist (ReachableConfig G) :=
  runPolicyNodes supported.graphWF hguards
    (GameTheory.Profile.update (sig := ⟨CommitPolicy G, ReachableConfig G⟩)
      profile focal (supported.commitPolicyOfDisclosures hinfo focal choose))
    ⟨Config.initial G, .initial⟩ G.nodeOrder

theorem runOfDisclosures_terminal (cfg : ReachableConfig G)
    (hcfg : cfg ∈ (supported.runOfDisclosures hinfo hguards focal choose profile).support) :
    Terminal G cfg.1 :=
  runPolicyNodes_terminal supported.graphWF hguards _
    ⟨Config.initial G, .initial⟩ G.nodeOrder
    G.nodeOrder_readyOrder (fun node => Or.inr (by simp)) cfg hcfg

/-- Actual complete graph realizations supply exactly the earlier disclosure
values used by the replacement. No input agreement is left as a hypothesis. -/
theorem runOfDisclosures_consistent (fallback : L.Val ty)
    (cfg : ReachableConfig G)
    (hcfg : cfg ∈ (supported.runOfDisclosures hinfo hguards focal choose profile).support)
    (decision : Fin G.nodeCount) (guard : EventGuard L)
    (hdecision : (G.nodeRow decision).sem = .commit focal guard) :
    cfg.1.nodeValues fallback decision =
      choose decision (fun coordinate => cfg.1.nodeValues fallback coordinate.val) := by
  have hterminal := supported.runOfDisclosures_terminal hinfo hguards focal choose profile cfg hcfg
  have hchoices := runPolicyNodes_support_commitValues supported.graphWF
    hguards _ _ (CommitValuesSupported.initial _)
    G.nodeOrder cfg hcfg
  obtain ⟨reads, hreads, choice, hchoice, hvalue⟩ :=
    hchoices decision (hterminal decision) focal guard hdecision
  rw [Profile.update_same] at hchoice
  have hinputs := supported.disclosureInputs_eq_nodeValues hinfo focal decision guard hdecision
    cfg hterminal reads hreads fallback
  simp only [SealedFragment.commitPolicyOfDisclosures, FinDist.mem_support_pure] at hchoice
  have hselected := congrArg (fun value => cast
    (congrArg L.Val (supported.commitType decision focal guard hdecision))
      value.val) hchoice
  simp only [cast_cast, cast_eq, hinputs] at hselected
  change cfg.1.store (G.nodeTarget decision) =
    some (⟨guard.ty, choice.1⟩ : TypedValue L) at hvalue
  rw [Config.nodeValues, Store.getAs, hvalue]
  simpa only [TypedValue.as?,
    dif_pos (supported.commitType decision focal guard hdecision), Option.getD_some]
    using hselected
end Vegas.EventGraph.SealedFragment

/-- info: 'Vegas.EventGraph.SealedFragment.runOfDisclosures_consistent'
depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Vegas.EventGraph.SealedFragment.runOfDisclosures_consistent
