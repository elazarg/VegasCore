# A. Fix the target: what “non-vacuity” should mean here

With your current `toEFG`, the only thing a player can condition on is **pid** (infoset id). So the correct non-vacuity statement is:

> For any two decision nodes in the compiled EFG with the same pid (hence same infoset), the induced action distribution under any behavioral strategy is identical.

This is the textbook imperfect-information guarantee. It does **not** claim the resulting outcome distribution (or EU) is identical—only the *choice distribution* is identical.

So the semantic object can still evolve differently under hidden state (via `k`), as it should.

---

# B. Required core definitions

## B.1 Decision-arity extraction

You need a function/def that extracts the number of available actions at a decision node:

```lean
def arity : GameTree → Option Nat
| .decision _ _ acts => some acts.length
| _                 => none
```

(or a dependent version if your `GameTree.decision` stores a vector; adapt.)

## B.2 Node collection / “occurs in tree”

You need a way to quantify over decision nodes that occur in a tree. Either:

* an inductive predicate `Occurs : GameTree → GameTree → Prop`, or
* a `nodes : GameTree → List Node` with membership.

You can keep it minimal; you only need to talk about decision nodes “in” a tree.

---

# C. Compiler invariants (GameProg → EFG)

## C.1 YieldId determines pid (you have it)

Keep it; it matters.

**Do not weaken** it by adding extra hypotheses; it must be unconditional.

## C.2 Action list depends only on observation (stronger than arity)

Agent is right: given `actions := A obs`, you can prove **full list equality** under `ObsEq`, not just length.

Required statement (strong form):

```lean
theorem actions_eq_of_ObsEq
  (ps : ParentSite …) (A : Act (viewOfVarSpec ps.vars) τ')
  {ρ₁ ρ₂ : Env Γ}
  (hObs : (viewOfVarSpec ps.vars).proj ρ₁ =
          (viewOfVarSpec ps.vars).proj ρ₂) :
  A ((viewOfVarSpec ps.vars).proj ρ₁) =
  A ((viewOfVarSpec ps.vars).proj ρ₂)
```

This is a good, sharp lemma. It pins down “player interface” precisely.

---

# D. Textbook well-formedness requirement you’re missing

This is the **real** missing content.

You must ensure that “same pid” corresponds to a *valid* information set, meaning:

> all decision nodes in that infoset have the same available actions (at least the same arity; ideally same action labels).

Given your setup, “infoset = pid”, and pid is currently `YieldId`. So you need:

## D.1 InfoSet arity consistency for compiled trees (global theorem)

This is the key theorem for v1.0.

Let `G = p.toEFG u env`. Define a predicate on `GameTree`:

```lean
def InfoSetArityConsistent (G : GameTree) : Prop :=
  ∀ pid who acts₁ acts₂,
    Occurs G (.decision pid who acts₁) →
    Occurs G (.decision pid who acts₂) →
    acts₁.length = acts₂.length
```

(You might also want to quantify `who` to be equal, depending on whether pid already encodes player; if not, add it.)

Then the required theorem is:

```lean
theorem toEFG_infoset_arity_consistent
  (p : ParentProtoProg … Γ τ) (u : Utility … τ) (env : Env Γ)
  (hp : WF_GameProg p) :
  InfoSetArityConsistent (p.toEFG u env)
```

**No weakening allowed:**

* it must be about *all* decision nodes with the same pid that occur in the compiled tree.
* it cannot be restricted to “reachable under some strategy” (unless your semantics is reachability-based and you formalize reachability; but v1.0 should avoid that complexity).
* it cannot assume additional congruences like `env₁=env₂`.

This is the theorem a reviewer will accept as “you really built imperfect-information EFGs”.

### How to make it provable

You have two options; pick one and be explicit:

**Option 1 (WF enforces constant arity per YieldId):**
Add a WF condition that ensures for any `choose id …` site, `A obs` has the same length for all `obs`. This is exactly what the agent suggested.

But be careful: if arity depends on obs, that’s not inherently wrong in a *protocol* language; it’s wrong only if you’re mapping infosets solely by `id`. So this WF condition is a *consequence of your chosen compilation scheme*, not a generic semantic truth.

A precise WF clause:

```lean
ConstantArityAtSite (A : Obs → List ActionVal) : Prop :=
  ∀ obs₁ obs₂, (A obs₁).length = (A obs₂).length
```

Then make `WF_GameProg` require this at every choose site.

**Option 2 (pid incorporates enough to ensure arity consistency):**
Change pid design to `(YieldId, arity)` or `(YieldId, obs)` etc. But that *is* a design change; you said “don’t weaken the statement,” so if you keep pid = id, you must take Option 1.

For v1.0, Option 1 is fine and minimal.

---

# E. The real non-vacuity theorem (and it must be local-to-choice, not whole-eval)

Once D.1 holds, your non-vacuity statement becomes *textbook*:

## E.1 Root-choice distribution depends only on pid

Define (in EFG layer) what it means to compute the strategy’s action distribution at a decision node. For a behavioral strategy `σ : pid → Dist (Fin n)` or weights list, you can define:

```lean
def rootChoiceDist : GameTree → BehavioralStrategy → Option (Dist ActionIndex)
| .decision pid _ acts, σ => some (σ pid)   -- suitably typed w.r.t acts.length
| _, _ => none
```

Then the non-vacuity theorem is:

```lean
theorem same_pid_same_choice
  (σ : BehavioralStrategy)
  (pid : Pid) (who : Player) (acts₁ acts₂ : List GameTree)
  (h₁ : acts₁.length = acts₂.length) :
  rootChoiceDist (.decision pid who acts₁) σ =
  rootChoiceDist (.decision pid who acts₂) σ
```

This will be definitional once you choose a strategy representation that is *by pid and arity-correct*.

## E.2 Non-vacuity for compiled choose nodes under ObsEq

Now you can connect views:

Given the same `choose id who ps A k` and two envs with same observation, you can show:

* pid is the same (`id`)
* available actions list is the same (by `actions_eq_of_ObsEq`)
* therefore the *choice distribution* is the same under any σ

A statement that must hold:

```lean
theorem choose_nonvacuity
  (σ : BehavioralStrategy)
  (hObs : ObsEq ps ρ₁ ρ₂) :
  rootChoiceDist ((choose id who ps A k).toEFG u ρ₁) σ =
  rootChoiceDist ((choose id who ps A k).toEFG u ρ₂) σ
```

**No weakening allowed:**

* must quantify over **all** `σ`
* must only assume `ObsEq` (not `ρ₁ = ρ₂`)
* must conclude equality of **choice distributions**, not EU / full eval

That is the right statement, and it is actually what you want.

---

# F. The agent’s two extra design warnings are also real

## F.1 Perfect-information conditioning is currently impossible

If pid = YieldId, then a player cannot condition on *anything* not encoded in pid, including past public moves, unless those correspond to distinct YieldIds.

So for perfect-information games, you need either:

* different YieldIds at different information states (encoder responsibility), or
* pid = (YieldId, obs) (design change), or
* make pid derived from the program position + observed history (heavier)

This is not a proof issue. It’s a **modeling choice** you must state in the v1.0 contract.

## F.2 Constant arity is required if pid collapses multiple nodes

Yes. This is the one place where “it’s all rfl” stops being true. The global theorem D.1 is the substantive one.
