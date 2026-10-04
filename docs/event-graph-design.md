# Typed event graphs

The compiler lowers the source program to immutable typed fields and bind,
resolve and sample nodes. Dependencies determine readiness. Execution carries a
completed cut, typed store, event history and original owner action recall.

A bind stores a private value or failure. A resolve produces a public result
using its binding and guard inputs. A sample executes the source public chance
kernel. Each legal step adds one ready event to the completed cut.

Sequentialization adds source-rank predecessor edges. Barrier order permits
independent different-owner bindings between public events while ordering public
observations. Commuting stores alone does not identify the information or
strategic games of those orders.

The owning interfaces are [Basic](../Vegas/EventGraph/Basic.lean),
[Execution](../Vegas/EventGraph/Execution.lean),
[Information](../Vegas/EventGraph/Information.lean),
[Barriers](../Vegas/EventGraph/Barriers.lean) and
[PolicyCommutation](../Vegas/EventGraph/PolicyCommutation.lean).
The pending-message application is a separate backend; graph readiness does not
by itself guarantee that a player is activated or its packet is included.
See the [compiler design](compilation-design.md) and [SE plan](se-schedule-generalization.md).
