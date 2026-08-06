import Crush.Translation.Attr
import Crush.Translation.Theories
import Crush.SMT.Quote
open Lean Meta

/-!
# Default head-indexed SMT lowerings

Encodings in this module use the same public `@[crush_lower target]` API available to
downstream users. They are kept out of the structural translator so support for library
constants can grow without extending its central pattern match.

Each lowering is exact for Lean's semantics and declines applications it cannot identify
soundly. In particular, overloaded operations check their type and canonical typeclass
instance; an explicitly supplied custom instance remains uninterpreted.
-/

namespace Crush.DefaultLowerings

open Crush SMT

/-- `Int.natAbs x`, represented in the non-negative `Int` encoding used for `Nat`. -/
@[crush_lower Int.natAbs]
def intNatAbs : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (ite (>= $sx 0) $sx (- $sx)))

/-- `Int.sign x`: `-1`, `0`, or `1` according to the arithmetic sign of `x`. -/
@[crush_lower Int.sign]
def intSign : LoweringHandler := fun ctx => do
  let #[x] := ctx.args | return none
  let sx ← ctx.emitTerm x
  return some (smt| (ite (> $sx 0) 1 (ite (= $sx 0) 0 (- 1))))

/-- Canonical integer/natural divisibility, using the exact remainder characterization
`a ∣ b ↔ b % a = 0`.

`intDivGuard` supplies Lean's value for `% 0`, making the characterization exact at
zero as well. Other carrier types and custom `Dvd` instances are declined. -/
@[crush_lower Dvd.dvd]
def dvd : LoweringHandler := fun ctx => do
  let #[carrier, _, a, b] := ctx.args | return none
  unless ← ctx.hasCanonicalInstance 1 do return none
  let carrier ← whnf carrier
  unless carrier.isConstOf ``Nat || carrier.isConstOf ``Int do return none
  let sa ← ctx.emitTerm a
  let sb ← ctx.emitTerm b
  let remainder := intDivGuard "mod" sb sa
  return some (smt| (= $remainder 0))

end Crush.DefaultLowerings
