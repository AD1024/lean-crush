import Lean

namespace Crush

/-- The certificate language determines inference-rule dispatch. -/
inductive ReplayFormat where
  | alethe
  | cpc
  deriving BEq, Hashable, Inhabited, Repr

instance : ToString ReplayFormat where
  toString | .alethe => "alethe" | .cpc => "cpc"

def ReplayFormat.displayName : ReplayFormat → String
  | .alethe => "Alethe"
  | .cpc => "CPC"

end Crush
