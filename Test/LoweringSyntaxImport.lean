import Crush

namespace LoweringSyntaxImported

def increment (x : Int) : Int := x + 1

register_lowering term <<
  (increment (term x)) => (smt| (+ $x 1))
>>

end LoweringSyntaxImported
