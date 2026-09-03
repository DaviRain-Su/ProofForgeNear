import Examples.Lang
import Tests.Fixtures

namespace Tests.LangSpec

open Examples.Lang

#guard (init 7).cells[0]! == 7
#guard get (init 7) == 7
#guard band (init 0) 0xf0 0x0f == 0
#guard bor (init 0) 0xf0 0x0f == 0xff
#guard bxor (init 0) 0xff 0x0f == 0xf0
#guard bnot (init 0) 0 == u64Max
#guard shl (init 0) 1 3 == 8
#guard shr (init 0) 8 3 == 1
#guard shl (init 0) 1 65 == 2
#guard shr (init 0) 8 67 == 1
#guard mask8 (init 0) 7 == 7
#guard Tests.Fixtures.getNarrowPrevious (Tests.Fixtures.initNarrow 7) 0 == 7
#guard
  match both (init 9) with
  | (a, b) => a == 9 && b == 0

end Tests.LangSpec
