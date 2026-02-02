/-
Copyright (c) 2022 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import CodeticTest.Persistence1
import CodeticTest.Persistence2

set_option codetic.check.all true

namespace Codetic

@[codetic 50% (rule_sets := [test_persistence2])]
def test (b : Bool) : NatOrBool := by
  codetic (rule_sets := [test_persistence1])

end Codetic
