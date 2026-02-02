import Codetic

set_option codetic.check.all true

/--
error: no such rule set: 'Nonexistent'
  (Use 'declare_codetic_rule_set' to declare rule sets.
   Declared rule sets are not visible in the current file; they only become visible once you import the declaring file.)
-/
#guard_msgs in
example : True := by
  codetic (rule_sets := [Nonexistent])
