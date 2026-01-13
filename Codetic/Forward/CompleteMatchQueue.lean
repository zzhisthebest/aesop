import Batteries.Data.BinomialHeap.Basic
import Codetic.Forward.Match

set_option linter.missingDocs true

namespace Codetic

open Batteries (BinomialHeap)

/-- A complete match queue. -/
abbrev CompleteMatchQueue := BinomialHeap ForwardRuleMatch ForwardRuleMatch.le

namespace CompleteMatchQueue

/-- Drop elements satisfying `f` from the front of `queue` until we reach
an element that does not satisfy `f` (or until the queue is empty). -/
partial def dropInitial (queue : CompleteMatchQueue)
    (f : ForwardRuleMatch → Bool) : CompleteMatchQueue :=
  match queue.deleteMin with
  | none => queue
  | some (m, queue') =>
    if f m then
      dropInitial queue' f
    else
      queue

end Codetic.CompleteMatchQueue
