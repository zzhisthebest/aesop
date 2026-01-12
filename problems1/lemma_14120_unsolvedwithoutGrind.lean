import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible, simp]
def append_precond (a : Array Int) (b : Int) : Prop :=
  True

def copy (a : Array Int) (i : Nat) (acc : Array Int) : Array Int :=
  if i < a.size then
    copy a (i + 1) (acc.push (a[i]!))
  else
    acc

def append (a : Array Int) (b : Int) (h_precond : append_precond (a) (b)) : Array Int :=
  let c_initial := copy a 0 (Array.empty)
  let c_full := c_initial.push b
  c_full

@[reducible, simp]
def append_postcond (a : Array Int) (b : Int) (result: Array Int) (h_precond : append_precond (a) (b)) :=
  (List.range' 0 a.size |>.all (fun i => result[i]! = a[i]!)) ∧
  result[a.size]! = b ∧
  result.size = a.size + 1
@[simp]
theorem Array.get_push_spec {α} (a : Array α) (v : α) (i : Nat) :
    (a.push v)[i]? = if i < a.size then a[i]? else if i = a.size then some v else none := by
  aesop
@[simp] theorem getElem!_eq_getElem?_getD [Inhabited α] (a : Array α) (i : Nat) :
    a[i]! = (a[i]?).getD default := by
  -- 证明部分
  aesop

#check getElem?_pos
#check getElem!_pos

theorem push_preserves_get (a : Array Int) (b : Int) (i : Nat) (h : i < a.size) :
    (a.push b)[i]! = a[i]!:= by
aesop?(config := { enableGrind := false })


end tmp
