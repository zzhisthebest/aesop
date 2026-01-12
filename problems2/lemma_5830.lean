import Aesop
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def reverseString_precond (s : String) : Prop :=
  True

def reverseString (s : String) (h_precond : reverseString_precond (s)) : String :=
  let rec reverseAux (chars : List Char) (acc : List Char) : List Char :=
    match chars with
    | [] => acc
    | h::t => reverseAux t (h::acc)
  String.mk (reverseAux (s.toList) [])

@[reducible]
def reverseString_postcond (s : String) (result: String) (h_precond : reverseString_precond (s)) : Prop :=
  result.length = s.length ∧ result.toList = s.toList.reverse


theorem string_length_eq (t : String) : t.length = t.toList.length:= by 
aesop(config:={enableGrind:=false,enableOmega:=false})


end tmp