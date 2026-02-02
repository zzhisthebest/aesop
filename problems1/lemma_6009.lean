import Codetic
set_option maxHeartbeats 0
namespace tmp
@[reducible]
def runLengthEncoder_precond (input : String) : Prop :=
  True

def runLengthEncoder (input : String) (h_precond : runLengthEncoder_precond (input)) : String :=
  let chars : String → List Char := fun s => s.data

  let charEq : Char → Char → Bool := fun c1 c2 => c1 == c2

  let numToString : Nat → String := fun n =>
    let rec digits : Nat → List Char := fun n =>
      if n < 10 then
        [Char.ofNat (n + 48)]
      else
        digits (n / 10) ++ [Char.ofNat (n % 10 + 48)]
    String.mk (digits n)

  let rec encode : List Char → Option Char → Nat → String :=
    fun input currentChar count =>
      match input with
      | [] =>
        match currentChar with
        | none => ""
        | some c => String.mk [c] ++ numToString count
      | c::rest =>
        match currentChar with
        | none => encode rest c 1
        | some c' =>
          if charEq c c' then
            encode rest c' (count + 1)
          else
            let currentPart := String.mk [c'] ++ numToString count
            currentPart ++ encode rest c 1

  if input.isEmpty then
    ""
  else
    let firstChar := (chars input).head?
    encode (chars input).tail firstChar 1

@[reducible]
def runLengthEncoder_postcond (input : String) (result: String) (h_precond : runLengthEncoder_precond (input)) : Prop :=
  let chars : String → List Char := fun s => s.data

  let parseEncodedString : String → List (Char × Nat) :=
    let rec parseState : List Char → Option Char → Option Nat → List (Char × Nat) → List (Char × Nat) :=
      fun remaining currentChar currentCount acc =>
        match remaining with
        | [] =>
          match currentChar, currentCount with
          | some c, some n => (c, n) :: acc
          | _, _ => acc
        | c :: cs =>
          if c.isDigit then
            match currentChar with
            | none => []
            | some ch =>
              let digit := c.toNat - 48
              let newCount :=
                match currentCount with
                | none => digit
                | some n => n * 10 + digit
              parseState cs currentChar (some newCount) acc
          else
            let newAcc :=
              match currentChar, currentCount with
              | some ch, some n => (ch, n) :: acc
              | _, _ => acc
            parseState cs (some c) none newAcc

    fun s =>
      let result := parseState (chars s) none none []
      result.reverse

  let formatValid : Bool :=
    let rec checkPairs (chars : List Char) (nowDigit : Bool) : Bool :=
      match chars with
      | [] => true
      | c :: cs =>
        if nowDigit && c.isDigit then
          checkPairs cs true
        else
          match cs with
          | [] => false
          | d :: ds =>
            if d.isDigit then
              checkPairs ds true
            else
              false

    checkPairs (chars result) false

  let contentValid : Bool :=
    let pairs := parseEncodedString result
    let expanded := pairs.flatMap (fun (c, n) => List.replicate n c)
    expanded == chars input

  let nonEmptyValid : Bool :=
    input.isEmpty = result.isEmpty

  formatValid && contentValid && nonEmptyValid


theorem tail_cons {α} (x : α) (xs : List α) : (x :: xs).tail = xs:= by 
codetic?(config := { enableGrind := false })


end tmp