-- -----Description-----  
-- This problem involves combining two maps by creating a new map that includes every key from both inputs. When a key is found in both maps, the value from the second map is used in the result.
--
-- -----Input-----  
-- The input consists of:  
-- • m1: A Map (represented as a list of key-value pairs) where each key is of type Int and each value is of type Int.  
-- • m2: A Map (similarly represented) where keys may overlap with m1.
--
-- -----Output-----  
-- The output is a Map that meets the following conditions:  
-- • Every key present in m2 is present in the result.  
-- • Every key present in m1 is also present in the result.  
-- • For keys that appear in both maps, the resulting value is the one from m2.  
-- • For keys that appear only in m1, the resulting value remains unchanged.  
-- • No keys outside those present in m1 or m2 are included in the result.
-- • The entries in the map should be sorted
--
-- -----Note-----  
-- It is assumed that the Map structure ensures key uniqueness in the final result using BEq for key comparison.

-- !benchmark @start import type=solution

-- !benchmark @end import

-- !benchmark @start task_aux
structure Map (K V : Type) [BEq K] [BEq V] where
  entries : List (K × V)
deriving Inhabited

instance  (K V : Type) [BEq K] [BEq V] : BEq (Map K V) where
  beq m1 m2 := List.length m1.entries = List.length m2.entries ∧ List.beq m1.entries m2.entries

def empty {K V : Type} [BEq K] [BEq V] : Map K V := ⟨[]⟩

def insert {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) (v : V) : Map K V :=
  let entries := m.entries.filter (fun p => ¬(p.1 == k)) ++ [(k, v)]
  ⟨entries⟩

-- !benchmark @end task_aux

-- !benchmark @start solution_aux

-- !benchmark @end solution_aux

-- !benchmark @start precond_aux

-- !benchmark @end precond_aux
@[reducible, simp]
def update_map_precond (m1 : Map Int Int) (m2 : Map Int Int) : Prop :=
  -- !benchmark @start precond
  True
  -- !benchmark @end precond


-- !benchmark @start code_aux

-- !benchmark @end code_aux


def update_map (m1 : Map Int Int) (m2 : Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Map Int Int :=
  -- !benchmark @start code
  let foldFn := fun (acc : Map Int Int) (entry : Int × Int) =>
    insert acc entry.1 entry.2
  let updated := m2.entries.foldl foldFn m1
  ⟨updated.entries.mergeSort (fun a b => a.1 ≤ b.1)⟩
  -- !benchmark @end code


-- !benchmark @start postcond_aux
def find? {K V : Type} [BEq K] [BEq V] (m : Map K V) (k : K) : Option V :=
  m.entries.find? (fun p => p.1 == k) |>.map (·.2)
-- !benchmark @end postcond_aux


@[reducible, simp]
def update_map_postcond (m1 : Map Int Int) (m2 : Map Int Int) (result: Map Int Int) (h_precond : update_map_precond (m1) (m2)) : Prop :=
  -- !benchmark @start postcond
  List.Pairwise (fun a b => a.1 ≤ b.1) result.entries ∧
  m2.entries.all (fun x => find? result x.1 = some x.2) ∧
  m1.entries.all (fun x =>
    match find? m2 x.1 with
    | some _ => true
    | none => find? result x.1 = some x.2
  ) ∧
  result.entries.all (fun x =>
    match find? m1 x.1 with
    | some v => match find? m2 x.1 with
      | some v' => x.2 = v'
      | none => x.2 = v
    | none => find? m2 x.1 = some x.2
  )
  -- !benchmark @end postcond


-- !benchmark @start proof_aux

-- !benchmark @end proof_aux


theorem update_map_spec_satisfied (m1: Map Int Int) (m2: Map Int Int) (h_precond : update_map_precond (m1) (m2)) :
    update_map_postcond (m1) (m2) (update_map (m1) (m2) h_precond) h_precond := by
  -- !benchmark @start proof
  sorry
  -- !benchmark @end proof

