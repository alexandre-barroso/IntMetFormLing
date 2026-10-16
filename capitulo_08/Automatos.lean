import Mathlib

namespace Chapter08Automata

inductive Segment where
  | t | a | d
  deriving DecidableEq, Repr

inductive State where
  | initial | pending | stopped
  deriving DecidableEq, Repr

open Segment State

def transitions : State → Segment → List (State × Segment)
  | stopped, _ => []
  | _, t => [(initial,t)]
  | _, a => [(initial,a)]
  | _, d => [(pending,d),(stopped,t)]

def finalState : State → Bool
  | initial | stopped => true
  | pending => false

def outputs : State → List Segment → List (List Segment)
  | q, [] => if finalState q then [[]] else []
  | q, x::xs => (transitions q x).flatMap
      (fun (r,y) => (outputs r xs).map (fun ys => y::ys))

def devoice : List Segment → List Segment
  | [] => []
  | [d] => [t]
  | [x] => [x]
  | x::y::xs => x::devoice (y::xs)

theorem stopped_nonempty (x : Segment) (xs : List Segment) :
    outputs stopped (x::xs) = [] := by simp [outputs, transitions]

theorem initial_pending_nonempty (x : Segment) (xs : List Segment) :
    outputs initial (x::xs) = outputs pending (x::xs) := by
  cases x <;> rfl

theorem devoice_cons_cons (x y : Segment) (xs : List Segment) :
    devoice (x::y::xs) = x::devoice (y::xs) := by cases x <;> rfl

theorem unique_output (xs : List Segment) : outputs initial xs = [devoice xs] := by
  induction xs with
  | nil => simp [outputs, finalState, devoice]
  | cons x xs ih =>
    cases xs with
    | nil => cases x <;> simp [outputs, transitions, finalState, devoice]
    | cons y ys =>
      have hw := initial_pending_nonempty y ys
      rw [devoice_cons_cons]
      cases x <;> rw [outputs] <;>
        simp only [transitions, List.flatMap_cons, List.flatMap_nil,
          List.append_nil]
      · rw [ih]; rfl
      · rw [ih]; rfl
      · rw [←hw, ih, stopped_nonempty]; simp

theorem total_and_functional (xs : List Segment) :
    ∃! ys, ys ∈ outputs initial xs := by
  rw [unique_output]
  exact ⟨devoice xs, by simp, by intro y hy; simpa using hy⟩

theorem nonfinal_unchanged (x y : Segment) (xs : List Segment) :
    devoice (x::y::xs) = x::devoice (y::xs) := by cases x <;> rfl

theorem last_segment (pre : List Segment) (x : Segment) :
    devoice (pre ++ [x]) = pre ++ [if x=d then t else x] := by
  induction pre with
  | nil => cases x <;> simp [devoice]
  | cons y ys ih =>
    cases ys with
    | nil => cases x <;> simp [devoice]
    | cons z zs => simpa [devoice] using congrArg (List.cons y) ih

theorem output_length (xs : List Segment) : (devoice xs).length = xs.length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases xs with
    | nil => cases x <;> rfl
    | cons y ys => simpa [devoice] using congrArg Nat.succ ih

theorem accepted_exactly_final_devoicing (pre : List Segment) (x : Segment)
    (ys : List Segment) :
    ys ∈ outputs initial (pre ++ [x]) ↔
      ys = pre ++ [if x=d then t else x] := by
  rw [unique_output, last_segment]
  simp

theorem published_tad : outputs initial [t,a,d] = [[t,a,t]] := by decide +kernel

theorem published_tada : outputs initial [t,a,d,a] = [[t,a,d,a]] := by decide +kernel

end Chapter08Automata

#print axioms Chapter08Automata.unique_output
#print axioms Chapter08Automata.accepted_exactly_final_devoicing
