import Batteries.Data.Vector

open Batteries (Vector)
open Batteries.Vector


inductive StackOps (σ : Type u) : Nat → Nat → Type u → Type (u+1) where
  | push : σ  → StackOps σ  h    (h+1) PUnit
  | pop  :      StackOps σ (h+1)  h    σ
  | top  :      StackOps σ (h+1) (h+1) σ
  | pure : ty → StackOps σ  h     h    ty
  | bind :      StackOps σ  h1    h2   α
         → (α → StackOps σ  h2    h3   β)
         →      StackOps σ  h1    h3   β

#print Monad

-- instance (h1 h2 : Nat) : Monad (StackOps σ h1 h2) where
--   pure := .pure
--   bind := .bind


def runStackOp (s : Vector σ n) : StackOps σ n k α → α × Vector σ k
  | .push x => ⟨(), s.push x⟩
  | .pop    => ⟨s.back, s.pop⟩
  | .top    => ⟨s.back, s⟩
  | .pure x => ⟨x, s⟩
  | .bind op1 f => let ⟨x, s1⟩ := runStackOp s op1
      runStackOp s1 (f x)


def testAdd : StackOps Int 0 0 Int :=
  (StackOps.push 10).bind fun _ =>
  (StackOps.push 20).bind fun _ =>
  StackOps.pop.bind fun v1 =>
  StackOps.pop.bind fun v2 =>
  StackOps.pure (v1 + v2)

#eval runStackOp .empty testAdd

def onlyAdd : StackOps Int (n+2) n Int :=
  StackOps.pop.bind fun v1 =>
  StackOps.pop.bind fun v2 =>
  StackOps.pure (v1 + v2)

#eval runStackOp #v[20, 30] onlyAdd
#eval runStackOp #v[20, 30, 50] onlyAdd


-- Interactive Calculator

inductive Command where
  | push : Int → Command
  | top  :       Command
  | add  :       Command
  | quit :       Command

def parseCommand : String → Option Command
  | ""  => none
  | "." => some .top
  | "+" => some .add
  | "q" => some .quit
  | s   => .push <$> s.toInt?

-- IO

partial def icalc : IO Unit := do
  let sin  ← IO.getStdin
  let sout ← IO.getStdout
  let rec loop {n : Nat} (s : Vector Int n) : IO Unit := do
    let inp <- sin.getLine
    match parseCommand inp with
    | .none => sout.putStrLn "Unknown command"
    | .some .quit => pure ()
    | .some (.push x) => loop (s.push x)
    | .some .top  =>
      if h : 0 < s.size
      then
        have : n - 1 < n := by
          apply Nat.sub_one_lt
          simp [Vector.size] at h
          exact (Nat.ne_zero_iff_zero_lt.mpr h)
        let t := s[n - 1]
        sout.putStrLn (t.repr)
        loop s
      else
        sout.putStrLn "Empty stack"
        loop s
    | .some .add  =>
      if h: 1 < s.size
      then
        have : n - 1 < n := by
          apply Nat.sub_one_lt
          simp [Vector.size] at h
          simp [Nat.ne_zero_iff_zero_lt, Nat.lt_trans _ h]
        let b := s[n-1]
        let a := s[n-2]
        let sum := a + b
        sout.putStrLn sum.repr
        loop (s.pop.pop.push sum)
      else
        sout.putStrLn "Not enough arguments"
        loop s
  loop .empty


-- TODO

abbrev Command.stackType : Command → Type 1
  | .push _ => {h : Nat} → StackOps Int  h    (h+1) PUnit
  | .top    => {h : Nat} → StackOps Int (h+1) (h+1) Int
  | .add    => {h : Nat} → StackOps Int (h+2) h Int
  | .quit   => PUnit


def Command.toStackOps : (c : Command) → c.stackType
  | .push x => .push x
  | .top    => .top
  | .add    => onlyAdd
  | .quit   => PUnit.unit


-- TODO: Lawful stack

abbrev push_top_prog {h : Nat} (v : α) : StackOps α h (h+1) α := (StackOps.push v).bind (fun _ => .top)

theorem push_top : ∀ (s : Vector α h) (v : α), (runStackOp s (push_top_prog v)).fst = v := by
  sorry
