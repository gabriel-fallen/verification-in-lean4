/-
The most dumb key-value store
-/

import Lean.Exception

open Lean (MonadError)
open System (FilePath)


class KVS (m : Type → Type) where
  load  : FilePath     → m Unit
  store : FilePath     → m Unit
  get   : Nat          → m String
  set   : Nat → String → m Unit


-- IO

-- Data structure to read/write and work with

abbrev KV := Array (Nat × String)


def parseLine [Monad m] [MonadExcept String m] (s : String) : m (Nat × String) :=
  let l := s.splitOn ";"
  if l.length < 2
  then throw "Malformed line in the file"
  else pure $ ⟨l[0]!.toNat!, l[1]!⟩ -- TODO: prove the indexing is safe

def KV.toString (kv : KV) : String :=
  kv.foldl (fun acc (n, s) => acc ++ s!"{n};{s}\n") ""

def KV.lookup [Monad m] [MonadExcept String m] (k : Nat) (kv : KV) : m String :=
  kv.find? (fun (n, _) => n == k) |> (Option.elim · (throw "Missing key") (fun (_, s) => pure s))

def KV.set (k : Nat) (v : String) (kv : KV) : KV :=
  kv.find? (fun (n, _) => n == k) |> (Option.elim · (kv.push ⟨k, v⟩) (fun _ => kv.set! k ⟨k, v⟩)) -- TODO: prove the indexing is safe

-- set_option diagnostics true
-- set_option diagnostics.threshold 60


instance : KVS (StateT KV (ExceptT String IO)) where

  load path  := IO.FS.lines path >>= Array.mapM parseLine >>= set

  store path := do
    let s ← (KV.toString <$> get)
    IO.FS.writeFile path s

  get n := get >>= KV.lookup n

  set k v := modify (KV.set k v)
