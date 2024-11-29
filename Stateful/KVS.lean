/-
The most dumb key-value store
-/

import Lean.Exception

open Lean (MonadError)
open Std (HashMap)
open System (FilePath)


class KVS (m : Type → Type) where
  load  : FilePath     → m Unit
  store : FilePath     → m Unit
  get   : Nat          → m String
  set   : Nat → String → m Unit


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


-- IO

instance iokvs : KVS (StateT KV (ExceptT String IO)) where

  load path  := IO.FS.lines path >>= Array.mapM parseLine >>= set

  store path := do
    let s ← (KV.toString <$> get)
    IO.FS.writeFile path s

  get n      := get >>= KV.lookup n

  set k v    := modify (KV.set k v)


-- pure

abbrev FS := HashMap FilePath KV

-- set_option diagnostics true
-- set_option diagnostics.threshold 60

instance purekvs : KVS (StateT FS (StateT KV (Except String))) where

  load path  := do
    let fs ← getThe FS
    (fs.get? path).elim (throw "Missing file") set

  store path := do
    let kv ← getThe KV
    modifyThe FS fun fs => fs.insert path kv

  get n      := getThe KV >>= KV.lookup n

  set k v    := modifyThe KV (KV.set k v)


-- Lawful

class LawfulKVS (m : Type → Type) [Monad m] [KVS m] : Prop where

  set_get : ∀ k v, KVS.set k v >>= (fun _ => KVS.get k) = pure (f := m) v

  set_set : ∀ k v1 v2, KVS.set k v1 >>= (fun _ => KVS.set k v2) = KVS.set (m := m) k v2


  -- level up

  store_store : ∀ path, KVS.store path >>= (fun _ => KVS.store path) = KVS.store (m := m) path
