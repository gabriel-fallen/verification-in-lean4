import Batteries.Data.Vector

open Batteries (Vector)
open Function (const)


abbrev PIN := Vector Nat 4

inductive ATMState where
  | ready
  | haveCard
  | session

inductive PINCheck where
  | succeded
  | failed

inductive ATMCmd : (α : Type) → ATMState → (α → ATMState) → Type 1 where
  | insertCard :       ATMCmd PUnit    .ready    (const PUnit .haveCard)
  | ejectCard  :       ATMCmd PUnit    _         (const PUnit .ready)
  | getPin     :       ATMCmd PIN      .haveCard (const PIN .haveCard)
  | checkPin   : PIN → ATMCmd PINCheck .haveCard (fun res => match res with
                                                  | .succeded => .session
                                                  | .failed   => .haveCard)
  | getBalance :       ATMCmd Nat      .session  (const Nat .session)
  | dispense   : Nat → ATMCmd PUnit    .session  (const PUnit .session)
  | pure       : (x : α) → ATMCmd α (state_fn x) state_fn
  | bind       :            ATMCmd α state1 state2_fn →
                 ((x : α) → ATMCmd β (state2_fn x) state3_fn) →
                 ATMCmd β state_1 state3_fn


def grabCache (amount : Nat) : ATMCmd PUnit .ready (const PUnit .ready) :=
  ATMCmd.insertCard.bind fun _ =>
  ATMCmd.getPin.bind fun pin =>
  (ATMCmd.checkPin pin).bind fun res =>
  match res with
  | .succeded => (ATMCmd.dispense amount).bind fun _ => .ejectCard
  | .failed   => .ejectCard

def grabSome (upto : Nat → Nat) : ATMCmd PUnit .ready (const PUnit .ready) :=
  ATMCmd.insertCard.bind fun _ =>
  ATMCmd.getPin.bind fun pin =>
  (ATMCmd.checkPin pin).bind fun res =>
  match res with
  | .succeded =>
    ATMCmd.getBalance.bind fun max => (ATMCmd.dispense $ upto max).bind fun _ => .ejectCard
  | .failed   => .ejectCard


def allOrNothing (want max : Nat) : Nat := if max < want then 0 else want

def allUpto (want max : Nat) : Nat := Nat.max want max

def grabAllOrNothing (amount : Nat) : ATMCmd PUnit .ready (const PUnit .ready) :=
  grabSome $ allOrNothing amount

def grabAllUpto (amount : Nat) : ATMCmd PUnit .ready (const PUnit .ready) :=
  grabSome $ allUpto amount
