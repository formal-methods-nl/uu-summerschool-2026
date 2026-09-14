import Mathlib
import UuSummerschool2026.Projects.AlgComp.AlgComp

open Lean Elab Command Meta

partial def collectExpr (e : Expr) : MetaM Unit := do
  match e with
  | .proj idx s b =>
    IO.println s!"  PROJ idx={idx}"
    collectExpr b
  | .app f a =>
    collectExpr f
    collectExpr a
  | .const n _ => IO.println s!"  CONST {n}"
  | .fvar _ => IO.println s!"  FVAR"
  | .mvar _ => IO.println s!"  MVAR"
  | .lam n d b _ =>
    IO.println s!"  LAM {n}"
    collectExpr d
    collectExpr b
  | .forallE n d b _ =>
    IO.println s!"  FORALL {n}"
  | .letE n _ v b _ =>
    IO.println s!"  LET {n}"
    collectExpr v
    collectExpr b
  | .mdata _ b => collectExpr b
  | _ => IO.println s!"  OTHER: {e.ctorName}"

partial def peelLambdas : Expr → Expr
  | .lam _ _ body _ => peelLambdas body
  | e => e

partial def collectApps : Expr → MetaM (Array Name)
  | .app f a => do
    let r1 ← collectApps f
    let r2 ← collectApps a
    return r1 ++ r2
  | .const n _ => return #[n]
  | .lam _ _ b _ => collectApps b
  | .letE _ _ v b _ => do
    let r1 ← collectApps v
    let r2 ← collectApps b
    return r1 ++ r2
  | .mdata _ b => collectApps b
  | .proj _ _ b => collectApps b
  | _ => return #[]

#eval show MetaM Unit from do
  let defn ← getConstInfoDefn ``slow_reverse._f
  let apps ← collectApps defn.value
  IO.println s!"slow_reverse._f consts: {apps}"

#eval show MetaM Unit from do
  let defn ← getConstInfoDefn ``fast_reverse_acc._f
  let apps ← collectApps defn.value
  IO.println s!"fast_reverse_acc._f consts: {apps}"

#eval show MetaM Unit from do
  IO.println "=== slow_reverse._f body ==="
  let defn ← getConstInfoDefn ``slow_reverse._f
  collectExpr defn.value

#eval show MetaM Unit from do
  IO.println "=== fast_reverse_acc._f body ==="
  let defn ← getConstInfoDefn ``fast_reverse_acc._f
  collectExpr defn.value
