/-
Copyright (c) 2024 Amazon.com, Inc. or its affiliates. All Rights
Reserved.  Released under Apache 2.0 license as described in the file
LICENSE.
Author(s): Nathan Wetzler
-/

import Mathlib.Tactic.Sat.FromLRAT

-- ===================== Simple Target Theorems ======================

theorem dm_and_2 (a b : Prop) :
  ¬(a ∧ b) ↔ (¬a ∨ ¬b) :=
by
  rw [not_and_or]

theorem dm_and_3 (a b c : Prop) :
  ¬(a ∧ b ∧ c) ↔ (¬a ∨ ¬b ∨ ¬c) :=
by
  repeat rw [not_and_or]

-- Manual comparison of NNF of goal to FromLRAT result
theorem dm_and_4 (a b c d : Prop) :
  ¬(a ∧ b ∧ c ∧ d) ↔ (¬a ∨ ¬b ∨ ¬c ∨ ¬d) :=
by
  repeat (first
          | rw [iff_def]
          | rw [imp_iff_not_or]
          | rw [not_and_or]
          | rw [not_or]
          | rw [not_not]
          | rw [or_assoc]
          | rw [and_assoc]
          | rw [and_self]
          | rw [or_self_iff]
          )
  have lrat := (from_lrat "p cnf 4 5 1 0 2 0 3 0 4 0 -1 -2 -3 -4 0"
                          "6 0 1 2 3 4 5 0")
  specialize lrat a b c d
  simp [or_assoc] at lrat
  rw [or_rotate] ; rw [or_assoc] ; rw [or_assoc]
  assumption

-- ============================ Utilities ============================

def current_function (e : Lean.Expr) : Lean.Name :=
  match e with
  | .app n _ => current_function n
  | .const n _ => n
  | _ => .anonymous

def expr_walk (e : Lean.Expr) : String :=
  match e with
  | .app n a => (let ns := expr_walk n
                let as := expr_walk a
                s!"\napp(fn:{ns}\narg:{as})")
  | .const decl _ => s!"const:{decl}"
  | .forallE n t b _ => s!"forallE(name:{n}\ntype:{t}\nbody:{b})"
  | .fvar _ => s!"fvar:{e}"
  | _ => "other"

def literal_p (e : Lean.Expr) : Bool :=
  match e with
  | .fvar _ => true
  | .app (.const ``Not _) (.fvar _) => true
  | _ => false

def expr_clause_p (e : Lean.Expr) : Bool :=
  match e with
  | .app (.app (.const ``Or _) l) c => literal_p l ∧ expr_clause_p c
  | _ => literal_p e

def expr_cnf_p (e : Lean.Expr) : Bool :=
  match e with
  | .app (.app (.const ``And _) c) f => expr_clause_p c ∧ expr_cnf_p f
  | _ => expr_clause_p e

--  ==================== Proposition Formula Check ====================

def prop_app_names : List Lean.Name := [``And, ``Or, ``Not, ``Iff, ``Implies]
def bool_constant_names : List Lean.Name := [``Bool.true, ``Bool.false]
def prop_names : List Lean.Name := prop_app_names ++ bool_constant_names

def prop_type_p (e : Lean.Expr) : Bool :=
  match e with
  | .const n _ => n = ``Bool
  | .sort u => BEq.beq u .zero
  | _ => false

def prop_formula_p (lctx : Lean.LocalContext) (e : Lean.Expr) : Bool :=
  match e with
  | .app (.const ``Eq _) (.const ``Bool _) => true
  | .app n a => prop_formula_p lctx n ∧ prop_formula_p lctx a
  | .const n _ => List.elem n prop_names
  | .forallE _ t b _ =>
    (Lean.Expr.isArrow e ∧
     prop_formula_p lctx t ∧
     prop_formula_p lctx b)
  | .fvar fid =>
    (let decl := lctx.get! fid
     let t := decl.type
     prop_type_p t)
  | _ => false

-- =================== Negation Normal Form (NNF) ====================

def get_nnf_rw_name (e : Lean.Expr) : Option Lean.Name :=
  match e with
  | .app n a =>
    (let first := current_function n
     let second := current_function a
     let tactic :=
       (match first, second with
        | ``Iff, _ => some ``iff_def
        | ``Implies, _ => some ``imp_iff_not_or
        | ``Not, ``Not => some ``not_not
        | ``Not, ``And => some ``not_and_or
        | ``Not, ``Or => some ``not_or
        | ``And, _
        | ``Or, _ => 
          (Option.getD (get_nnf_rw_name n) (get_nnf_rw_name a))
        | _, _ => none)
     tactic)
  | .forallE _ _ _ _ =>
    (if Lean.Expr.isArrow e then some ``imp_iff_not_or else none)
  | _ => none

def exec_nnf_tactic (e : Lean.Expr) : Lean.Elab.Tactic.TacticM Bool :=
  let maybe_rw_name := get_nnf_rw_name e
  match maybe_rw_name with
  | some n =>
    Lean.Elab.Tactic.withMainContext do
      Lean.Elab.Tactic.rewriteTarget (Lean.mkIdent n) false
      pure true
  | none => pure false

partial def to_nnf : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    let goal <- Lean.Elab.Tactic.getMainGoal
    let goal_type <- goal.getType
    match <- exec_nnf_tactic goal_type with
    | false => Lean.Elab.Tactic.evalTactic (<- `(tactic| skip))
    | true => to_nnf

-- ==================== Tseitin Encoding Theorems ====================

theorem and_encode_cnf (a b x : Prop) :
  ((a ∧ b) = x) <-> (x ∨ ¬a ∨ ¬b) ∧ (¬x ∨ a) ∧ (¬x ∨ b) :=
by
  by_cases x <;> by_cases a <;> by_cases b <;> simp_all

theorem or_encode_cnf (a b x : Prop) :
  ((a ∨ b) = x) <-> (x ∨ ¬a) ∧ (x ∨ ¬b) ∧ (¬ x ∨ a ∨ b) :=
by
  by_cases x <;> by_cases a <;> by_cases b <;> simp_all

-- ===================== Tseitin Transformation ======================

def find_tseitin_expr (e : Lean.Expr) : Option Lean.Expr :=
  match e with
  | .app (.app (.const ``And _) a) b
  | .app (.app (.const ``Or  _) a) b =>
    (if (literal_p a ∧
         literal_p b) then
       some e
     else
       match find_tseitin_expr a with
       | none => find_tseitin_expr b
       | some e' => some e')
  | _ => none

def tseitin_generalize
  (varNum : Nat)
  : Lean.Elab.Tactic.TacticM (Option Lean.FVarId) :=
  Lean.Elab.Tactic.withMainContext do
    let goal_mvarid <- Lean.Elab.Tactic.getMainGoal
    let goal_type <- goal_mvarid.getType
    let maybe_te := find_tseitin_expr goal_type
    match maybe_te with
    | none => pure none
    | some te =>
      let varName := s!"x{varNum}"
      let hypName := s!"gx{varNum}"
      let (decl_fvarids, new_mvarid) <- (Lean.MVarId.generalize
                                          goal_mvarid
                                          #[{expr := te,
                                             xName? := varName,
                                             hName? := hypName}])
      Lean.Elab.Tactic.replaceMainGoal [new_mvarid]
      Lean.Elab.Tactic.withMainContext do
      let new_hyp_fvarid := decl_fvarids[1]!
      let new_hyp_decl <- Lean.FVarId.getDecl new_hyp_fvarid
      let new_hyp_name := new_hyp_decl.userName
      match current_function te with
      | ``And => (Lean.Elab.Tactic.rewriteLocalDecl
                   (Lean.mkIdent ``and_encode_cnf) false new_hyp_fvarid)
      | ``Or => (Lean.Elab.Tactic.rewriteLocalDecl
                  (Lean.mkIdent ``or_encode_cnf) false new_hyp_fvarid)
      | _ => (Lean.Meta.throwTacticEx
               `tseitin_generalize goal_mvarid s!"Unknown function {te}")
      Lean.Elab.Tactic.evalTactic (<- `(tactic| repeat (rw [not_not] at *)))
      Lean.Elab.Tactic.withMainContext do
        let new_hyp_decl <- Lean.Meta.getLocalDeclFromUserName new_hyp_name
        let new_hyp_fvarid := new_hyp_decl.fvarId
        pure (some new_hyp_fvarid)
    
partial def tseitin_transform
  (varNum : Nat := 1)
  : Lean.Elab.Tactic.TacticM (List Lean.FVarId) :=
  Lean.Elab.Tactic.withMainContext do
    match <- tseitin_generalize varNum with
    | none => Lean.Elab.Tactic.evalTactic (<- `(tactic| skip))
              pure []
    | some fvarid => let rest <- tseitin_transform (varNum + 1)
                     pure (fvarid :: rest)

-- ================== Conjunctive Normal Form (CNF) ==================

def conjoin_clauses
  (hyp_fvarids : List Lean.FVarId)
  : Lean.Elab.Tactic.TacticM Unit :=
  Lean.Elab.Tactic.withMainContext do
    match hyp_fvarids with
    | [] => Lean.Elab.Tactic.evalTactic (<- `(tactic| skip))
    | hyp_fvarid :: rest =>
      let hyp_decl <- Lean.FVarId.getDecl hyp_fvarid
      let hyp_name := hyp_decl.userName
      (Lean.Elab.Tactic.evalTactic
        (<- `(tactic| have $(Lean.mkIdent "g"):ident :=
                        And.intro $(Lean.mkIdent "g"):ident
                                  $(Lean.mkIdent hyp_name))))
      conjoin_clauses rest

-- =========================== DIMACS CNF ============================

abbrev VarMap := (Nat × (Std.HashMap Lean.Name Nat))

def cnf_variable_to_string
  (fvarid : Lean.FVarId)
  (lctx : Lean.LocalContext)
  (varMap : VarMap) : VarMap × String :=
  let (next, map) := varMap
  let decl := lctx.get! fvarid
  let name := decl.userName
  match Std.HashMap.find? map name with
  | some n => (varMap, s!"{n}")
  | none => (((next + 1), (Std.HashMap.insert map name next)), s!"{next}")

def cnf_literal_to_string
  (e : Lean.Expr)
  (lctx : Lean.LocalContext)
  (varMap : VarMap) : VarMap × String :=
  match e with
  | .fvar id => cnf_variable_to_string id lctx varMap
  | .app (.const ``Not _) (.fvar id) =>
    let (vm, s) := cnf_variable_to_string id lctx varMap
    (vm, "-" ++ s)
  | _ => (varMap, "")

def cnf_clause_to_string
  (e : Lean.Expr)
  (lctx : Lean.LocalContext)
  (varMap : VarMap) : VarMap × String :=
  match e with
  | .app (.app (.const ``Or _) l) c => 
    let (vm1, ls) := cnf_literal_to_string l lctx varMap
    let (vm2, cs) := cnf_clause_to_string c lctx vm1
    (vm2, ls ++ " " ++ cs)
  | _ =>
    let (vm1, ls) := cnf_literal_to_string e lctx varMap
    (vm1, ls ++ " 0\n")

def cnf_formula_to_string
  (e : Lean.Expr)
  (lctx : Lean.LocalContext)
  (varMap : VarMap) : VarMap × String × Nat :=
  match e with
  | .app (.app (.const ``And _) c) f => 
    let (vm1, cs) := cnf_clause_to_string c lctx varMap
    let (vm2, fs, cn) := cnf_formula_to_string f lctx vm1
    (vm2, cs ++ fs, cn + 1)
  | _ =>
    let (vm1, cs) := cnf_clause_to_string e lctx varMap
    (vm1, cs, 1)

def to_dimacs_cnf
  (varMap : VarMap)
  (fs : String)
  (clauseNum : Nat) : String :=
  let (nextVar, _) := varMap
  s!"p cnf {(nextVar - 1)} {clauseNum}\n{fs}"

-- ==================== Reverse Variable Mapping =====================

def varMap_to_specialize_args (varMap : VarMap) : Lean.Term :=
  let (_, hm) := varMap
  let hma := hm.toArray
  let hmas := hma.qsort (fun (_, y1) (_, y2) => y1 < y2)
  let vars := hmas.map (fun (x, _) => x)
  let vars_syntax := vars.map (fun x => Lean.mkIdent x)
  Lean.Syntax.mkApp (Lean.mkIdent "lrat") vars_syntax

-- =========================== SAT Tactic ============================

elab "sat_tactic" : tactic =>
  Lean.Elab.Tactic.withMainContext do
    -- If not a propositional/boolean formula, then quit
    let goal_mvarid <- Lean.Elab.Tactic.getMainGoal
    let goal_type <- goal_mvarid.getType
    let lctx <- Lean.getLCtx
    if ¬(prop_formula_p lctx goal_type) then return
    -- Convert propositional formula to Negation Normal Form
    to_nnf
    -- Perform Tseitin transform and save hypothesis FVarIds
    let hyp_fvarids <- tseitin_transform
    -- Move remaining formula to local context (for positive form)
    Lean.Elab.Tactic.evalTactic (<- `(tactic| apply by_contradiction))
    Lean.Elab.Tactic.evalTactic
      (<- `(tactic| intro $(Lean.mkIdent "g"):ident))
    -- Conjoin remaining formula with all Tseitin clauses
    conjoin_clauses hyp_fvarids
    -- Flatten CNF formula
    Lean.Elab.Tactic.evalTactic
      (<- `(tactic| repeat rw [and_assoc] at $(Lean.mkIdent "g"):ident))
    -- Convert hypothesis "g" into DIMACS CNF string
    Lean.Elab.Tactic.withMainContext do
      let g_hyp_decl <- Lean.Meta.getLocalDeclFromUserName "g"
      let g_hyp_expr := g_hyp_decl.type
      let lctx <- Lean.getLCtx
      let (varMap : VarMap) := (1, Std.mkHashMap)
      let (vm1, fs, cn) := cnf_formula_to_string g_hyp_expr lctx varMap
      -- Add DIMACS header to formula
      let dimacs_cnf := to_dimacs_cnf vm1 fs cn
      -- Write DIMACS CNF file
      IO.FS.withFile "sat_tactic.cnf" IO.FS.Mode.write fun fd => 
        fd.putStrLn dimacs_cnf
      -- Call solver of dimacs file
      let _ <- IO.Process.output {cmd := "cadical",
                                  args := #["--binary=false",
                                            "--lrat=true",
                                            "sat_tactic.cnf",
                                            "sat_tactic.lrat"]}
      -- TODO: inspect output for SAT or UNKNOWN
      -- Invoke FromLRAT on CNF formula and LRAT proof
      Lean.Elab.Tactic.evalTactic
        (<- `(tactic| have $(Lean.mkIdent "lrat"):ident :=
                        -- TODO: Need to do better with file paths
                        from_lrat (include_str "../sat_tactic.cnf")
                                  (include_str "../sat_tactic.lrat")))
      -- Coerce goal "g" and FromLRAT result into matching NNF form
      Lean.Elab.Tactic.evalTactic
        (<- `(tactic| simp [or_assoc] at $(Lean.mkIdent "lrat"):ident))
      Lean.Elab.Tactic.evalTactic
        (<- `(tactic| revert $(Lean.mkIdent "g"):ident ;
                      simp [imp_iff_not_or, not_and_or, not_or]))
      -- Map FromLRAT variables to original names
      Lean.Elab.Tactic.evalTactic
        (<- `(tactic| specialize $(varMap_to_specialize_args vm1)))
      -- Finally apply FromLRAT hypothesis to goal
      Lean.Elab.Tactic.evalTactic
        (<- `(tactic| exact $(Lean.mkIdent "lrat"):ident))
  
-- ============================ Examples =============================

theorem test_dm_and_2 (a b : Prop) :
  ¬(a ∧ b) ↔ (¬a ∨ ¬b) :=
by
  sat_tactic
