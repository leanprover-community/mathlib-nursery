
import tactic.nursery

namespace tactic
open expr

meta structure type_cnstr :=
(name : name)
(args : list expr)
(result : list expr)

meta structure inductive_type :=
(name : name)
(u_names : list _root_.name)
(params : list expr)
(idx : list expr)
(type : expr)
(ctors : list type_cnstr)

meta def inductive_type.mk_const (decl : inductive_type) (n : string) : expr :=
const (decl.name <.> n) $ decl.u_names.map level.param

meta def inductive_type.mk_name (decl : inductive_type) (n : string) : name :=
decl.name <.> n

meta def mk_cases_on (decl : inductive_type) : tactic unit :=
do u ← get_unused_name "u",
   let idx := decl.idx,
   n ← mk_app decl.name (decl.params ++ idx) >>= mk_local_def `n,
   C ← pis (idx ++ [n]) (sort $ level.param u) >>= mk_local_def `C,
   cases ← decl.ctors.mmap $ λ c,
     do { let ctor : expr := const c.name $ decl.u_names.map level.param,
          cn ← get_unused_name "c",
          n ← mk_mapp c.name $ (decl.params ++ c.args).map some,
          pis c.args (C.mk_app $ c.result ++ [n]) >>= mk_local_def cn },
   t ← pis ((decl.params ++ [C] ++ idx).map to_implicit ++ [n] ++ cases) (C.mk_app (idx ++ [n])),
   p ← mk_mapp (decl.name <.> "rec") $ (decl.params ++ [C] ++ cases ++ idx ++ [n]).map some,
   p ← lambdas (decl.params ++ [C] ++ idx ++ [n] ++ cases) p,
   d ← instantiate_mvars p,
   add_decl $ mk_definition (decl.name <.> "cases_on") (u :: decl.u_names) t d,
   return ()

meta def inductive_type.mk_cases_on (decl : inductive_type) (C e : expr) (f : name → list expr → tactic expr) : tactic expr :=
do let cases_on_n := decl.mk_name "cases_on",
   cases_on ← mk_const cases_on_n,
   cs ← decl.ctors.mmap $ λ c,
     do { f c.name c.args >>= lambdas c.args },
   unify_app cases_on (decl.params ++ [C] ++ decl.idx ++ [e] ++ cs)

meta def inductive_type.mk_cases_on' (decl : inductive_type) (C e : expr) (f : name → list expr → tactic unit) : tactic expr :=
do let cases_on_n := decl.mk_name "cases_on",
   cases_on ← mk_const cases_on_n,
   cs ← decl.ctors.mmap $ λ c, mk_mvar,
   gs ← get_goals,
   unify_app cases_on (decl.params ++ [C] ++ decl.idx ++ [e] ++ cs) <*
     mzip_with' (λ g (c : type_cnstr),
       do set_goals [g],
          intro_lst (c.args.map expr.local_pp_name) >>= f c.name) cs decl.ctors <*
     set_goals gs

meta def mk_no_confusion_type (decl : inductive_type) : tactic unit :=
do let t := (const decl.name $ decl.u_names.map level.param).mk_app $ decl.params ++ decl.idx,
   u ← get_unused_name `u,
   let cases_on_n := decl.mk_name "cases_on",
   cases_on ← mk_const cases_on_n,
   v1 ← mk_local_def `v1 t,
   v2 ← mk_local_def `v2 t,
   P  ← mk_local_def `P (expr.sort $ level.param u),
   C ← lambdas (decl.idx ++ [v1]) (sort $ level.param u),
   e ← decl.mk_cases_on C v1 $ λ c args,
     do { decl.mk_cases_on C v2 $ λ c' args',
          if c = c' then do
            hs ← mzip_with (λ x y,
              mk_app `eq [x,y] >>= mk_local_def `h)
              args args',
            h ← pis hs P,
            pure $ h.imp P
          else pure P },
   let vs := (decl.params ++ decl.idx ++ [P,v1,v2]),
   e ← lambdas vs e,
   p ← pis vs (sort $ level.param u),
   infer_type e >>= unify p,
   e ← instantiate_mvars e,
   add_decl $ mk_definition (decl.mk_name "no_confusion_type") (u :: decl.u_names) p e

-- #check @eq.rec

-- @[reducible]
-- protected def get_m.head_t_.no_confusion : Π {α : Type u_1} {P : Sort l} {v1 v2 : head_t_ α}, v1 = v2 → get_m.head_t_.no_confusion_type P v1 v2 :=
-- λ {α : Type u_1} {P : Sort l} {v1 v2 : head_t_ α} (h12 : v1 = v2),
--   eq.rec
--     (λ (h11 : v1 = v1),
--        get_m.head_t_.cases_on v1 (λ (a : P), a) (λ (a : α) (a_1 : a = a → P), a_1 _) (λ (a : P), a))
--     h12
--     h12


meta def mk_no_confusion (decl : inductive_type) : tactic unit :=
do let t := (const decl.name $ decl.u_names.map level.param).mk_app $ decl.params ++ decl.idx,
   u ← get_unused_name `u,
   v1 ← mk_local_def `v1 t,
   v2 ← mk_local_def `v2 t,
   P  ← mk_local_def `P (expr.sort $ level.param u),
   type ← mk_const (decl.mk_name "no_confusion_type"),
   Heq ← mk_app `eq [v1,v2] >>= mk_local_def `Heq,
   let vs := decl.params ++ decl.idx ++ [P,v1,v2,Heq],
   p ← unify_app type (decl.params ++ decl.idx ++ [P,v1,v2]),
   (_,pr) ← solve_aux p $
     do { intros,
          dunfold_target [decl.mk_name "no_confusion_type"],
          tgt ← target,
          cases_on ← mk_const ``eq.rec,
          C ← pis [Heq] tgt >>= lambdas ([v2]),
          t ← infer_type v1,
          g ← mk_mvar,
          unify_app cases_on ([t,v1,C,g,v2,Heq,Heq]) >>= exact,
          set_goals [g],
          intro1,
          tgt ← target,
          C ← lambdas (decl.idx ++ [v1]) tgt,
          cases_on ← mk_const (decl.mk_name "cases_on"),
          e ← decl.mk_cases_on' C v1 $ λ _ _,
            do { dunfold_target [decl.mk_name "cases_on"],
                 h ← intro `h, () <$ apply h; reflexivity },
          exact e },
   p ← pis vs p,
   p ← instantiate_mvars p,
   pr ← instantiate_mvars pr,
   pr ← lambdas vs pr,
   add_decl $ mk_definition (decl.mk_name "no_confusion") (u :: decl.u_names) p pr,
   pure ()

meta def mk_inductive : inductive_type → tactic unit
| decl@{ u_names := u_names, params := params, ctors := ctors, .. } :=
do env ← get_env,
   let n := decl.name,
   sig_t ← pis (decl.params ++ decl.idx) decl.type,
   let sig_c  : expr := const n (u_names.map level.param),
   cs ← ctors.mmap $ λ ⟨cn,vs,r⟩,
   do { t ← tactic.pis (params ++ vs) $ sig_c.mk_app $ params ++ r,
        pure (cn.update_prefix n,t) },
   env ← env.add_inductive n u_names params.length sig_t cs ff,
   set_env env,
   mk_cases_on decl,
   mk_no_confusion_type decl,
   mk_no_confusion decl

open interactive

meta def inductive_type.of_decl (decl : inductive_decl) : tactic inductive_type :=
do d ← decl.decls.nth 0,
   (idx,t) ← infer_type  d.sig >>= unpi,
   cs ← d.intros.mmap $ λ d : expr,
   do { t ← infer_type d,
        (vs,t) ← unpi t,
        pure { type_cnstr .
               name := d.local_pp_name,
               args := vs,
               result := t.get_app_args.drop $ decl.params.length } },
   pure { name := d.sig.local_pp_name,
          u_names := decl.u_names,
          params := decl.params,
          idx := idx, type := t,
          ctors := cs }

end tactic
