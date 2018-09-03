import category.positive
import data.coinductive.basic
import data.coinductive.eq
import logic.nursery
import tactic.inductive_decl
import tactic.recursive_def

namespace tactic
open lean.parser interactive interactive.types
open tactic.interactive (generalize cases_arg_p)
local postfix `?`:9000 := optional

meta def co_cases (pat : parse cases_arg_p) (ns : parse with_ident_list) : tactic unit :=
do ls ← local_context,
   e ← to_expr pat.2,
   ls ← ls.mfilter (λ h, do
     t ← infer_type h,
     return $ e.occurs t),
   n ← revert_lst ls,
   generalize e `p,
   p ← intro1,
   t ← target,
   lam ← lambdas [p] t,
   refine ``(@cofix.cases _ _ %%lam _ %%p),
   clear p,
   when (e.is_local_constant ∧ pat.1.is_none) (clear e),
   intro_lst $ ns.take 2,
   intron (2 - ns.length),
   target >>= head_beta >>= change,
   intron n

run_cmd add_interactive [`co_cases]

open expr list

meta def mk_head_t (decl : inductive_type) : tactic inductive_type :=
do let n := decl.name,
   let head_n := (n <.> "head_t"),
   let sig_c  : expr := const n decl.u_params,
   cs ← decl.ctors.mmap $ λ d : type_cnstr,
   do { vs' ← d.args.mfilter $ λ v,
          do { t ← infer_type v, pure $ ¬ sig_c.occurs t },
        pure { name := d.name.update_prefix head_n, args := vs', .. d } },
   let decl' := { name := head_n, ctors := cs, .. decl },
   decl' <$ mk_inductive decl'

meta def mk_child_t (decl : inductive_type) : tactic inductive_type :=
do let n := decl.name,
   let mk_constr : name → expr := λ n', (const (n'.update_prefix $ n <.> "head_t") decl.u_params).mk_app decl.params,
   let head_t : expr := const (n <.> "head_t") decl.u_params,
   let child_n := (n <.> "child_t"),
   let sig_c  : expr := const n decl.u_params,
   cs ← decl.ctors.mmap $ λ d : type_cnstr,
   do { (rec,vs') ← d.args.mpartition $ λ v,
          do { t ← infer_type v, pure $ sig_c.occurs t },
        rec.enum.mmap $ λ ⟨i,r⟩, do
          (args',r') ← infer_type r >>= unpi,
          pure { name := (d.name.append_after i).update_prefix $ n <.> "child_t",
                 args := vs' ++ args', result := [(mk_constr d.name).mk_app vs'], .. d } },
   idx ← mk_local_def `i $ head_t.mk_app $ decl.params ++ decl.idx,
   let decl' := { name := child_n, idx := decl.idx ++ [idx], ctors := cs.join, .. decl },
   decl' <$ mk_inductive decl'

meta def child_ctor_base_name : name → name
| (name.mk_string s _) := name.mk_string (string.intercalate "_" (s.split (= '_')).init) name.anonymous
| n := n

meta def mk_discr_of (decl child_dec : inductive_type) (ctor : type_cnstr) (sig_c : expr) : tactic unit :=
do let rec_n := ctor.name.update_prefix $ decl.mk_name "child_t" <.> "rec",
   let u := fresh_univ decl.u_names,
   let u_params := decl.u_params,
   let u_params' := level.param u :: u_params,
   C ← mk_local' `C binder_info.implicit (sort $ level.param u),
   (rec,vs') ← ctor.args.mpartition $ λ v,
          do { t ← infer_type v, pure $ sig_c.occurs t },
   let head_n := (decl.mk_name "head_t"),
   let head_t : expr := const head_n u_params,
   let child_t : expr := const (decl.mk_name "child_t") u_params,
   let head_ctor : expr := const (ctor.name.update_prefix head_n) u_params,
   fs ← rec.enum.mmap $ λ ⟨i,e⟩,
     do { as ← infer_type e >>= unpi,
          pis as.1 C >>= mk_local_def `f },
   vs' ← vs'.mmap renew,
   let j := head_ctor.mk_app $ decl.params ++ vs',
   x ← mk_local_def `x $ child_t.mk_app $ decl.params ++ decl.idx ++ [j],
   let vs := (decl.params ++ vs' ++ [C] ++ fs ++ [x]),
   p ← pis vs C,
   (_,pr) ← solve_aux C $
   do { i ← mk_local_def `i $ head_t.mk_app $ child_dec.params ++ decl.idx,
        y ← mk_local_def `y $ child_t.mk_app $ child_dec.params ++ decl.idx ++ [i],
        hij ← mk_app `eq [i,j] >>= mk_local_def `hij,
        C' ← pis [hij] C >>= lambdas (decl.idx ++ [i,y]),
        vs ← inductive_type.mk_cases_on' { idx := decl.idx ++ [j], .. child_dec }
          C' x $ λ c args,
          do { h ← intro `h,
               let no_conf := @const tt (head_n <.> "no_confusion") u_params',
               (v0,v1) ← infer_type h >>= match_eq,
               unify_app no_conf (decl.params ++ decl.idx ++ [C,v0,v1,h]) >>= apply,
               done <|> do
                 ls ← intros,
                 (h :: nil).mmap' clear,
                 () <$ revert_lst (args.drop vs'.length) },
        gs ← get_goals,
        mzip_with' unify vs fs,
        gs.for_each (λ g, set_goals [g] >> reflexivity) },
   pr ← instantiate_mvars pr >>= lambdas vs,
   add_decl $ mk_definition rec_n (u :: decl.u_names) p pr,
   pure ()

meta def mk_branch_discr (decl head_t child_t : inductive_type) : tactic unit :=
do let sig_c  : expr := const decl.name decl.u_params,
   decl.ctors.mmap' $ λ c, mk_discr_of decl child_t c sig_c

meta def mk_constr (decl : inductive_type) : tactic (list expr) :=
do decl.ctors.mmap $ λ c, do
     t ← c.type decl,
     (arg,_) ← unpi t,
     let F := (decl.mk_const "F").mk_app (arg.take decl.params.length),
     let n := c.name.update_prefix (decl.name <.> "F"),
     fix ← mk_mapp ``cofix' [F,none],
     let d := (expr.const n decl.u_params).mk_app (arg.take decl.params.length ++ fix :: arg.drop decl.params.length),
     d ← mk_mapp ``cofix.fold [F,none,d] >>= lambdas arg,
     add_decl $ mk_definition c.name decl.u_names t d,
     pure $ expr.const c.name decl.u_params

meta def mk_cases_eqns (decl : inductive_type) (cases_n u : name) (vs₀ cs : list expr) : tactic unit :=
do let discr := (expr.const cases_n (level.param u :: decl.u_params)).mk_app vs₀,
   mzip_with' (λ (c : type_cnstr) (f : ℕ × expr),
     do { let e := (expr.const c.name decl.u_params).mk_app (decl.params ++ c.args),
          t ← mk_app `eq [discr e,f.2.mk_app c.args] >>= pis (vs₀ ++ c.args),
          let n := (decl.name <.> "cases" <.> "equations" <.> "_eqn").append_after f.1,
          updateex_env $ λ e, pure $ environment.add_namespace e $ decl.name <.> "cases",
          (_,d) ← solve_aux t $ do {
            intros,
            dunfold_target [cases_n,c.name],
            applyc ``eq_mp_heq,
            mk_const ``cofix.unfold_fold >>= rewrite_target,
            applyc ``heq.rfl },
          let d := t.mk_sorry,
          add_decl $ declaration.thm n (u :: decl.u_names) t (pure d),
          simp_attr.pseudo_eqn.set n () tt,
          set_basic_attribute `simp n })
     decl.ctors cs.enum

meta def mk_cases_def (decl : inductive_type) (u : name) (coind_t C x : expr) (vs cs : list expr) : tactic expr :=
do (_,d) ← solve_aux (C x) $ do {
     x' ← mk_app ``cofix.unfold [x],
     vs ← cs.mmap (λ c, mk_mvar),
     let F := (expr.const (decl.mk_name "F" <.> "cases_on") (level.param u :: decl.u_params)).mk_app (decl.params ++ [coind_t]),
     v ← infer_type x' >>= mk_local_def `v,
     v' ← mk_app ``cofix.fold [v],
     C' ← lambdas [v] (C v'),
     e ← unify_app F (C' :: x' :: vs),
     eq_p ← mk_app ``cofix.fold_unfold [x] >>= mk_congr_arg C,
     e ← mk_eq_mp eq_p e,
     exact e,
     mzip_with (λ v c, set_goals [v] >> exact c) vs cs,
     done },
   instantiate_mvars d >>= lambdas vs >>= instantiate_mvars

meta def mk_cases (decl : inductive_type) : tactic unit :=
do let coind_t := (expr.const decl.name decl.u_params).mk_app decl.params,
   let u := fresh_univ decl.u_names,
   x ← mk_local_def `x coind_t,
   C ← pis [x] (expr.sort $ level.param u) >>= mk_local' `C binder_info.implicit,
   cs ← decl.ctors.mmap $ λ c,
     do { let t := C $ (expr.const c.name decl.u_params).mk_app $ decl.params ++ c.args,
          pis c.args t >>= mk_local_def (c.name.update_prefix name.anonymous) },
   let vs := (decl.params.map to_implicit ++ [C] ++ cs ++ [x]),
   t ← pis vs (C x),
   d ← mk_cases_def decl u coind_t C x vs cs,
   let cases_n := (decl.name <.> "cases"),
   add_decl $ mk_definition cases_n (u :: decl.u_names) t d,
   mk_cases_eqns decl cases_n u vs.init cs,
   let vs' := (decl.params.map to_implicit ++ [C,x] ++ cs),
   t ← pis vs' (C x),
   let c := (expr.const (decl.name <.> "cases") $ level.param u :: decl.u_params ).mk_app vs,
   d ← lambdas vs' c,
   add_decl $ mk_definition (decl.name <.> "cases_on") (u :: decl.u_names) t d

meta def mk_pos_functor (decl : inductive_type) : tactic unit :=
do let sig_c : expr := const decl.name decl.u_params,
   let n := decl.mk_name "F",
   X ← mk_local_def `x decl.type,
   cs ← decl.ctors.mmap $ λ c,
     do { args' ← c.args.mmap $ λ v,
                do { local_const uniq pp bi t ← pure v,
                     let t' := t.replace_all (λ e, e.get_app_fn = sig_c) X,
                     pure $ @local_const tt uniq pp bi t' },
          return $ { name := c.name.update_prefix n, args := args' , .. c } },
   let decl' := { name := n,
                  params := decl.params ++ [ X ],
                  u_names := decl.u_names,
                  ctors   := cs, .. decl },
   mk_inductive decl'

meta def mk_to_rep_to_fun (decl : inductive_type) (fn_t rep_t X : expr) : tactic expr :=
do let n := decl.name <.> "to_rep" <.> "to_fun",
   t ← pis (decl.params ++ decl.idx ++ [X]) (fn_t.imp rep_t),
   let d := t.mk_sorry,
   add_decl' $ mk_definition n decl.u_names t d

meta def mk_to_rep_inv_fun (decl : inductive_type) (fn_t rep_t X : expr) : tactic expr :=
do let n := decl.name <.> "to_rep" <.> "inv_fun",
   t ← pis (decl.params ++ decl.idx ++ [X]) (rep_t.imp fn_t),
   let d := t.mk_sorry,
   add_decl' $ mk_definition n decl.u_names t d

meta def mk_to_rep (decl : inductive_type) : tactic expr :=
do X ← mk_local_def `x decl.type,
   ch_t ← mk_mapp (decl.mk_name "child_t") $ (decl.params ++ decl.idx).map some,
   rep_t ← mk_app ``rep [ch_t,X],
   fn_t ← mk_app (decl.mk_name "F") (decl.params ++ decl.idx ++ [X]),
   to  ← mk_to_rep_to_fun  decl fn_t rep_t X,
   inv ← mk_to_rep_inv_fun decl fn_t rep_t X,
   let vs := (decl.params ++ decl.idx ++ [X]),
   t  ← mk_app `equiv [fn_t,rep_t],
   t' ← pis vs t,
   (_,d) ← solve_aux t $ do {
     refine ``( { to_fun := %%(to.mk_app vs),
                  inv_fun := %%(inv.mk_app vs), .. } )
       ; admit },
   d ← instantiate_mvars d >>= lambdas vs,
   add_decl' $ mk_definition (decl.mk_name "to_rep") decl.u_names t' d

meta def mk_positive_inst (decl : inductive_type) : tactic unit :=
do d ← mk_to_rep decl,
   let vs := (decl.params ++ decl.idx),
   let F := (decl.mk_const "F").mk_app vs,
   let hd_t := (decl.mk_const "head_t").mk_app vs,
   let ch_t := (decl.mk_const "child_t").mk_app vs,
   t  ← mk_app ``positive [F],
   t' ← pis vs t,
   (_,d) ← solve_aux t $ do {
     refine
     ``( { head_t  := %%hd_t,
           child_t := %%ch_t,
           to_rep  := %%(d.mk_app vs) } ) },
   d ← instantiate_mvars d >>= lambdas vs,
   let n := (decl.mk_name "F" <.> "positive"),
   add_decl $ mk_definition n decl.u_names t' d,
   set_basic_attribute `instance n tt

meta def mk_cofix (decl : inductive_type) : tactic unit :=
do let child_n := decl.mk_const "F",
   let child_t := child_n.mk_app decl.params,
   co ← mk_mapp ``cofix' [child_t,none],
   d  ← lambdas decl.params co,
   t ← infer_type d,
   add_decl $ mk_definition decl.name decl.u_names t d

meta def mk_temp (n : name) (t : expr) : expr :=
expr.local_const n n binder_info.default t

meta def mk_bisimulation_pred (decl : inductive_type) : tactic unit :=
do let params := decl.params.map to_implicit,
   let d : expr := (const decl.name decl.u_params).mk_app params,
   let sim_n := decl.name <.> "bisim",
   v ← mk_local_def `x d,
   t ← pis ([v,v]) `(Prop),
   let nm := mk_temp sim_n t,
   updateex_env $ λ e, pure $ e.add_namespace sim_n,
   let lc := @const tt sim_n decl.u_params,
   cs ← decl.ctors.mmap $ λ c,
     do { σ ← c.args.mmap $ λ e,
             do { if d.occurs e.local_type then do
                     x₀ ← prod.mk e.local_uniq_name <$> mk_local_def (e.local_pp_name.append_after 0) e.local_type,
                     x₁ ← prod.mk e.local_uniq_name <$> mk_local_def (e.local_pp_name.append_after 1) e.local_type,
                     (args,t) ← mk_local_pis e.local_type,
                     let t := lc.mk_app $ params ++ [x₀.2.mk_app args,x₁.2.mk_app args],
                     v ← pis args t >>= mk_local_def `h,
                     pure (x₀,x₁,[x₀.2,x₁.2,v])
                  else pure ((e.local_pp_name,e),(e.local_pp_name,e),[e]) },
          let (σ₀,σ₁) := σ.unzip,
          let (σ₁,hs) := σ₁.unzip,
          let result₀ := c.result.map $ λ (e : expr), e.instantiate_locals σ₀,
          let result₁ := c.result.map $ λ (e : expr), e.instantiate_locals σ₁,
          rt₀ ← mk_mapp c.name $ (params ++ σ₀.map prod.snd).map some,
          rt₁ ← mk_mapp c.name $ (params ++ σ₁.map prod.snd).map some,
          let t := lc.mk_app $ params ++ [rt₀,rt₁],
          t' ← pis hs.join t,
          instantiate_mvars $ mk_temp (c.name.update_prefix sim_n) t' },
   t ← pis [v] (lc.mk_app $ params ++ [v,v]),
   let c := mk_temp (sim_n <.> "rfl") t,
   add_coinductive_predicate decl.u_names params [(nm,c::cs)],
   v' ← mk_local_def `x' d,
   p ← mk_app `eq [v,v'],
   t ← pis (params ++ [v,v']) $ (lc.mk_app $ params ++ [v,v']).imp p,
   let d := t.mk_sorry,
   add_decl $ declaration.thm (decl.name <.> "bisim_sound") decl.u_names t (pure d)

@[user_command]
meta def coinductive_def (meta_info : decl_meta_info) (_ : parse $ tk "codata") : lean.parser unit :=
do decl ← inductive_decl.parse meta_info,
   decl ← inductive_type.of_decl decl,
   updateex_env $ λ e, pure $ e.add_namespace decl.name,
   head_t  ← trace_error $ mk_head_t  decl,
   child_t ← trace_error $ mk_child_t decl,
   _       ← trace_error $ mk_branch_discr decl head_t child_t,
   _       ← trace_error $ mk_pos_functor   decl,
   _       ← trace_error $ mk_positive_inst decl,
   _       ← trace_error $ mk_cofix  decl,
   _       ← trace_error $ mk_constr decl,
   _       ← trace_error $ mk_cases  decl,
   _       ← trace_error $ mk_no_confusion_type decl,
   _       ← trace_error $ mk_no_confusion decl,
   _       ← trace_error $ mk_bisimulation_pred decl,
   add_meta_definition (decl.name <.> "_info") [] `(inductive_type) (reflect decl),
   pure ()

meta def get_coinductive_info (n : name) : tactic inductive_type :=
mk_const (n <.> "_info") >>= eval_expr' _

open expr

meta def to_functor_ctor_name (decl : inductive_type) : expr → expr
| (const n ls) := const (n.update_prefix $ n.get_prefix <.> "F") ls
| e := e

meta def to_functor_ctor (decl : inductive_type) (x e : expr) : expr :=
e.replace $ λ a i,
do let fn := a.get_app_fn,
   guard (decl.is_constructor fn.const_name),
   let args := a.get_app_args,
   let (params,rest) := args.split_at decl.params.length,
   let e := (const decl.name fn.const_params).mk_app params,
   pure $ (to_functor_ctor_name decl fn).mk_app $ params ++ x :: rest


namespace interactive
open interactive interactive.types expr lean.parser
local postfix `?`:9001 := optional
local postfix *:9001 := many

meta def bisimulation
  (revert : parse $ (tk "generalizing" *> ident*)?) : tactic unit :=
do `(%%x = %%y) ← target,
   t ← infer_type y,
   let n := t.get_app_fn.const_name,
   applyc $ n <.> "bisim_sound",
   coinduction (n <.> "bisim" <.> "corec_on") revert

end interactive

end tactic

namespace examples

@[vm_monitor]
meta def my_mon : vm_monitor (nat × option name) :=
{ init := (0, none),
  step := λ fn,
  do fn' ← vm.curr_fn,
     n' ← vm.call_stack_size,
     when (fn ≠ (n',some fn') ∧ ¬ (`interaction_monad.monad).is_prefix_of fn') $
       vm.trace $ (string.join $ list.repeat "| " n') ++ to_string fn',
     pure (n',fn') }

codata computation (α : Type*)
| pure (x : α) : computation
| think : computation → computation

end examples

namespace tactic

open lean.parser interactive interactive.types
open tactic.interactive (generalize cases_arg_p)
local postfix `?`:9000 := optional
open binder_info expr

meta def mk_corecursive_eqn (args : list expr) (decl' : inductive_type) : recursive_def → tactic unit
| decl@{ term := def_term.single v, .. } :=
do let args := decl.args,
   let c : expr := const decl.name decl.u_params,
   let lhs := c.mk_app args,
   rhs ← head_beta $ v.mk_app args,
   t ← infer_type rhs,
   f ← mk_const ``eq,
   t ← unify_app f [t,lhs,rhs] >>= instantiate_mvars,
   let t := (c.mk_app args).instantiate_local decl.rec_fn.local_uniq_name t,
   t ← pis args t >>= instantiate_mvars,
   -- (_,d) ← solve_aux t $ do {
   --   intros,
   --   dunfold_target $ decl.name :: decl'.ctors.map type_cnstr.name,
   --   mk_const ``cofix.fold_apply_corec' >>= rewrite_target,
   --   reflexivity,
   --   done },
   -- d ← instantiate_mvars d,
   let d := t.mk_sorry,
   add_decl $ declaration.thm (decl.name.append_suffix "_def") t.collect_univ_params t (pure d),
   pure ()

meta def mk_corecursive_def : recursive_def → tactic unit
| d@{ term := def_term.single v, .. } :=
do (_,hd) ← unpi d.type,
   let coind_n := hd.get_app_fn.const_name,
   decl ← get_coinductive_info coind_n,
   g ← mk_meta_var d.type,
   set_goals [g],
   vs ← intron' d.args.length,
   v ← head_beta (v.mk_app vs) >>= instantiate_mvars,
   refine ``(cofix.corec' _ punit.star),
   [x,f,a] ← intron' 3,
   let v' := (v.abstract d.rec_fn).instantiate_var (f a),
   let ctor := to_functor_ctor decl x v',
   right,
   v ← target >>= mk_meta_var,
   exact ctor,
   set_goals [v],
   t ← instantiate_mvars d.type,
   v' ← instantiate_mvars g,
   add_decl $ mk_definition d.name d.u_names t v',
   mk_corecursive_eqn vs decl d

@[user_command]
meta def corecursive_def (meta_info : decl_meta_info) (_ : parse $ tk "codef") : lean.parser unit :=
do d ← recursive_def.parse,
   meta_info.attrs.apply d.name,
   trace_error $ mk_corecursive_def d,
   pure ()

end tactic

-- set_option debugger false

-- set_option debugger true

-- #print prefix tree.child_t.rec

namespace examples

codef diverge {α : Sort*} : examples.computation α :=
computation.think diverge

def computation.bind {α β} (x : examples.computation α) (f : α → examples.computation β) : examples.computation β :=
cofix.corec'
(λ X rec x, @examples.computation.cases _ (λ _, examples.computation β ⊕ examples.computation.F β X)
  (λ i, sum.inl $ f i)
  (λ a, sum.inr $ examples.computation.F.think $ rec a) x)
x

instance : monad examples.computation :=
{ pure := @examples.computation.pure,
  bind := @examples.computation.bind }

lemma computation.bind.equations.eqn_1 {α β} (x : α) (f : α → computation β) :
  computation.pure x >>= f = f x :=
begin
  dsimp [(>>=),computation.bind],
  rw cofix.fold_apply_corec',
  simp [cofix.fold'] with pseudo_eqn,
end

lemma computation.bind.equations.eqn_2 {α β} (x : computation α) (f : α → computation β) :
  computation.think x >>= f = computation.think (x >>= f) :=
begin
  dsimp [(>>=),computation.bind],
  rw cofix.fold_apply_corec',
  simp [cofix.fold'] with pseudo_eqn, refl
end

open examples.computation (bisim)
     -- examples.computation.bisim (cases_on)

@[refl]
lemma bisim_refl {α} (x : examples.computation α) :
  bisim x x :=
begin
  coinduction examples.computation.bisim.corec_on,
  left, refl,
end

lemma head_think {α} (x : computation α) :
  cofix.head (computation.think x) = computation.head_t.think :=
begin
  dunfold cofix.head computation.think cofix.fold,
  simp, admit
end

lemma children_think {α} (x : computation α) (i : child_t (cofix.head (computation.think x))) :
  cofix.children (computation.think x) i = x :=
begin
  dunfold cofix.head computation.think cofix.fold,
  simp, admit
end

-- lemma bisim_sound {α} (x y : examples.computation α)
--   (h : bisim x y) : x = y :=
-- begin
--   apply cofix.eq_of_bisim bisim; try { assumption },
--   dunfold cofix.is_bisimulation, introv h,
--   apply computation.bisim.cases_on h; intros,
--   { split, refl,
--     introv h, subst h, },
--   { split, refl,
--     dunfold computation.pure,
--     intros, cases a, refl, },
--   { split, simp [head_think],
--     intros, simp [children_think,*], }
-- end

lemma bind_pure {α} (x : examples.computation α) :
  x >>= pure = x :=
begin
  bisimulation generalizing x,
  apply computation.cases_on w; intros;
  simp [computation.bind.equations.eqn_1,computation.bind.equations.eqn_2],
  { right, left, existsi [_,rfl], refl },
  { right, right, existsi [_,_,rfl,rfl], refl }
end

lemma pure_bind {α β} (x : α) (f : α → examples.computation β) :
  pure x >>= f = f x :=
by simp [pure,computation.bind.equations.eqn_1,computation.bind.equations.eqn_2]

lemma bind_assoc {α β γ}
  (x : examples.computation α)
  (f : α → examples.computation β)
  (g : β → examples.computation γ) :
  x >>= f >>= g = x >>= λ i, f i >>= g :=
begin
  bisimulation generalizing x,
  apply computation.cases_on w; intros;
  simp [computation.bind.equations.eqn_1,computation.bind.equations.eqn_2],
  { right, right, constructor_matching* [_ ∧ _,Exists _]; try { refl } }
end

instance : is_lawful_monad examples.computation :=
begin
  refine { .. }; intros,
  apply bind_pure,
  apply pure_bind,
  apply bind_assoc,
end
-- #check diverge_def

-- codef bind {α} (x : computation α) : computation α := think bind

-- def computation.F.rep.to_fun (α x) (y : computation.F α x) : rep (computation.child_t α) x :=
-- @computation.F.cases_on _
-- _ (λ _, rep (computation.child_t α) x) y
-- (λ a, rep.mk (computation.head_t.pure _ a)
--              (computation.child_t.rec.pure _ _) )
-- (λ a, rep.mk (computation.head_t.think _)
--              (computation.child_t.rec.think _ a))

-- def computation.F.rep.inv_fun (α x : Type*) : rep (computation.child_t α) x → computation.F α x :=
-- @sigma.rec _ _ (λ _, computation.F α x) (λ a,
-- @computation.head_t.cases_on _ (λ a, (computation.child_t α a → x) → computation.F α x) a
-- (λ i f, computation.F.pure _ _ i)
-- (λ (f : computation.child_t α (computation.head_t.think _) → x), computation.F.think _ _ (f $ computation.child_t.think_0 _)))

-- def computation.to_rep (α x) : computation.F α x ≃ rep (computation.child_t α) x :=
-- begin
--  refine { to_fun := computation.F.rep.to_fun α x,
--           inv_fun := computation.F.rep.inv_fun α x,
--           .. };
--  simp [ computation.F.rep.to_fun,computation.F.rep.inv_fun ]; intro x,
--  { apply computation.F.cases_on x; intros; refl, } ,
--  { apply sigma.cases_on x, intros,
--    revert snd, apply computation.head_t.cases_on fst; intros;
--    dsimp [computation.F.rep.to_fun,rep.mk];
--    dunfold computation.F.cases_on computation.head_t.cases_on, ext;
--    simp, ext, admit,
--    ext; simp,
--    ext,
--    induction x_1 using examples.computation.child_t.rec,
--    apply computation.child_t.cases_on x_1,
--    -- refl,
--  }
-- end

end examples

set_option debugger false

codata tree (α : Type*)
| leaf : α → tree
| node : α → (unsigned → tree) → (α → ℕ → tree) → tree

codata get_m (α : Type*)
| fail : get_m
| pure : α → get_m
| read : (unsigned → unsigned → get_m) → get_m

universes u

def get_m' (α) := cofix (get_m.child_t α)

-- inductive get_m (α : Type*)
-- | fail {} : get_m
-- | pure : α → get_m
-- | read : (unsigned → unsigned → get_m' α) → get_m

-- open get_m

-- def get_m.to_get_m' {α} : get_m α → get_m' α
-- | get_m.fail := cofix.mk (head_t.fail α) (get_m.child_t.rec.fail α)
-- | (get_m.pure x) := cofix.mk (head_t.pure _ x) (get_m.child_t.rec.pure _ _)
-- | (get_m.read f) := cofix.mk (get_m.head_t.read α) (get_m.child_t.rec.read α f)

-- def get_m.of_get_m' {α} : get_m' α → get_m α :=
-- cofix.cases $ λ i,
-- @get_m.head_t.rec  _ (λ a, (get_m.child_t _ a → get_m' α) → get_m α)
-- (λ f, get_m.fail)
-- (λ a f, get_m.pure a)
-- (λ f, get_m.read $ λ j k, f $ child_t.read_0 _ j k) i

-- instance {α} : has_coe (get_m α) (get_m' α) := ⟨ get_m.to_get_m' ⟩
-- instance {α} : has_coe (get_m' α) (get_m α) := ⟨ get_m.of_get_m' ⟩
