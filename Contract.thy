theory Contract
  imports Solidity
  keywords "contract" :: thy_decl
       and "constructor"
       and "cmethod"
       and "memory"
       and "param"
       and "calldata"
       and "invariant" :: thy_goal

begin
ML \<open>
  infix 1 |>|
  fun x |>| y = (x,y);
\<close>
ML \<open>
fun solidity_command trans command_keyword comment parse =
  Outer_Syntax.command command_keyword comment
    (parse >> (fn f => trans NONE (SOME ("Solidity",\<^here>)) f));
\<close>

ML \<open>
  structure Methods = Theory_Data
  (
    type T = term list Symtab.table
    val empty = Symtab.empty
    val merge = Symtab.merge (K true)
  )
  
  val mlookup = Symtab.lookup o Methods.get
  fun mupdate k v = Methods.map (Symtab.update (k, v))
\<close>

ML \<open>
  fun list_all ts t =
    let
      fun go (s, T) t = HOLogic.mk_all (s, T, t)
    in
      fold_rev go ts t
    end
\<close>

ML \<open>
  fun list_implies (t::ts) t' =
    let
      fun go t t' = HOLogic.mk_conj (t, t')
    in
      HOLogic.mk_imp ((fold go ts t), t')
    end
\<close>

ML \<open>
  fun apply_fresh_args f ctxt =
    f |> fastype_of
    |> binder_types
    |> map (pair "x")
    |> Variable.variant_frees ctxt [f]
    |> map Free
    |> curry list_comb f
\<close>

ML \<open>
  fun capitalizeFirst (str : string) =
      case str of
          "" => ""  (* Return an empty string if the input string is empty *)
        | s => Char.toString(Char.toUpper (String.sub (s, 0))) ^ String.substring (s, 1, size s - 1)

  fun decapitalizeFirst (str : string) =
      case str of
          "" => ""  (* Return an empty string if the input string is empty *)
        | s => Char.toString(Char.toLower (String.sub (s, 0))) ^ String.substring (s, 1, size s - 1)
\<close>

ML \<open>
  fun a_to_b (TFree("'a",["Utils.address"])) = TFree("'b",["Utils.address"])
    | a_to_b T = T;
\<close>

ML \<open>                                                  
  fun define_simple_datatype (dt_tyargs, dt_name) constructors =
    let
       val options = Plugin_Name.default_filter
       fun lift_c (tyargs, name) = (((Binding.empty, Binding.name name), map (fn t => (Binding.empty, t)) tyargs), NoSyn)
       val c_spec = map lift_c constructors
       val datatyp = ((map (fn ty => (NONE, ty)) dt_tyargs, dt_name), NoSyn)
       val dtspec =
          ((options,false),
           [(((datatyp, c_spec), (Binding.empty, Binding.empty, Binding.empty)), [])])
        
     in
       BNF_FP_Def_Sugar.co_datatypes BNF_Util.Least_FP BNF_LFP.construct_lfp dtspec
     end
\<close>

context Solidity
begin                       

ML \<open>
  fun mk_wordT b = \<^Type>\<open>word b\<close>
  fun mk_sumT (a, b) = \<^Type>\<open>sum a b\<close>;
  val stringT = \<^typ>\<open>String.literal\<close>

  val a = TFree("'a",["Utils.address"])
  val this = Free ("this", a)
  val exT = \<^typ>\<open>ex\<close>;
  val e = Free ("e", exT);
  val rvalueT = \<^Type>\<open>rvalue a\<close>;
  val stateT = \<^Type>\<open>state_ext a HOLogic.unitT\<close>
  val s = Free ("s", stateT)
  val s' = Free ("s'", stateT)
  val rT = mk_sumT (HOLogic.mk_prodT (rvalueT, stateT), HOLogic.mk_prodT (exT, stateT));
  val r = Free ("r", rT);
  val smonadT = \<^Type>\<open>state_monad rvalueT exT stateT\<close>;

  fun change_type (_,\<^sort>\<open>address\<close>) = a
    | change_type t = TFree t;
  fun change_types x = Term.map_types (fn t => Term.map_type_tfree change_type t) x;
  fun change_types2 (Free (n, _)) = Free (n, \<^Type>\<open>cdata a\<close>)
    | change_types2 _ = error "Only free variables allowed";

  fun mk_inv r P Q = \<^Const>\<open>Contract.inv a for r P Q\<close>
  fun mk_inv_state i = \<^Const>\<open>Contract.inv_state a for this i\<close>

  val effect = \<^Const>\<open>State_Monad.effect rvalueT exT stateT\<close>;
  val kdataT = \<^Type>\<open>State.kdata a\<close>
  val finit_map_T = \<^Type>\<open>Finite_Map.fmap stringT kdataT\<close>;

  fun mk_Bind x y = \<^Const>\<open>bind rvalueT exT stateT rvalueT for x \<open>\<^Const>\<open>K smonadT rvalueT for y\<close>\<close>\<close>;

  fun mk_init x y = \<^Const>\<open>Solidity.init a for x y\<close>;

  fun mk_minit x y = \<^Const>\<open>Solidity.minit a for x y\<close>;

  fun mk_cinit x y = \<^Const>\<open>Solidity.cinit a for x y\<close>;

  val mk_newStack = \<^Const>\<open>newStack a\<close>

  val mk_newMemory = \<^Const>\<open>newMemory a\<close>

  val mk_newCalldata = \<^Const>\<open>newCalldata a\<close>

  val init_balance = \<^Const>\<open>Solidity.Solidity.init_balance a for \<open>Free ("msg_value", mk_wordT \<^typ>\<open>256\<close>)\<close> this\<close>

  fun mk_contract_typ ctxt name_lc =
    let
      val full_name = Local_Theory.full_name ctxt (Binding.name name_lc)
    in
      Type (full_name, [a])
    end;

  fun get_free t =
    let
      val ts = Term.add_frees t []
    in
      if length ts = 1 then hd ts else error "error"
    end;

  fun mk_init_storage x y = \<^Const>\<open>Solidity.Contract.initStorage a for this x y\<close>

  fun constructor_name n = n ^ "_constructor";

  fun constructor_binding n p = Binding.make (constructor_name n, p);

  fun mono_binding n p = Binding.make (n ^ "_mono", p);

  fun change_types3 ctxt ((((name, parlist), memlist), cdlist), body) =
    let
      val parlist = map (apply2 (Syntax.read_term ctxt)) parlist
                 |> map (apsnd change_types);
      val memlist = map (apply2 (Syntax.read_term ctxt)) memlist
                 |> map (apsnd change_types2);
      val cdlist = map (apply2 (Syntax.read_term ctxt)) cdlist
                 |> map (apsnd change_types2);
    in
      ((((name, parlist), memlist), cdlist), body)
    end;

  let
    val specparser =
      let
        fun mk_contract ((name, variables), ((((constr_params, constr_memory), constr_calldata), constr_body), methods)) ctxt =
          let
            val methods = map (change_types3 ctxt) methods;

            fun mk_inits parlist body =
              let
                fun go (name, par) mon =
                  mk_init name par
                  |>| mon
                  |-> mk_Bind
              in
                fold_rev go parlist body
              end;

            fun mk_minits parlist body =
              let
                fun go (name, par) mon =
                  mk_minit name par
                  |>| mon
                  |-> mk_Bind
              in
                fold_rev go parlist body
              end;

            fun mk_cinits parlist body =
              let
                fun go (name, par) mon =
                  mk_cinit name par
                  |>| mon
                  |-> mk_Bind
              in
                fold_rev go parlist body
              end;

            val name_lc = decapitalizeFirst (Binding.name_of name);

            fun mk_constructor ctxt =
              let
                fun mk_init_storages body =
                  let
                    fun go (name, par) mon =
                      mk_init_storage name par
                      |>| mon
                      |-> mk_Bind
                    val member_term = map (apply2 (Syntax.read_term ctxt)) variables
                                   |> map (apsnd change_types);
                  in
                    fold_rev go member_term body
                  end;

                val parlist = map (apply2 (Syntax.read_term ctxt)) constr_params
                            |> map (apsnd change_types);
                val memlist = map (apply2 (Syntax.read_term ctxt)) constr_memory
                            |> map (apsnd change_types2);
                val cdlist = map (apply2 (Syntax.read_term ctxt)) constr_calldata
                            |> map (apsnd change_types2);
                val parlist_free = map (snd #> get_free #> Free) parlist |> rev;
                val memlist_free = map (snd #> get_free #> Free) memlist |> rev;
                val cdlist_free = map (snd #> get_free #> Free) cdlist |> rev
                val constr_name = constructor_binding name_lc (Binding.pos_of name);
                val constr_def_name = Thm.def_binding constr_name;
                val constr_body = Syntax.read_term ctxt constr_body
                             |> change_types
                             |> mk_minits memlist
                             |> mk_inits parlist
                             |> mk_Bind mk_newCalldata
                             |> mk_Bind mk_newMemory
                             |> mk_Bind mk_newStack
                             |> mk_init_storages
                             |> mk_Bind init_balance
                             |> fold lambda cdlist_free
                             |> fold lambda memlist_free
                             |> fold lambda parlist_free
              in
                ctxt |> Local_Theory.begin_nested |> snd
                     |> Local_Theory.define ((constr_name, NoSyn), ((constr_def_name, []), constr_body)) |> snd
                     |> Local_Theory.end_nested
              end
    
            fun mk_contract_datatype ctxt =
              let
                fun mk_constructor ((((name, parlist), memlist), cdlist), _) =
                  let
                    fun go (_, par) = map_atyps a_to_b (par |> get_free |> snd);
                    val parlist = map go (parlist @ memlist @ cdlist);
                  in
                    (parlist, capitalizeFirst (Binding.name_of name) ^ "_m")
                  end
                val constructors = map mk_constructor methods;
                val name_contract_datatype = Binding.make (name_lc, Binding.pos_of name);
              in  
                ctxt |> Local_Theory.begin_nested |> snd
                     |> define_simple_datatype ([(TFree("'b",["Utils.address"]), ["Utils.address"])], name_contract_datatype) constructors
                     |> Local_Theory.end_nested
              end

            fun mk_methods ctxt =
              let
                val contract = mk_contract_typ ctxt name_lc;
                fun mk_method ((((name, parlist), memlist), cdlist), body) ctxt =
                  let
                    val parlist_free = map (snd #> get_free #> Free) (parlist @ memlist @ cdlist)
                    val def_name = Thm.def_binding name
                    val def_body = Syntax.read_term ctxt body
                                  |> change_types
                                  |> mk_cinits cdlist
                                  |> mk_minits memlist
                                  |> mk_inits parlist
                                  |> mk_Bind mk_newCalldata
                                  |> mk_Bind mk_newMemory
                                  |> mk_Bind mk_newStack
                                  |> mk_Bind init_balance
                                  |> fold_rev lambda parlist_free
                                  |> lambda (Free ("call", \<^Type>\<open>fun contract smonadT\<close>))

                    fun mk_mono ((f, _), ctxt) =
                      let
                        val goal =
                          let
                            val sm_ord = \<^Const>\<open>sm_ord rvalueT exT stateT\<close>
                            val fun_sm_ord = \<^Const>\<open>fun_ord smonadT smonadT contract for sm_ord\<close>
                            val top = \<^Const>\<open>top \<^Type>\<open>set \<^Type>\<open>fun contract smonadT\<close>\<close>\<close>
                            val mono_sm = \<^Const>\<open>monotone_on \<^Type>\<open>fun contract smonadT\<close> smonadT for top fun_sm_ord sm_ord\<close>
                            val f_call = f $ Free ("call", \<^Type>\<open>fun contract smonadT\<close>)
                          in
                            list_comb (f_call, parlist_free)
                            |> lambda (Free ("call", \<^Type>\<open>fun contract smonadT\<close>))
                            |> curry (op $) mono_sm
                            |> HOLogic.mk_Trueprop
                          end
                        val plist_names = map (snd #> get_free #> fst) (parlist @ memlist @ cdlist)
                        val mono_tac =
                          rewrite_goal_tac ctxt [Proof_Context.get_thm ctxt (Binding.name_of def_name)]
                          THEN' (fn x => REPEAT (resolve_tac ctxt @{thms mono} x))
                        val thm = Goal.prove ctxt plist_names [] goal (K (mono_tac 1))
                        val mono_name = mono_binding (Binding.name_of def_name) (Binding.pos_of def_name);
                      in
                        Local_Theory.note ((mono_name, [Attrib.internal \<^here> (K (Named_Theorems.add "Partial_Function.partial_function_mono"))]), [thm]) ctxt |> snd
                      end
                  in
                    Local_Theory.define ((name, NoSyn), ((def_name, []), def_body)) ctxt
                    |> mk_mono
                  end
                in
                  ctxt |> Local_Theory.begin_nested |> snd
                       |> fold mk_method methods
                       |> Local_Theory.end_nested
                end
    
            fun mk_partial_function ctxt =
              let
                fun mkcase contract ((((name, parlist), memlist), cdlist), _) =
                  let
                    val t = Syntax.read_term ctxt (Binding.name_of name)
                    val t_call = t $ Free ("call", \<^Type>\<open>fun contract smonadT\<close>)
                    fun go (_, par) = par |> get_free |> snd;
                    val parlist = map go (parlist @ memlist @ cdlist);
                    val x = parlist ---> smonadT
                  in
                    (t_call, x)
                  end
                val contract = mk_contract_typ ctxt name_lc;
                val cases = map (mkcase contract) methods
                val case_t = Binding.name ("case_"^name_lc)
                              |> Binding.qualify false name_lc
                              |> Local_Theory.full_name ctxt
                              |> rpair (map snd cases ---> \<^Type>\<open>fun contract smonadT\<close>)
                              |> Const
                val x = Free ("x",contract)
                val lhs = (list_comb (case_t, map fst cases)) $ x
                val rhs = Free ("call", \<^Type>\<open>fun contract smonadT\<close>) $ x
                val vars = [(Binding.make ("call", \<^here>),NONE,NoSyn)]
                val mprop = \<^Const>\<open>HOL.eq smonadT for rhs lhs\<close>
                          |> HOLogic.mk_Trueprop
              in
                ctxt
                |> Local_Theory.begin_nested |> snd
                |> Partial_Function.add_partial_function "sm" vars (Binding.empty_atts,mprop) |> #2
                |> Local_Theory.end_nested
              end
    
            fun registerFunctions ctxt =
              let
                fun read_term t = Syntax.read_term ctxt (Binding.name_of (fst (fst (fst (fst t)))))
                fun update_table c t' = Local_Theory.background_theory (mupdate name_lc t') c
              in
                map read_term methods
                |> update_table ctxt
              end
          in
            ctxt |> mk_contract_datatype
                 |> mk_constructor
                 |> mk_methods
                 |> mk_partial_function
                 |> registerFunctions
          end

        val parameter_parser = Parse.term -- (Parse.$$$ ":" |-- Parse.term);
        val storage_list_parser = Scan.optional (Parse.$$$ "for" |-- Parse.!!! (Parse.and_list1 parameter_parser)) [];
        val parameter_list_parser = Scan.optional (Parse.$$$ "param" |-- Parse.!!! (Parse.and_list1 parameter_parser)) [];
        val memory_list_parser = Scan.optional (Parse.$$$ "memory" |-- Parse.!!! (Parse.and_list1 parameter_parser)) [];
        val calldata_list_parser = Scan.optional (Parse.$$$ "calldata" |-- Parse.!!! (Parse.and_list1 parameter_parser)) [];
        val body_parser = Parse.$$$ "where" |-- Parse.!!! Parse.term;
        val method_parser = Parse.$$$ "cmethod" |-- (Parse.binding -- parameter_list_parser -- memory_list_parser -- calldata_list_parser -- body_parser)
        val constructor_parser = Parse.$$$ "constructor" |-- (parameter_list_parser -- memory_list_parser -- calldata_list_parser -- body_parser)
        val contract_parser = (Parse.binding -- storage_list_parser) -- (constructor_parser -- (Parse.list method_parser))
      in
        contract_parser >> mk_contract
      end
  in
    solidity_command Toplevel.local_theory @{command_keyword "contract"} "creates a contract" specparser
  end
\<close>

ML \<open>
  let
    fun goal_prop (pname,((invariant, inverr), contract_name)) ctxt =
      let
        val name_lc = decapitalizeFirst (Binding.name_of contract_name);
        val constructor = constructor_name name_lc |> Syntax.read_term ctxt
        val inv = Syntax.read_term ctxt invariant
        val err = Syntax.read_term ctxt inverr
        val contract = mk_contract_typ ctxt name_lc;

        fun verify rules ctxt =
          let
            val cr::or = flat rules

            fun call_tac ctxt asm =
              let
                val ind_rule = Proof_Context.get_thm ctxt "call.raw_induct"
              in
                resolve_tac ctxt [ind_rule]
                THEN' Induct_Tacs.case_tac ctxt "x" [] NONE
                THEN' REPEAT o (resolve_tac ctxt or THEN_ALL_NEW force_tac ctxt)
                THEN' cut_facts_tac asm
                THEN' assume_tac ctxt
              end

            val nb = Binding.make (Binding.name_of pname^"_constructor_inv", Binding.pos_of pname)
            val ctxt' = Local_Theory.note ((nb, []), [cr]) ctxt |> snd

            val (_, ctxt'') = Variable.add_fixes ["x'", "s", "r"] ctxt'
            val asm = Syntax.read_prop ctxt'' ("effect (call x') s r")
            val conc = mk_inv_state inv $ s
                      |>| mk_inv r (mk_inv_state inv) (mk_inv_state err)
                      |> HOLogic.mk_imp
                      |> HOLogic.mk_Trueprop
            val thm = Goal.prove ctxt'' [] [asm] conc (fn {prems, context, ...} => call_tac context prems 1)
                    |> singleton (Proof_Context.export ctxt'' ctxt')
          in
            Local_Theory.note ((pname, []), [thm]) ctxt' |> snd
          end

        fun mkthms ctxt defn =
          let
            val call = Free (hd (Variable.variant_frees ctxt [] [("callx", \<^Type>\<open>fun contract smonadT\<close>)]))
            val defn_call = apply_fresh_args (defn $ call) ctxt

            val concl = HOLogic.mk_Trueprop (effect $ defn_call $ s $ r)
                    |>| HOLogic.mk_Trueprop (HOLogic.mk_imp (mk_inv_state inv $ s, mk_inv r (mk_inv_state inv) (mk_inv_state err)))
                    |> Logic.mk_implies

            val x = Free ("x", contract)
            val call_x = call $ x
            val prem = [effect $ call_x $ s $ r, mk_inv_state inv $ s]
                     |>| mk_inv r (mk_inv_state inv) (mk_inv_state err)
                     |-> list_implies
                     |> list_all [("s", stateT), ("r", rT)]
                     |> HOLogic.mk_Trueprop
                     |> Logic.all x

            val goal = Logic.mk_implies (prem, concl)
          in
            [(goal,[])]
          end

        fun mk_const_thm ctxt =
          let
            val const_term = apply_fresh_args constructor ctxt
          in
            HOLogic.mk_Trueprop (effect $ const_term $ s $ r)
            |>| HOLogic.mk_Trueprop (mk_inv r (mk_inv_state inv) (mk_inv_state err))
            |> Logic.mk_implies
          end
        val cons = mk_const_thm ctxt;

        val defns = Proof_Context.theory_of ctxt
                  |> Methods.get
                  |>| name_lc
                  |-> Symtab.lookup
  
        val thms = map (mkthms ctxt) (Option.valOf defns)
      in
        Proof.theorem NONE verify ([(cons, [])]::thms) ctxt
      end
    in
      solidity_command Toplevel.local_theory_to_proof @{command_keyword "invariant"}
      "initiates verification of invariant"
      (Parse.binding -- (Parse.$$$ ":" |-- ((Parse.term -- Parse.term) -- (Parse.$$$ "for" |-- Parse.binding))) >> goal_prop)
    end
  \<close>

end

end