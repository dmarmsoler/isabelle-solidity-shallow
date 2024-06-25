theory Solidity
imports State_Monad State
begin

datatype ('a::address) rvalue =
  Storage id "('a::address) valtype list" |
  Memory location |
  Calldata id "('a::address) valtype list" |
  Value (vt: "('a::address) valtype") |
  Empty

definition kdbool where
  "kdbool = Value \<circ> Bool"

definition kdSint where
  "kdSint \<equiv> Value \<circ> Sint"

definition kdAddress where
  "kdAddress = Value \<circ> Address"

fun lift_value_unary::"(('a::address) valtype \<Rightarrow> ('a::address) valtype option) \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) rvalue option" where
  "lift_value_unary op (rvalue.Value v) = op v \<bind> Some \<circ> rvalue.Value"
| "lift_value_unary op _ = None"

definition kdnot::"('a::address) rvalue \<Rightarrow> ('a::address) rvalue option" where
  "kdnot = lift_value_unary vtnot"

fun lift_value_binary::"(('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option) \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) rvalue option" where
  "lift_value_binary op (rvalue.Value l) (rvalue.Value r) = op l r \<bind> Some \<circ> rvalue.Value"
| "lift_value_binary op _ _ = None"

definition kdequals where
  "kdequals = lift_value_binary vtequals"

definition kdless where
  "kdless = lift_value_binary vtless"

definition kdand where
  "kdand = lift_value_binary vtand"

definition kdor where
  "kdor = lift_value_binary vtor"

definition kdplus where
  "kdplus = lift_value_binary vtplus"

definition kdplus_safe where
  "kdplus_safe = lift_value_binary vtplus_safe"

definition kdminus where
  "kdminus = lift_value_binary vtminus"

definition kdminus_safe where
  "kdminus_safe = lift_value_binary vtminus_safe"

definition kdmult where
  "kdmult = lift_value_binary vtmult"

definition kdmod where
  "kdmod = lift_value_binary vtmod"

type_synonym 'a expression_monad = "('a rvalue, ex, 'a state) state_monad"

definition newStack::"'a::address expression_monad" where
  "newStack = update (\<lambda>s. (Empty, s\<lparr>Stack:=fmempty\<rparr>))"

definition newMemory::"'a::address expression_monad" where
  "newMemory = update (\<lambda>s. (Empty, s\<lparr>Memory:=[]\<rparr>))"

definition newCalldata::"'a::address expression_monad" where
  "newCalldata = update (\<lambda>s. (Empty, s\<lparr>Calldata:=fmempty\<rparr>))"

fun the_value where
  "the_value (rvalue.Value x) = Some x"
| "the_value _ = None"

primrec lfold :: "('a::address) expression_monad list \<Rightarrow> (('a::address) valtype list, ex,('a::address) state) state_monad"
  where
    "lfold [] = return []"
  | "lfold (m#ms) =
      do {
        l \<leftarrow> m;
        l' \<leftarrow> option Err (\<lambda>_. the_value l);
        ls \<leftarrow> lfold ms;
        return (l' # ls)
      }"

locale Keccak256 =
  fixes keccak256::"('a::address) rvalue \<Rightarrow> ('a::address) rvalue"
  assumes "\<And>x y. keccak256 x = keccak256 y \<Longrightarrow> x = y"
begin

definition keccak256_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "keccak256_monad m = 
    do {
      v \<leftarrow> m;
      return (keccak256 v)
    }"

end

locale Contract =
  fixes this :: "'a::address" (*address of executing contract*)

begin

definition storage_update:: "id \<Rightarrow> ('a::address) sdata \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "storage_update i d s = s\<lparr>Storage := (state.Storage s) (this := (state.Storage s this) (i := d))\<rparr>"

abbreviation balance_update:: "nat \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "balance_update \<equiv> balances_update this"

definition inv:: "'a rvalue \<times> ('a::address) state + ex \<times> ('a::address) state \<Rightarrow> (('a::address) state \<Rightarrow> bool) \<Rightarrow> (('a::address) state \<Rightarrow> bool) \<Rightarrow> bool" where
  "inv r P Q \<equiv> (case r of Inl a \<Rightarrow> P (snd a)
                        | Inr a \<Rightarrow> Q (snd a))"

definition inv_state:: "((id \<Rightarrow> ('a::address) sdata) \<times> nat \<Rightarrow> bool) \<Rightarrow> ('a::address) state \<Rightarrow> bool"
  where "inv_state i s = i (state.Storage s this, state.Balances s this)"

end

section \<open>Expressions\<close>

subsection \<open>Constants\<close>

definition bool_monad where
  "bool_monad = return \<circ> kdbool"

definition true_monad::"('a::address) expression_monad" where
  "true_monad = bool_monad True"

definition false_monad::"('a::address) expression_monad" where
  "false_monad = bool_monad False"

definition sint_monad where
  "sint_monad = return \<circ> kdSint"

definition address_monad where
  "address_monad = return \<circ> kdAddress"

definition (in Contract) this_monad where
  "this_monad = address_monad this"

subsection \<open>Unary Operations\<close>

definition lift_unary_monad ::"(('a::address) rvalue \<Rightarrow> ('a::address) rvalue option) \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "lift_unary_monad op lm = 
    do {
      lv \<leftarrow> lm;
      val \<leftarrow> option Err (K (op lv));
      return val
    }"

definition not_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "not_monad = lift_unary_monad kdnot"

subsection \<open>Binary Operations\<close>

definition lift_op_monad::"(('a::address) rvalue \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) rvalue option) \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "lift_op_monad op lm rm = 
    do {
      lv \<leftarrow> lm;
      rv \<leftarrow> rm;
      val \<leftarrow> option Err (K (op lv rv));
      return val
    }"

lemma lift_op_monad_simp1:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = Exception (e, s'')"
    shows "execute (lift_op_monad op lm rm) s = Exception (e, s'')"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

lemma lift_op_monad_simp2:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = NT"
    shows "execute (lift_op_monad op lm rm) s = NT"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

lemma lift_op_monad_simp3:
  assumes "execute lm s = Exception (e, s')"
    shows "execute (lift_op_monad op lm rm) s = Exception (e, s')"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

lemma lift_op_monad_simp4:
  assumes "execute lm s = NT"
    shows "execute (lift_op_monad op lm rm) s = NT"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

lemma lift_op_monad_simp5:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = Normal (rv, s'')"
    shows "execute (lift_op_monad op lm rm) s = execute (option Err (K (op lv rv))) s''"
  unfolding lift_op_monad_def by (simp add: execute_simps assms)

definition equals_monad where
  "equals_monad = lift_op_monad kdequals"

lemma equals_monad_simp1[execute_simps]:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = Exception (e, s'')"
    shows "execute (equals_monad lm rm) s = Exception (e, s'')"
  unfolding equals_monad_def by (rule lift_op_monad_simp1[OF assms])

lemma equals_monad_simp2[execute_simps]:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = NT"
    shows "execute (equals_monad lm rm) s = NT"
  unfolding equals_monad_def by (rule lift_op_monad_simp2[OF assms])

lemma equals_monad_simp3[execute_simps]:
  assumes "execute lm s = Exception (e, s')"
    shows "execute (equals_monad lm rm) s = Exception (e, s')"
  unfolding equals_monad_def by (rule lift_op_monad_simp3[OF assms])

lemma equals_monad_simp4[execute_simps]:
  assumes "execute lm s = NT"
    shows "execute (equals_monad lm rm) s = NT"
  unfolding equals_monad_def by (rule lift_op_monad_simp4[OF assms])

lemma equals_monad_simp5[execute_simps]:
  assumes "execute lm s = Normal (lv, s')"
      and "execute rm s' = Normal (rv, s'')"
    shows "execute (equals_monad lm rm) s = execute (option Err (K (kdequals lv rv))) s''"
  unfolding equals_monad_def by (rule lift_op_monad_simp5[OF assms])

definition less_monad where
  "less_monad = lift_op_monad kdless"

definition and_monad where
  "and_monad = lift_op_monad kdand"

definition or_monad where
  "or_monad = lift_op_monad kdor"

definition plus_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "plus_monad = lift_op_monad kdplus"

definition plus_monad_safe::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "plus_monad_safe = lift_op_monad kdplus_safe"

definition minus_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "minus_monad = lift_op_monad kdminus"

definition minus_monad_safe::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "minus_monad_safe = lift_op_monad kdminus_safe"

definition mult_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "mult_monad = lift_op_monad kdmult"

definition mod_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "mod_monad = lift_op_monad kdmod"

subsection \<open>Require\<close>

definition require_monad::"('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "require_monad em = 
    do {
      e \<leftarrow> em;
      if e = kdbool True then return Empty else throw Err
    }"

subsection \<open>Store Lookups\<close>

definition (in Contract) storeLookup::"id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad" where
  "storeLookup i es =
    do {
      is \<leftarrow> lfold es;
      sd \<leftarrow> option Err (\<lambda>s. slookup is (state.Storage s this i));
      if sdata.is_Value sd then return (rvalue.Value (sdata.vt sd)) else return (rvalue.Storage i is)
    }"

definition (in Contract) storeArrayLength::"id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad" where
  "storeArrayLength i es =
    do {
      is \<leftarrow> lfold es;
      sd \<leftarrow> option Err (\<lambda>s. slookup is (state.Storage s this i));
      storage_check sd
        (K (throw Err))
        (\<lambda>sa. return (rvalue.Value (Sint (of_nat (length (sdata.ar sd))))))
        (K (throw Err))
    }"

section \<open>Statements\<close>

definition skip_monad:: "('a rvalue, ex, ('a::address) state) state_monad" where
"skip_monad = return Empty"

subsection \<open>Conditionals\<close>

definition cond_monad:: "('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
"cond_monad bm mt mf = 
  do {
    b \<leftarrow> equals_monad bm true_monad;
    if b = kdbool True then mt else if b = kdbool False then mf else throw Err
  }"

lemma execute_cond_monad_normal_E:
  assumes "execute (cond_monad bm mt mf) s = Normal (x, s')"
  obtains (1) s'' where "execute (equals_monad bm true_monad) s = Normal (kdbool True, s'')" and "execute mt s'' = Normal (x, s')"
        | (2) s'' where "execute (equals_monad bm true_monad) s = Normal (kdbool False, s'')" and "execute mf s'' = Normal (x, s')"
  using assms unfolding cond_monad_def
  by (cases "execute (equals_monad bm true_monad) s") (auto simp add: execute_simps split:if_split_asm)

lemma execute_cond_monad_exception_E:
  assumes "execute (cond_monad bm mt mf) s = Exception (x, s')"
  obtains (1) "execute (equals_monad bm true_monad) s = Exception (x, s')"
        | (2) s'' where "execute (equals_monad bm true_monad) s = Normal (kdbool True, s'')" and "execute mt s'' = Exception (x, s')"
        | (3) s'' where "execute (equals_monad bm true_monad) s = Normal (kdbool False, s'')" and "execute mf s'' = Exception (x, s')"
        | (4) a where "execute (equals_monad bm true_monad) s = Normal (a, s')" and "a \<noteq> kdbool True \<and> a \<noteq> kdbool False \<and> x = Err"
  using assms unfolding cond_monad_def
  by (cases "execute (equals_monad bm true_monad) s") (auto simp add: execute_simps split:if_split_asm)

lemma execute_cond_monad_simp1[execute_simps]:
  assumes "execute (equals_monad bm true_monad) s = Normal (kdbool True, s')"
  shows "execute (cond_monad bm mt mf) s = execute mt s'"
  unfolding cond_monad_def by (simp add: execute_simps assms)

lemma execute_cond_monad_simp2[execute_simps]:
  assumes "execute (equals_monad bm true_monad) s = Normal (kdbool False, s')"
  shows "execute (cond_monad bm mt mf) s = execute mf s'"
  unfolding cond_monad_def by (simp add: execute_simps assms kdbool_def)

lemma execute_cond_monad_simp3[execute_simps]:
  assumes "execute (equals_monad bm true_monad) s = Exception (e, s')"
  shows "execute (cond_monad bm mt mf) s = Exception (e, s')"
  unfolding cond_monad_def by (simp add: execute_simps assms)

lemma execute_cond_monad_simp4[execute_simps]:
  assumes "execute (equals_monad bm true_monad) s = NT"
  shows "execute (cond_monad bm mt mf) s = NT"
  unfolding cond_monad_def by (simp add: execute_simps assms)

subsection \<open>Assignments\<close>

definition my_update_monad:: "(('a::address) state \<Rightarrow> 'b) \<Rightarrow> (('c \<Rightarrow> 'd) \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state) \<Rightarrow> ('b \<Rightarrow> 'd option) \<Rightarrow> 'a expression_monad" where
  "my_update_monad s u f = option Err (\<lambda>s'. f (s s')) \<bind> modify \<circ> u \<circ> K \<bind> K (return Empty)"

definition memory_update_monad:: "(('a::address) memory \<Rightarrow> ('a::address) memory option) \<Rightarrow> 'a expression_monad" where
  "memory_update_monad = my_update_monad state.Memory Memory_update"

definition calldata_update_monad where
  "calldata_update_monad xs is cd p = option Err (\<lambda>s. state.Calldata s $$ p \<bind> updateCalldata (xs @ is) cd) \<bind> modify \<circ> (calldata_update p) \<bind> K (return Empty)"

definition (in Contract) storage_update_monad where
  "storage_update_monad xs is sd p = option Err (\<lambda>s. updateStore (xs @ is) sd (state.Storage s this p)) \<bind> modify \<circ> (storage_update p) \<bind> K (return Empty)"

fun push where
  "push d (sdata.Array xs) = Some (sdata.Array (xs @@ d))"
| "push _ _ = None"

definition (in Contract) allocate::"id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) sdata \<Rightarrow> ('a::address) expression_monad" where
  "allocate i es d =
    do {
      is \<leftarrow> lfold es;
      ar \<leftarrow> option Err (\<lambda>s. slookup is (state.Storage s this i) \<bind> push d);
      storage_update_monad [] is (K ar) i
    }"

definition stack_check where
  "stack_check i kf mf cf sf =
    do {
      k \<leftarrow> applyf Stack;
      case k $$ i of
        Some x \<Rightarrow> case_kdata sf mf cf kf x
      | None \<Rightarrow> throw Err
    }"

definition option_check where
  "option_check f m = option Err f \<bind> m"

definition(in Contract) stackLookup::"id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad" where
  "stackLookup i es =
    do {
      is \<leftarrow> lfold es;
      stack_check i
        (\<lambda>k. return (Value k))
        (\<lambda>p. do {
          (l, md) \<leftarrow> option Err (\<lambda>s. mlookup (state.Memory s) is p);
          if mdata.is_Value md then return (rvalue.Value (mdata.vt md)) else return (rvalue.Memory l)
        })
        (\<lambda>p xs. do {
          sd \<leftarrow> option Err (\<lambda>s. state.Calldata s $$ p \<bind> clookup (xs@is));
          if cdata.is_Value sd then return (rvalue.Value (cdata.vt sd)) else return (rvalue.Calldata p (xs@is))
        })
        (\<lambda>p xs. do {
          sd \<leftarrow> option Err (\<lambda>s. slookup (xs@is) (state.Storage s this p));
          if sdata.is_Value sd then return (rvalue.Value (sdata.vt sd)) else return (rvalue.Storage p (xs@is))
        })
    }"

definition(in Contract) arrayLength::"id \<Rightarrow> ('a::address) expression_monad list \<Rightarrow> ('a::address) expression_monad" where
  "arrayLength i es =
    do {
      is \<leftarrow> lfold es;
      stack_check i
        (K (throw Err))
        (\<lambda>p. do {
          (l, md) \<leftarrow> option Err (\<lambda>s. mlookup (state.Memory s) is p);
          if mdata.is_Array md then return (rvalue.Value (Sint (of_nat (length (mdata.ar md))))) else throw Err
        })
        (\<lambda>p xs. do {
          sd \<leftarrow> option Err (\<lambda>s. state.Calldata s $$ p \<bind> clookup (xs@is));
          if cdata.is_Array sd then return (rvalue.Value (Sint (of_nat (length (cdata.ar sd))))) else throw Err
        })
        (\<lambda>p xs. do {
          sd \<leftarrow> option Err (\<lambda>s. slookup (xs@is) (state.Storage s this p));
          if sdata.is_Array sd then return (rvalue.Value (Sint (of_nat (length (sdata.ar sd))))) else throw Err
        })
    }"

subsection \<open>Stack\<close>

primrec (in Contract) assign_stack:: "id \<Rightarrow> ('a::address) valtype list \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) expression_monad" where
  "assign_stack i is (rvalue.Value v) =
    stack_check i
      (K ((modify (stack_update i (kdata.Value v))) \<bind> K (return Empty)))
      (\<lambda>p. (memory_update_monad (mvalue_update is p v)))
      (K (K (throw Err)))
      (\<lambda>p xs. storage_update_monad xs is (K (sdata.Value v)) p)"
| "assign_stack i is (rvalue.Memory p) =
    stack_check i
      (K (throw Err))
      (\<lambda>p'. case_list is
        (modify (stack_update i (kdata.Memory p))\<bind> K (return Empty))
        (K (K (memory_update_monad (marray_update is p' p)))))
      (K (K (throw Err)))
      (\<lambda>p' xs. option_check
        (\<lambda>s. copy_memory_storage (state.Memory s) p)
        (\<lambda>sd. storage_update_monad xs is (K sd) p'))"
| "assign_stack i is (rvalue.Calldata p xs) =
    stack_check i
      (K (throw Err))
      (\<lambda>p'. option_check
        (\<lambda>s. state.Calldata s $$ p \<bind> clookup (xs @ is))
        (\<lambda>cd. memory_update_monad (copy_calldata_memory (cd, p'))))
      (K (K (throw Err)))
      (\<lambda>p' xs'. option_check
        (\<lambda>s. state.Calldata s $$ p \<bind> clookup (xs @ is))
        (\<lambda>cd. storage_update_monad xs' is (K (copy_calldata_storage cd)) p'))"
| "assign_stack i is (rvalue.Storage p xs) =
    stack_check i
      (K (throw Err))
      (\<lambda>p'. option_check
        (\<lambda>s. slookup (xs @ is) (state.Storage s this p))
        (\<lambda>sd. memory_update_monad (copy_storage_memory (sd, p'))))
      (K (K (throw Err)))
      (\<lambda>p' xs'. case_list is
        (modify (stack_update i (kdata.Storage p xs)) \<bind> K (return Empty))
        (K (K (option_check
          (\<lambda>s. slookup (xs @ is) (state.Storage s this p))
          (\<lambda>sd. storage_update_monad xs' [] (K sd) p')))))"
| "assign_stack i is rvalue.Empty = throw Err"

definition (in Contract) assign_stack_monad::"String.literal \<Rightarrow> ('a rvalue, ex, 'a state) state_monad list \<Rightarrow> ('a rvalue, ex, 'a state) state_monad \<Rightarrow> ('a rvalue, ex, 'a state) state_monad" where
  "assign_stack_monad i es m \<equiv> 
    do {
      val \<leftarrow> m;
      is \<leftarrow> lfold es;
      assign_stack i is val;
      return Empty
    }"

subsection \<open>Storage\<close>

primrec (in Contract) assign_storage:: "id \<Rightarrow> ('a::address) valtype list \<Rightarrow> ('a::address) rvalue \<Rightarrow> ('a::address) expression_monad" where
  "assign_storage i is (rvalue.Value v) = storage_update_monad [] is (K (sdata.Value v)) i"
| "assign_storage i is (rvalue.Memory p) =
    (option_check
      (\<lambda>s. copy_memory_storage (state.Memory s) p)
      (\<lambda>sd. storage_update_monad [] is (K sd) i))"
| "assign_storage i is (rvalue.Calldata p xs) =
    (option_check
      (\<lambda>s. state.Calldata s $$ p \<bind> clookup xs)
      (\<lambda>cd. storage_update_monad [] is (K (copy_calldata_storage cd)) i))"
| "assign_storage i is (rvalue.Storage p xs) =
    (option_check
      (\<lambda>s. slookup xs (state.Storage s this p))
      (\<lambda>sd. storage_update_monad [] is (K sd) i))"
| "assign_storage i is rvalue.Empty = throw Err"

definition (in Contract) assign_storage_monad where
  "assign_storage_monad i es m \<equiv> 
    do {
      val \<leftarrow> m;
      is \<leftarrow> lfold es;
      assign_storage i is val
    }"

(*
  Note that m is evaluated first and then indexed expressions are evaluated from left to right.
  
  This can be seen by executing test() in the following example which outputs 3 before 1 and 2.
  
  pragma solidity >=0.7.0 <0.9.0;
  
  contract Test {
  
      event Log(uint _value);
  
      uint[5][5] myarray;
  
      function print(uint x) public returns (uint) {
          emit Log(x);
          return x;
      }
  
      function test() external {
          myarray[print(1)][print(2)] = print(3);
      }
  }
*)

section \<open>Declarations\<close>

definition (in Contract) initStorage::"id \<Rightarrow> ('a::address) sdata \<Rightarrow> ('a::address) expression_monad" where
  "initStorage i v \<equiv> modify (\<lambda>s. storage_update i v s) \<bind> K (return Empty)"

abbreviation emptyStack::"('a::address) expression_monad" where
  "emptyStack \<equiv> (modify (Stack_update (K fmempty)) \<bind> K (return Empty))"

definition init::"id \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) expression_monad" where
  "init i v \<equiv> modify (stack_update i (kdata.Value v)) \<bind> K (return Empty)"

definition minit::"id \<Rightarrow> ('a::address) cdata \<Rightarrow> ('a::address) expression_monad" where
  "minit i c \<equiv> update (\<lambda>s. let (l,m) = State.minit c (state.Memory s) in (Empty, s\<lparr>Stack := fmupd i (kdata.Memory l) (Stack s), Memory := m\<rparr>))"

definition cinit::"id \<Rightarrow> ('a::address) cdata \<Rightarrow> ('a::address) expression_monad" where
  "cinit i c \<equiv> modify (calldata_update i c \<circ> stack_update i (kdata.Calldata i [])) \<bind> K (return Empty)"

definition cdecl::"id \<Rightarrow> id \<Rightarrow> ('a::address) valtype list \<Rightarrow> ('a::address) expression_monad" where
  "cdecl i i' v \<equiv> modify (stack_update i (kdata.Calldata i' v)) \<bind> K (return Empty)"

definition sinit::"id \<Rightarrow> id \<Rightarrow> ('a::address) valtype list \<Rightarrow> ('a::address) expression_monad" where
  "sinit i i' v \<equiv> modify (stack_update i (kdata.Storage i' v)) \<bind> K (return Empty)"

definition create_memory_value :: "('a::address) valtype \<Rightarrow> (location, unit, ('a::address) memory) state_monad" where
  "create_memory_value v = 
    do {
      pos \<leftarrow> applyf length;
      modify (\<lambda>m. m @@ mdata.Value v);
      return pos
    }"

definition create_memory_array :: "nat \<Rightarrow> (location, unit, ('a::address) memory) state_monad \<Rightarrow> (location, unit, ('a::address) memory) state_monad" where
  "create_memory_array x mm = 
    do {
      ls \<leftarrow> mfold mm x;
      pos \<leftarrow> applyf length;
      modify (\<lambda>m. m @@ mdata.Array ls);
      return pos
    }"

lemma "P (execute (create_memory_array 2 (create_memory_array 3 (create_memory_value (Bool False)))) [])=
       P (Normal (8, [mdata.Value (Bool False), mdata.Value (Bool False), mdata.Value (Bool False), mdata.Array [0, 1, 2], mdata.Value (Bool False),
          mdata.Value (Bool False), mdata.Value (Bool False), mdata.Array [4, 5, 6], mdata.Array [3, 7]]))"
  by normalization

definition decl_memory_array :: "(location, unit, ('a::address) memory) state_monad \<Rightarrow> ('a::address) expression_monad" where
  "decl_memory_array mm = create (\<lambda>s.
    case (execute mm (state.Memory s)) of
      Normal (pos, m) \<Rightarrow> Normal (rvalue.Memory pos, s\<lparr>Memory := m\<rparr>)
    | Exception ((),m) \<Rightarrow> Exception (Err,s\<lparr>Memory := m\<rparr>)
    | NT \<Rightarrow> NT)"

section \<open>Loops\<close>

lemma true_monad_mono[mono]: "mono_sm (\<lambda>_. true_monad)"
  by (simp add: monotoneI sm_ordI)

lemma cond_K [partial_function_mono]: "mono_sm (\<lambda>f. K (f x) y)"
proof (rule monotoneI)
  fix xa::"'a \<Rightarrow> ('b, 'c, 'd) state_monad"
  and ya::" 'a \<Rightarrow> ('b, 'c, 'd) state_monad"
  assume "sm.le_fun xa ya"
  then show "sm_ord (K (xa x) y) (K (ya x) y)" using K.elims fun_ord_def by metis
qed

lemma lift_op_monad_mono:
  assumes "mono_sm A" and "mono_sm B"
  shows "mono_sm (\<lambda>f. lift_op_monad op (A f) (B f))"
  unfolding lift_op_monad_def
proof (rule bind_mono[OF assms(1)])
  fix lv
  show "mono_sm (\<lambda>f. B f \<bind> (\<lambda>rv. option Err (K (op lv rv)) \<bind> return))"
  proof (rule bind_mono[OF assms(2)])
    fix rv
    show "mono_sm (\<lambda>f. option Err (K (op lv rv)) \<bind> return)"
    proof (rule bind_mono)
      show "mono_sm (\<lambda>f. option Err (K (op lv rv)))" using option_monad_mono[of Err "K (op lv rv)"] by simp
    next
      fix y::"('x::address) rvalue"
      show "mono_sm (\<lambda>f. return y)" by (simp add: mono)
    qed
  qed
qed

lemma equals_monad_mono[mono]:
  assumes "mono_sm A" and "mono_sm B"
  shows "mono_sm (\<lambda>f. equals_monad (A f) (B f))"
  unfolding equals_monad_def by (rule lift_op_monad_mono[OF assms])

lemma cond_mono [partial_function_mono, mono]:
  assumes "mono_sm A" and "mono_sm B" and "mono_sm C"
  shows "mono_sm (\<lambda>f. cond_monad (A f) (B f) (C f))"
  unfolding cond_monad_def
proof (rule bind_mono)
  show "mono_sm (\<lambda>f. equals_monad (A f) true_monad)"
  proof (rule equals_monad_mono[OF assms(1)])
    show "mono_sm (\<lambda>f. true_monad)" by (simp add: mono)
  qed
next
  fix b
  show "mono_sm (\<lambda>f. if b = kdbool True then B f else if b = kdbool False then C f else throw Err)"
    by (rule Partial_Function.if_mono[OF assms(2)], rule Partial_Function.if_mono[OF assms(3)]) (rule throw_monad_mono) 
qed

subsection \<open>The While Monad\<close>

partial_function (sm) while_monad :: "('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "while_monad c m = cond_monad c (bind m (K (while_monad c m))) (return Empty)"

text \<open>
  The partial function package provides us with three properties:
  \<^item> A simplifier rule @{thm while_monad.simps}
  \<^item> A general induction rule @{thm while_monad.fixp_induct}
  \<^item> An induction rule for partial correctness @{thm while_monad.raw_induct}
\<close>

subsection \<open>Require/Assert\<close>

definition assert_monad :: "('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
 "assert_monad bm = 
    cond_monad bm (return Empty) (throw Err)"

section \<open>Solidity Constants\<close>

fun readValue:: "('a::address) rvalue \<Rightarrow> ((('a::address) valtype, ex, ('a::address) state) state_monad)" where
  "readValue (rvalue.Value x) = return x"
| "readValue _ = throw Err"

fun readAddress:: "('a::address) valtype \<Rightarrow> ((('a::address), ex, ('a::address) state) state_monad)" where
  "readAddress (Address x) = return x"
| "readAddress _ = throw Err"

fun readSint:: "('a::address) valtype \<Rightarrow> ((256 word, ex, ('a::address) state) state_monad)" where
  "readSint (Sint x) = return x"
| "readSint _ = throw Err"

locale Fallback = Contract +
  constrains this :: "'a::address"
  fixes fallback::"('a::address) \<Rightarrow> ('a::address) expression_monad"
  assumes fallback_invariant:
    "\<And>call:: 'a expression_monad.
      \<And>P E s.
      \<lbrakk>\<forall>s r. P s \<and> effect call s r \<longrightarrow> inv r P E;
      P s\<rbrakk>
      \<Longrightarrow> (\<forall>a r. effect (fallback a) s r
           \<longrightarrow> inv r (\<lambda>s'. state.Stack s' = state.Stack s \<and> state.Memory s' = state.Memory s \<and> state.Calldata s' = state.Calldata s \<and> P s')
                     (\<lambda>s'. state.Stack s' = state.Stack s \<and> state.Memory s' = state.Memory s \<and> state.Calldata s' = state.Calldata s \<and> E s'))"
begin

definition transfer_monad:: "('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad \<Rightarrow> ('a::address) expression_monad" where
  "transfer_monad am vm = 
    do {
      ak \<leftarrow> am;
      av \<leftarrow> readValue ak;
      a  \<leftarrow> readAddress av;
      vk \<leftarrow> vm;
      vv \<leftarrow> readValue vk;
      v  \<leftarrow> readSint vv;
      assert Err (\<lambda>s. Balances s this \<ge> unat v);
      modify (\<lambda>s. balances_update this (Balances s this - unat v) s);
      modify (\<lambda>s. balances_update a (Balances s a + unat v) s);
      fallback a
    }"

end

locale Method =
  fixes msg_sender :: "'a::address" (*address of calling contract*)
    and msg_value :: "256 word" (*money send*)
  assumes sender_neq_null: "msg_sender \<noteq> null"
begin

definition sender_monad where
  "sender_monad = address_monad msg_sender"

definition value_monad where
  "value_monad = sint_monad msg_value"

end

locale Solidity = Keccak256 + Method + Fallback +
  constrains keccak256::"('a::address) rvalue \<Rightarrow> ('a::address) rvalue"
         and msg_sender :: "'a::address"
         and this::"'a::address"
         and fallback::"('a::address) \<Rightarrow> ('a::address) expression_monad"
begin
  definition init_balance:: "('a rvalue, ex, ('a::address) state) state_monad" where
    "init_balance = modify (\<lambda>s. balance_update (Balances s this + unat msg_value) s) \<bind> K (return Empty)"
end

end
