theory Casino
  imports Solidity_Main
begin

lemma sym[wpdrules]:
  assumes "rvalue.Value v = y"
    shows "y = rvalue.Value v"
  using assms by simp

lemma sym2[wpdrules]:
  assumes "sdata.Value v = y"
    shows "y = sdata.Value v"
  using assms by simp

section \<open>Casino Contract\<close>

text \<open>
  In the following we verify the Casino contract from the VerifyThis Long-Term Challenge:
  \<^url>\<open>https://verifythis.github.io/02casino/\<close>.
\<close>

subsection \<open>Specification\<close>

text \<open>
  In the following we describe the specification of the contract.
\<close>

text \<open>
  Method modifiers are formalized as abbreviations.
  They need to be formalized in the Solidity context to provide access to various contextual information.
\<close>

context Solidity
begin

abbreviation byOperator::"(unit, ex, 'a state) state_monad" where
  "byOperator \<equiv> assert Err (\<lambda>s. sdata.Value (valtype.Address msg_sender) = state.Storage s this (STR ''operator''))"

abbreviation inState:: "'a valtype \<Rightarrow> (unit, ex, 'a state) state_monad" where
  "inState state \<equiv> assert Err (\<lambda>s. state.Storage s this (STR ''state'') = sdata.Value state)"

abbreviation noActiveBet::"(unit, ex, ('a, 'b) state_scheme) state_monad" where
  "noActiveBet \<equiv> assert Err (\<lambda>s. state.Storage s this (STR ''state'') \<noteq> sdata.Value (Sint 2))"

end

text \<open>
  The contract can now be specified using the "contract" command.
  This command requires the following:
  \<^item> A sequence of member variables
  \<^item> A constructor
  \<^item> A sequence of methods
\<close>
ML \<open>
  val pretty_term = Syntax.pretty_term

  val pwriteln = Pretty.writeln

  fun pretty_terms ctxt trms =
    Pretty.block (Pretty.commas (map (pretty_term ctxt) trms))

  fun pretty_typ ctxt ty = Syntax.pretty_typ ctxt ty

  fun pretty_typs ctxt tys =
    Pretty.block (Pretty.commas (map (pretty_typ ctxt) tys))

  fun pretty_thm ctxt thm =
    pretty_term ctxt (Thm.prop_of thm)
\<close>

contract Casino
  for "STR ''state''": "sdata.Value sint"
  and "STR ''operator''": "sdata.Value address"
  and "STR ''player''": "sdata.Value address"
  and "STR ''pot''": "sdata.Value sint"
  and "STR ''hashedNumber''": "sdata.Value bytes"
  and "STR ''bet''": "sdata.Value sint"
  and "STR ''guess''": "sdata.Value sint"

constructor
where
  "skip_monad"

cmethod createGame
  param "STR ''hashNum''": "Bytes hashNum"
where
  "do {
    byOperator;
    inState (valtype.Sint 0);
    assign_storage_monad (STR ''hashedNumber'') [] (stackLookup (STR ''hashNum'') []);
    assign_storage_monad (STR ''state'') [] (sint_monad 1)
   }",

cmethod placeBet
  param "STR ''guess''": "Sint guess"
where
  "do {
    inState (valtype.Sint 1);
    assert_monad (not_monad (equals_monad sender_monad (storeLookup (STR ''operator'') [])));
    assert_monad (not_monad (equals_monad value_monad (storeLookup (STR ''pot'') [])));
    assign_storage_monad (STR ''state'') [] (sint_monad 2);
    assign_storage_monad (STR ''player'') [] sender_monad;
    assign_storage_monad (STR ''bet'') [] value_monad;
    assign_storage_monad (STR ''guess'') [] (stackLookup (STR ''guess'') [])
  }",

cmethod decideBet
  param "STR ''secretNumber''": "Sint secretNumber"
where
  "do {
    byOperator;
    inState (valtype.Sint 2);
    assert_monad (equals_monad (storeLookup (STR ''hashedNumber'') []) (keccak256_monad (stackLookup (STR ''secretNumber'') [])));
    init (STR ''secret'') (sint :: 'a valtype);
    assign_stack_monad (STR ''secret'') [] (cond_monad (equals_monad (mod_monad (stackLookup (STR ''secretNumber'') []) (sint_monad 2)) (sint_monad 0)) (bool_monad True) (bool_monad False));
    cond_monad (equals_monad (stackLookup (STR ''secret'') []) (storeLookup (STR ''guess'') []))
      (do {
        assign_stack_monad (STR ''pot'') [] (minus_monad (storeLookup (STR ''pot'') []) (storeLookup (STR ''bet'') []));
        transfer_monad (storeLookup (STR ''player'') []) (mult_monad (storeLookup (STR ''bet'') []) (sint_monad 2));
        assign_stack_monad (STR ''bet'') [] (sint_monad 0)
       })
      (do {
        assign_stack_monad (STR ''pot'') [] (plus_monad (storeLookup (STR ''pot'') []) (storeLookup (STR ''bet'') []));
        assign_stack_monad (STR ''bet'') [] (sint_monad 0)
       });
    assign_storage_monad (STR ''state'') [] (sint_monad 0)
  }",

cmethod addToPot
where
  "do {
    byOperator;
    assign_storage_monad (STR ''pot'') [] (plus_monad_safe (storeLookup (STR ''pot'') []) value_monad)
  }",

cmethod removeFromPot
  param "STR ''amount''": "Sint amount"
where
  "do {
    byOperator;
    noActiveBet;
    assign_storage_monad (STR ''pot'') [] (minus_monad_safe (storeLookup (STR ''pot'') []) (stackLookup (STR ''amount'') []));
    transfer_monad (storeLookup (STR ''operator'') []) (stackLookup (STR ''amount'') [])
  }"

text (in Solidity) \<open>
  The contract command creates definitions for the constructor and each method:
  \<^item> @{thm Casino.Solidity.casino_constructor_def [no_vars]}
  \<^item> @{thm Casino.Solidity.createGame_def [no_vars]}
  \<^item> ...

  In addition it creates and proves monotonicity lemmas for the partial\_function package for each method:
  \<^item> @{thm createGame_def_mono [no_vars]}

  It also creates a datatype for the contract:
  \<^item> @{typ "'a Solidity.casino"}
  with constructors for each method:
  \<^item> @{term Casino.Solidity.casino.CreateGame_m}

  Finally it creates a recursive definition using the partial\_function package in mode sm:
  \<^item> @{term Casino.Solidity.call}
  \<^item> @{thm Casino.Solidity.call.simps [no_vars]}
  
  The proof obligations are discharged using the previously generated monotonicity lemmas.

  The partial\_function package provides us with an induction rule:
  @{thm Casino.Solidity.call.raw_induct [no_vars]}
\<close>

section \<open>Verifying an Invariant\<close>

text \<open>
  We start by verifying an invariant regarding the relationship between pot and balance.
  To this end we need to add type information to the invariant.
  Note that an invariant is formalized as a predicate over the contracts state and balance.
\<close>

definition pot_balance:: "(id \<Rightarrow> 'a::address sdata) \<times> nat \<Rightarrow> bool"
  where "pot_balance sb \<equiv>
          (\<exists>x. (fst sb) (STR ''state'') = sdata.Value (Sint x)) \<and>
          (\<exists>x. (fst sb) (STR ''operator'') = sdata.Value (Address x)) \<and>
          (\<exists>x. (fst sb) (STR ''player'') = sdata.Value (Address x)) \<and>
          (\<exists>x. (fst sb) (STR ''pot'') = sdata.Value (Sint x)) \<and>
          (\<exists>x. (fst sb) (STR ''hashedNumber'') = sdata.Value (Bytes x)) \<and>
          (\<exists>x. (fst sb) (STR ''bet'') = sdata.Value (Sint x)) \<and>
          (\<exists>x. (fst sb) (STR ''guess'') = sdata.Value (Sint x)) \<and>
          (\<forall>x. (fst sb) (STR ''pot'') = sdata.Value (Sint (x)) \<longrightarrow> (snd sb) \<ge> unat x)"

text \<open>We need to create introduction and elimination rules for the invariant and add it to the wprule and wperule lists.\<close>

lemma pot_balanceI[wprule]:
  assumes "s (STR ''state'') = sdata.Value (Sint state)"
     and  "s (STR ''operator'') = sdata.Value (Address operator)"
     and  "s (STR ''player'') = sdata.Value (Address player)"
     and  "s (STR ''pot'') = sdata.Value (Sint pot)"
     and  "s (STR ''hashedNumber'') = sdata.Value (Bytes hashedNumber)"
     and  "s (STR ''bet'') = sdata.Value (Sint bet)"
     and  "s (STR ''guess'') = sdata.Value (Sint guess)"
     and  "\<And>x. s (STR ''pot'') = sdata.Value (Sint (x)) \<Longrightarrow> b \<ge> unat x"
  shows "pot_balance (s, b)"
  unfolding pot_balance_def using assms by simp

lemma pot_balanceE[wperule]:
  assumes "pot_balance (s, b)"
  obtains state operator player pot hashedNumber bet guess
  where "s (STR ''state'') = sdata.Value (Sint state)"
    and "s (STR ''operator'') = sdata.Value (Address operator)"
    and "s (STR ''player'') = sdata.Value (Address player)"
    and "s (STR ''pot'') = sdata.Value (Sint pot)"
    and "s (STR ''hashedNumber'') = sdata.Value (Bytes hashedNumber)"
    and "s (STR ''bet'') = sdata.Value (Sint bet)"
    and "s (STR ''guess'') = sdata.Value (Sint guess)"
    and "\<And>x. s (STR ''pot'') = sdata.Value (Sint (x)) \<Longrightarrow> b \<ge> unat x"
  using assms unfolding pot_balance_def by auto

text \<open>
  Now we can start verifying the invariant.
  To this end our package provides a keyword invariant which takes a property as parameter and generates proof obligations.
\<close>

context Solidity
begin

lemma constructor_casino:
  assumes "effect casino_constructor s r"
    shows "local.inv r (inv_state pot_balance) (inv_state pot_balance)"
  using assms
  apply (erule_tac inv_wp)
  unfolding casino_constructor_def inv_state_def
  by (vcg | auto)+

lemma createGame:
    fixes call:: "'a casino \<Rightarrow> (unit, ex, ('a::address) state) state_monad"
  assumes "effect (createGame callx x) s r"
      and "inv_state pot_balance s" 
    shows "inv r (inv_state pot_balance) (inv_state pot_balance)"
  using assms
  apply (erule_tac inv_wp)
  unfolding createGame_def inv_state_def
  by (vcg | auto)+

lemma placeBet:
    fixes call:: "'a casino \<Rightarrow> 'a expression_monad"
    assumes "effect (placeBet call x) s r"
        and "inv_state pot_balance s" 
    shows "inv r (inv_state pot_balance) (inv_state pot_balance)"
  using assms
  apply (erule_tac inv_wp)
  unfolding placeBet_def inv_state_def
  by (vcg | auto)+

lemma decideBet:
    fixes call:: "'a casino \<Rightarrow> 'a expression_monad"
    assumes "effect (decideBet call x) s r"
        and "inv_state pot_balance s" 
    shows "inv r (inv_state pot_balance) (inv_state pot_balance)"
  using assms
  apply (erule_tac inv_wp)
  unfolding decideBet_def inv_state_def
  by (vcg | auto)+

lemma unat_add_imp:
  assumes "(unat (x::256 word) + unat y < 115792089237316195423570985008687907853269984665640564039457584007913129639936)"
    shows "(unat (x + y) = unat x + unat y)" using assms Word.unat_add_lem[where ?'a=256, of x y] by simp

lemma addToPot:
    fixes call:: "'a casino \<Rightarrow> 'a expression_monad"
  assumes "effect (addToPot call) s r"
      and "inv_state pot_balance s"
    shows "inv r (inv_state pot_balance) (inv_state pot_balance)"
  using assms
  apply (erule_tac inv_wp)
  unfolding addToPot_def inv_state_def
  by (vcg | auto dest:unat_add_imp)+

text \<open>
  If a method uses a call parameter we can assume the property below and use it to discharge the first premise of @{thm wp_fallback}.
  Then we can pass wp\_fallback to the verification condition generator using the wprule attribute.
\<close>

lemma 111:
  assumes "unat pot \<le> Balances s this"
      and *: "x \<le> pot"
    shows "unat (pot - x) \<le> Balances s this + unat msg_value - unat x"
 using assms unat_sub[OF *]  by simp

lemma 222: "unat pot \<le> Balances s this \<Longrightarrow>
       x \<le> pot \<Longrightarrow>
    unat (pot - x) \<le> Balances s this + unat msg_value"
  using 111 by fastforce

lemma removeFromPot_this:
  fixes call:: "'a casino \<Rightarrow> 'a expression_monad"
  assumes "\<And>x. \<forall>s r. inv_state pot_balance s \<and> effect (call x) s r \<longrightarrow> local.inv r (inv_state pot_balance) (inv_state pot_balance)"
      and "effect (removeFromPot call x) s r"
      and "inv_state pot_balance s"
      and "msg_sender = this"
    shows "inv r (inv_state pot_balance) (inv_state pot_balance)"
  using assms(2-)
  apply (erule_tac inv_wp)
  unfolding removeFromPot_def inv_state_def
  by (vcg wprule: wp_fallback[OF assms(1)] | (rule 111;assumption) | (rule 222;assumption) | auto simp add:wpsimps)+

lemma removeFromPot_nthis:
  fixes call:: "'a casino \<Rightarrow> 'a expression_monad"
  assumes "\<And>x. \<forall>s r. inv_state pot_balance s \<and> effect (call x) s r \<longrightarrow> local.inv r (inv_state pot_balance) (inv_state pot_balance)"
      and "effect (removeFromPot call x) s r"
      and "inv_state pot_balance s"
      and "msg_sender \<noteq> this"
    shows "inv r (inv_state pot_balance) (inv_state pot_balance)"
  using assms(2-)
  apply (erule_tac inv_wp)
  unfolding removeFromPot_def inv_state_def
  by (vcg wprule: wp_fallback[OF assms(1)] | (rule 111;assumption) | (rule 222;assumption) | auto simp add:wpsimps)+

lemma removeFromPot:
  fixes call:: "'a casino \<Rightarrow>'a expression_monad"
  assumes "\<And>x. \<forall>s r. inv_state pot_balance s \<and> effect (call x) s r \<longrightarrow> local.inv r (inv_state pot_balance) (inv_state pot_balance)"
      and "effect (removeFromPot call x) s r"
      and "inv_state pot_balance s"
    shows "inv r (inv_state pot_balance) (inv_state pot_balance)"
proof (cases "msg_sender=this")
  case True
  then show ?thesis using removeFromPot_this[OF assms] by simp
next
  case False
  then show ?thesis using removeFromPot_nthis[OF assms] by simp
qed

end

invariant pot_balance: "pot_balance::(String.literal \<Rightarrow> 'a sdata) \<times> nat \<Rightarrow> bool" "pot_balance::(String.literal \<Rightarrow> 'a sdata) \<times> nat \<Rightarrow> bool" for Casino
  apply -
  using constructor_casino apply blast
  using createGame apply blast
  using placeBet apply blast
  using decideBet apply blast
  using addToPot apply blast
  using removeFromPot apply blast
  done

text \<open>
  The package then generates an overall proof over the call function:
  @{thm Solidity.pot_balance}
\<close>

end