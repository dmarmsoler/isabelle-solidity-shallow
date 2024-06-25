theory Token
  imports Solidity_Main
begin

section \<open>Token Contract\<close>

text \<open>
  In the following we verify a simple token contract from
  \<^url>\<open>https://www.isa-afp.org/entries/Solidity.html/\<close>.
\<close>

subsection \<open>Specification\<close>

contract Bank
  for "STR ''balances''": "sdata.Map (mapping (sdata.Value sint))"

constructor where
  "skip_monad"

cmethod deposit where
  "assign_storage_monad (STR ''balances'') [sender_monad]
    (plus_monad_safe (storeLookup (STR ''balances'') [sender_monad]) (value_monad))" ,

cmethod withdraw where
  "do {
    init (STR ''bal'') sint;
    assign_stack_monad (STR ''bal'') [] (storeLookup (STR ''balances'') [sender_monad]);
    assign_storage_monad (STR ''balances'') [sender_monad] (sint_monad 0);
    transfer_monad (sender_monad) (stackLookup (STR ''bal'') [])
  }"

section \<open>Verifying an Invariant\<close>

context Solidity
begin

abbreviation "SUMM x \<equiv> \<Sum>ad\<in>UNIV. unat (valtype.sint (sdata.vt (x (Address ad))))"

lemma 1:
  assumes "SUMM bal \<le> Balances s this"
      and "bal (Address msg_sender) = sdata.Value (Sint y)"
      and "unat y + unat msg_value < 2^256"
    shows "(\<Sum>ad\<in>UNIV. unat (valtype.sint (sdata.vt (if ad = msg_sender then sdata.Value (Sint (y + msg_value)) else bal (Address ad)))))
           \<le> Balances s this + unat msg_value"
proof -
  from sum_addr[of _ msg_sender] have "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> msg_sender. unat (valtype.sint (sdata.vt (bal (Address ad))))) +
    unat (valtype.sint (sdata.vt (bal (Address msg_sender)))) + unat msg_value \<le> Balances s this + unat msg_value"
  using assms(1) by simp
  moreover have "unat (valtype.sint (sdata.vt (sdata.Value (Sint (y + msg_value))))) \<le> unat (valtype.sint (sdata.vt (bal (Address msg_sender)))) + unat msg_value"
    using assms(2,3) unat_add_lem[where ?'a =256] by simp
  ultimately show ?thesis using sum_addr[of _ msg_sender] by simp
qed

lemma 2:
  assumes "SUMM bal \<le> Balances s this"
      and "bal (Address msg_sender) = sdata.Value (Sint y)"
    shows "(\<Sum>ad \<in> UNIV. unat (valtype.sint (sdata.vt (if ad = msg_sender then sdata.Value (Sint 0) else bal (Address ad)))))
          \<le> Balances s this + unat msg_value - unat y"
proof -
  from sum_addr[of _ msg_sender] have "(\<Sum>ad|ad \<in> UNIV \<and> ad \<noteq> msg_sender. unat (valtype.sint (sdata.vt (bal (Address ad))))) +
    (unat (valtype.sint (sdata.vt (bal (Address msg_sender)))) + unat msg_value - unat y) \<le> Balances s this + unat msg_value - unat y"
  using assms(1,2) by simp
  moreover have "unat (valtype.sint (sdata.vt (sdata.Value (Sint 0)))) \<le> unat (valtype.sint (sdata.vt (bal (Address msg_sender)))) + unat msg_value - unat y"
    using assms(2) unat_add_lem[where ?'a =256] by simp
  ultimately show ?thesis using sum_addr[of _ msg_sender] by simp
qed

lemma 3:
  assumes "SUMM bal \<le> Balances s this"
     and "bal (Address msg_sender) = sdata.Value (Sint y)"
  shows "(\<Sum>ad\<in>UNIV. unat (valtype.sint (sdata.vt (if ad = msg_sender then sdata.Value (Sint 0) else bal (Address ad)))))
       \<le> Balances s this + unat msg_value"
  using 2[OF assms] by simp

lemma 4:
  assumes "SUMM bal \<le> Balances s this"
     and "bal (Address msg_sender) = sdata.Value (Sint y)"
     and " msg_sender = this"
  shows "(\<Sum>ad\<in>UNIV. unat (valtype.sint (sdata.vt (if ad = this then sdata.Value (Sint 0) else bal (Address ad)))))
       \<le> Balances s this + unat msg_value"
  using 3[OF assms(1-2)] assms(3) by simp

lemma 5:
  assumes " \<forall>x. \<exists>y. bal x = sdata.Value (Sint y)"
     and "SUMM bal \<le> Balances s this"
     and "\<not> sdata.is_Value (bal (Address msg_sender))"
  shows "(\<Sum>ad \<in> UNIV. unat (valtype.sint (sdata.vt (if ad = msg_sender then sdata.Value (Sint 0) else bal (Address ad)))))
           \<le> Balances s this + unat msg_value"
proof -
  from assms(1) obtain y where "bal (Address msg_sender) = sdata.Value (Sint y)" by auto
  then have "sdata.is_Value (bal (Address msg_sender))" by simp
  with assms show ?thesis by simp
qed

definition sum_bal:: "(id \<Rightarrow> 'a sdata) \<times> nat \<Rightarrow> bool"
  where "sum_bal sb \<equiv>
          (\<exists>x. (fst sb) (STR ''balances'') = sdata.Map x \<and> (\<forall>y. \<exists>z. x y = sdata.Value (Sint z))) \<and>
          (\<forall>x. (fst sb) (STR ''balances'') = sdata.Map x \<longrightarrow> (snd sb) \<ge> SUMM x)"

text \<open>We need to create introduction and elimination rules for the invariant and add it to the wprule and wperule lists.\<close>

lemma sum_balI[wprule]:
  assumes "s (STR ''balances'') = sdata.Map bal"
      and "\<And>x. \<exists>y. bal x = sdata.Value (Sint y)"
      and "b \<ge> SUMM bal"
  shows "sum_bal (s, b)"
  unfolding sum_bal_def using assms by simp

lemma sum_balE[wperule]:
  assumes "sum_bal (s, b)"
  obtains bal where "s (STR ''balances'') = sdata.Map bal"
                and "\<forall>x. \<exists>y. bal x = sdata.Value (Sint y)"
                and "b \<ge> SUMM bal"
  using assms unfolding sum_bal_def by auto

lemma(in Solidity) bal_msg_sender:
  assumes "\<forall>x. \<exists>y. bal x = sdata.Value (Sint y)"
  obtains y where "bal (Address msg_sender) = sdata.Value (Sint y)"
  using assms by auto

text \<open>
  Now we can start verifying the invariant.
  To this end our package provides a keyword invariant which takes a property as parameter and generates proof obligations.
\<close>
end
context Solidity
begin

lemma constructor_bank:
  assumes "effect bank_constructor s r"
    shows "inv r (inv_state sum_bal) (inv_state sum_bal)"
  using assms
  apply (erule_tac inv_wp)
  unfolding bank_constructor_def inv_state_def
  by (vcg | auto)+

lemma deposit:
    fixes call:: "'a bank \<Rightarrow> 'a expression_monad"
  assumes "effect (deposit call) s r"
      and "inv_state sum_bal s" 
    shows "inv r (inv_state sum_bal) (inv_state sum_bal)"
  using assms
  apply (erule_tac inv_wp)
  unfolding deposit_def inv_state_def
  by (vcg | auto simp add:1 | rule bal_msg_sender, assumption)+

lemma withdraw_sender:
  fixes call:: "'a bank \<Rightarrow> 'a expression_monad"
  assumes "\<And>x. \<forall>s r. inv_state sum_bal s \<and> effect (call x) s r \<longrightarrow> local.inv r (inv_state sum_bal) (inv_state sum_bal)"
      and "effect (withdraw call) s r"
      and "inv_state sum_bal s"
      and "msg_sender \<noteq> this"
    shows "inv r (inv_state sum_bal) (inv_state sum_bal)"
  using assms(2-)
  apply (erule_tac inv_wp)
  unfolding withdraw_def inv_state_def
  apply (vcg | auto)+
  apply (rule bal_msg_sender, assumption)
  apply (vcg wprule: wp_fallback[OF assms(1)] | auto)+
  apply (simp add:2)
  apply (simp add:wpsimps)+
  apply (vcg | auto)+
  apply (simp add:3)
  apply (simp add:wpsimps)+
  by (vcg wprule: wp_fallback[OF assms(1)] | auto)+

lemma (in Solidity) subst:
  "msg_sender = this \<Longrightarrow> wp sender_monad P Q s \<Longrightarrow> wp (Method.sender_monad this) P Q s" by simp

(*
  Fixme: Here I do have some problems with the simplifier.
*)
lemma withdraw_this:
  fixes call:: "'a bank \<Rightarrow> 'a expression_monad"
  assumes "\<And>x. \<forall>s r. inv_state sum_bal s \<and> effect (call x) s r \<longrightarrow> local.inv r (inv_state sum_bal) (inv_state sum_bal)"
      and "effect (withdraw call) s r"
      and "inv_state sum_bal s"
      and "msg_sender = this"
    shows "inv r (inv_state sum_bal) (inv_state sum_bal)"
  using assms(2-)
  apply (erule_tac inv_wp)
  unfolding withdraw_def inv_state_def
  apply (vcg wprule: wp_fallback[OF assms(1)] | auto)+
  apply (rule bal_msg_sender, assumption)
  apply (vcg wprule: wp_fallback[OF assms(1)] | simp add: 4)+
  apply (rule bal_msg_sender, assumption)
  apply (rule subst,assumption,wp)
  apply (vcg wprule: wp_fallback[OF assms(1)])
  apply (rule subst,assumption, wp)
  apply (vcg wprule: wp_fallback[OF assms(1)])
  apply (rule subst,assumption,wp)
  by (wp wprule: wp_fallback[OF assms(1)] | auto simp add:wpsimps 4)+

lemma withdraw:
  fixes call:: "'a bank \<Rightarrow> 'a expression_monad"
  assumes "\<And>x. \<forall>s r. inv_state sum_bal s \<and> effect (call x) s r \<longrightarrow> local.inv r (inv_state sum_bal) (inv_state sum_bal)"
      and "effect (withdraw call) s r"
      and "inv_state sum_bal s"
    shows "inv r (inv_state sum_bal) (inv_state sum_bal)"
proof (cases "msg_sender = this")
  case True
  show ?thesis using withdraw_this[OF assms True] .
next
  case False
  show ?thesis using withdraw_sender[OF assms False] .
qed

end

invariant sum_bal: sum_bal sum_bal for Bank
  apply -
  using constructor_bank apply blast
  using deposit apply blast
  using withdraw apply blast
  done

end