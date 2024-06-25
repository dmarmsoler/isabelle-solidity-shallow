theory Voting
  imports Solidity_Main
begin

section \<open>Voting Contract\<close>

text \<open>
  In the following we verify the Voting contract from the official Solidity documentation:
  \<^url>\<open>https://docs.soliditylang.org/en/v0.8.25/solidity-by-example.html#voting\<close>.
\<close>

lemma kdequals_true[wpdrules]:
  assumes "kdequals (rvalue.Value (Sint w)) (rvalue.Value (Sint x)) = Some (rvalue.Value (Bool True))"
  shows "w = x"
  using assms unfolding kdequals_def by simp

subsection \<open>Specification\<close>

abbreviation TT::"((String.literal \<Rightarrow> 'a sdata) \<times> nat) \<Rightarrow> bool" where "TT a \<equiv> True"

context Solidity
begin

abbreviation Voter where "Voter \<equiv> sdata.Array [sdata.Value sint,sdata.Value bool,sdata.Value address,sdata.Value (sint::'a valtype)]"
abbreviation "weight \<equiv> return (rvalue.Value ((Sint 0)::'a valtype))"
abbreviation "voted \<equiv> 1::nat"
abbreviation "sdelegate \<equiv> 2::nat"
abbreviation "svote \<equiv> 3::nat"

abbreviation "Proposal name voteCount \<equiv> sdata.Array [name::'a sdata, voteCount]"
abbreviation "name \<equiv> 0::nat"
abbreviation "voteCount \<equiv> 1::nat"

end

text \<open>
  The contract can now be specified using the "contract" command.
  This command requires the following:
  \<^item> A sequence of member variables
  \<^item> A constructor
  \<^item> A sequence of methods
\<close>

context Solidity
begin

abbreviation "SUMM (x::('a valtype \<Rightarrow> 'a sdata)) \<equiv> \<Sum>ad|\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). (THE y. \<exists>v. x (Address ad) = sdata.Array v \<and> y=unat (valtype.sint (sdata.vt (v ! 0))))"
abbreviation "SUMM2 (x::'a sdata list) \<equiv> \<Sum>i\<in>{0..length x}. (THE y. \<exists>p. x ! i = sdata.Array p \<and> y=unat (valtype.sint (sdata.vt (p ! 1))))"

definition inv':: "(id \<Rightarrow> 'a sdata) \<Rightarrow> bool"
  where "inv' s \<equiv> (\<forall>x y. s (STR ''voters'') = sdata.Map x
                       \<and> s (STR ''proposals'') = sdata.Array y
                            \<longrightarrow> (SUMM2 y \<le> SUMM x))"

definition sum_votes:: "(id \<Rightarrow> 'a sdata) \<times> nat \<Rightarrow> bool"
  where "sum_votes sb \<equiv>
          (\<exists>x. (fst sb) (STR ''voters'') = sdata.Map x \<and> (\<forall>y. \<exists>w t d v. x y = sdata.Array [sdata.Value (Sint w),sdata.Value (Bool t),sdata.Value (Address d),sdata.Value (Sint v)])) \<and>
          (\<exists>x. (fst sb) (STR ''proposals'') = sdata.Array x \<and> (\<forall>y \<in> {0 .. length x}. \<exists>n v. x ! y = sdata.Array [sdata.Value (Bytes n), sdata.Value (Sint v)])) \<and>
          (\<exists>x. (fst sb) (STR ''chairperson'') = sdata.Value (Address x)) \<and>
          inv' (fst sb)"

text \<open>We need to create introduction and elimination rules for the invariant and add it to the wprule and wperule lists.\<close>

lemma sum_votesI:
  assumes "s (STR ''voters'') = sdata.Map voters"
      and "s (STR ''proposals'') = sdata.Array proposals"
      and "s (STR ''chairperson'') = sdata.Value (Address chairperson)"
      and "\<And>x. \<exists>w t d v. voters x = sdata.Array [sdata.Value (Sint w),sdata.Value (Bool t),sdata.Value (Address d),sdata.Value (Sint v)]"
      and "\<And>x. x \<in> {0 .. length proposals} \<longrightarrow> (\<exists>n v. proposals ! x = sdata.Array [sdata.Value (Bytes n), sdata.Value (Sint v)])"
      and "inv' s"
  shows "sum_votes (s, b)"
  unfolding sum_votes_def using assms by simp

lemma sum_votesE[wperule]:
  assumes "sum_votes (s, b)"
  obtains voters proposals chairperson where "s (STR ''voters'') = sdata.Map voters"
                   and "s (STR ''proposals'') = sdata.Array proposals"
                   and "s (STR ''chairperson'') = sdata.Value (Address chairperson)"
                   and "\<forall>x. \<exists>w t d v. voters x = sdata.Array [sdata.Value (Sint w),sdata.Value (Bool t),sdata.Value (Address d),sdata.Value (Sint v)]"
                   and "\<forall>x. x \<in> {0 .. length proposals} \<longrightarrow> (\<exists>n v. proposals ! x = sdata.Array [sdata.Value (Bytes n), sdata.Value (Sint v)])"
                   and "inv' s"
  using assms unfolding sum_votes_def by auto

contract Ballot
  for "STR ''chairperson''": "sdata.Value address"
  and "STR ''voters''": "sdata.Map (mapping Voter)"
  and "STR ''proposals''": "sdata.Array []"

constructor
  memory "STR ''proposalNames''": "proposalNames"
where
  "do {
    assign_storage_monad (STR ''chairperson'') [] sender_monad;
    assign_storage_monad (STR ''voters'') [stackLookup (STR ''chairperson'') [], weight] (sint_monad 1);
    init (STR ''i'') (Sint 0);
    while_monad (less_monad (stackLookup (STR ''i'') []) (arrayLength (STR ''proposalNames'') []))
      (do {
        allocate (STR ''proposals'') [] (Proposal (sdata.Value bytes) (sdata.Value sint));
        assign_storage_monad (STR ''proposals'') [storeArrayLength (STR ''proposals'') [], sint_monad 0] (stackLookup (STR ''proposalNames'') [stackLookup (STR ''i'') []]);
        assign_storage_monad (STR ''proposals'') [storeArrayLength (STR ''proposals'') [], sint_monad 1] (sint_monad 0);
        assign_stack_monad (STR ''i'') [] (plus_monad (stackLookup (STR ''i'') []) (sint_monad 1))
      })
   }"

cmethod giveRightToVote
  param "STR ''voter''": "valtype.Address voter"
where
  "do {
    require_monad (equals_monad sender_monad (storeLookup (STR ''chairperson'') []));
    require_monad (not_monad (storeLookup (STR ''voters'') [stackLookup (STR ''voter'') [], sint_monad 1]));
    require_monad (equals_monad (storeLookup (STR ''voters'') [stackLookup (STR ''voter'') [], sint_monad 0]) (sint_monad 0));
    assign_storage_monad (STR ''voters'') [stackLookup (STR ''voter'') [], sint_monad 0] (sint_monad 1)
  }",

cmethod delegate
  param "STR ''to''": "valtype.Address to"
where
  "do {
    sinit (STR ''sender'') (STR '''') [];
    assign_stack_monad (STR ''sender'') [] (storeLookup (STR ''voters'') [sender_monad]);
    require_monad (not_monad (equals_monad (stackLookup (STR ''sender'') [sint_monad 0]) (sint_monad 0)));
    require_monad (not_monad (stackLookup (STR ''sender'') [sint_monad 1]));
    require_monad (not_monad (equals_monad (stackLookup (STR ''to'') []) sender_monad));
    while_monad (equals_monad (storeLookup (STR ''voters'') [stackLookup (STR ''to'') [], sint_monad 2]) (address_monad null))
      (do {
        assign_stack_monad (STR ''to'') [] (storeLookup (STR ''voters'') [stackLookup (STR ''to'') [], sint_monad 2]);
        require_monad (not_monad (equals_monad (stackLookup (STR ''to'') []) sender_monad))
      });
    sinit (STR ''delegate_'') (STR '''') [];
    assign_stack_monad (STR ''delegate_'') [] (storeLookup (STR ''voters'') [stackLookup (STR ''to'') []]);
    require_monad (not_monad (less_monad (stackLookup (STR ''delegate_'') [sint_monad 0]) (sint_monad 1)));
    assign_stack_monad (STR ''sender'') [sint_monad 1] (true_monad);
    assign_stack_monad (STR ''delegate_'') [sint_monad 2] (stackLookup (STR ''to'') []);
    require_monad (not_monad (stackLookup (STR ''delegate_'') [sint_monad 1]));
    cond_monad (stackLookup (STR ''delegate_'') [sint_monad 1])
      (assign_storage_monad (STR ''proposals'') [stackLookup (STR ''delegate_'') [sint_monad 3], sint_monad 1] (plus_monad_safe (storeLookup (STR ''proposals'') [stackLookup (STR ''delegate_'') [sint_monad 3], sint_monad 1]) (stackLookup (STR ''sender'') [sint_monad 0])))
      (assign_stack_monad (STR ''delegate_'') [sint_monad 0] (plus_monad_safe (stackLookup (STR ''delegate_'') [sint_monad 0]) (stackLookup (STR ''sender'') [sint_monad 0])))
  }",

cmethod vote
  param "STR ''proposal''": "valtype.Sint proposal"
where
  "do {
    sinit (STR ''sender'') (STR '''') [];
    assign_stack_monad (STR ''sender'') [] (storeLookup (STR ''voters'') [sender_monad]);
    require_monad (not_monad (equals_monad (stackLookup (STR ''sender'') [sint_monad 0]) (sint_monad 0)));
    require_monad (not_monad (stackLookup (STR ''sender'') [sint_monad 1]));
    assign_stack_monad (STR ''sender'') [sint_monad 1] (true_monad);
    assign_stack_monad (STR ''sender'') [sint_monad 4] (stackLookup (STR ''proposal'') []);
    assign_storage_monad (STR ''proposals'') [stackLookup (STR ''proposal'') [], sint_monad 1] (plus_monad_safe (storeLookup (STR ''proposals'') [stackLookup (STR ''proposal'') [], sint_monad 1]) (stackLookup (STR ''sender'') [sint_monad 0]))
  }",

cmethod winningProposal
  param "STR ''winningProposalu''": "valtype.Sint winningProposalu"
where
  "do {
    init (STR ''winningVoteCount'') (Sint 0);
    init (STR ''p'') (Sint 0);
    while_monad (less_monad (stackLookup (STR ''p'') []) (storeArrayLength (STR ''proposals'') []))
      (do {
        cond_monad (less_monad (stackLookup (STR ''winningVoteCount'') []) (storeLookup (STR ''proposals'') [stackLookup (STR ''p'') [], sint_monad 1]))
          (do {
            assign_stack_monad (STR ''winningVoteCount'') [] (storeLookup (STR ''proposals'') [stackLookup (STR ''p'') [], sint_monad 1]);
            assign_stack_monad (STR ''winningProposalu'') [] (stackLookup (STR ''p'') [])
          })
          (skip_monad)
      })
  }"

lemma obtain_voters:
  assumes "\<forall>x. \<exists>w t d v. voters x =
    sdata.Array [sdata.Value (Sint w), sdata.Value (Bool t), sdata.Value (Address d), sdata.Value (Sint v)]"
  obtains w t d v where "voters x =
    sdata.Array [sdata.Value (Sint w), sdata.Value (Bool t), sdata.Value (Address d), sdata.Value (Sint v)]"
  using assms by blast

lemma constructor_ballot:
  assumes "effect (ballot_constructor x) s r"
    shows "inv r (inv_state sum_votes) (inv_state TT)"
  using assms
  apply (erule_tac inv_wp)
  unfolding ballot_constructor_def inv_state_def
  by (vcg wprule: sum_votesI | auto)+

lemma kdequals_true[wpdrules]:
  assumes "kdequals (rvalue.Value (Address x)) (rvalue.Value (Address y)) = Some (rvalue.Value (Bool True))"
  shows "x = y"
  using assms unfolding kdequals_def by simp

lemma kdequals_false:
  assumes "kdequals (rvalue.Value (Address x)) (rvalue.Value (Address y)) = Some (rvalue.Value (Bool False))"
  shows "x \<noteq> y"
  using assms unfolding kdequals_def by simp

lemma kdnot[wpdrules]:
  assumes "kdnot (rvalue.Value (Bool t)) = Some (rvalue.Value (Bool True))"
  shows "\<not> t"
  using assms unfolding kdnot_def vtnot_def by simp

lemma inv_0:
  assumes "state.Storage s this STR ''voters'' = Map voters"
     and  "state.Storage s this STR ''proposals'' = sdata.Array proposals"
     and "inv' (state.Storage s this)"
     and "voters (Address x) = sdata.Array [sdata.Value (Sint 0), sdata.Value (Bool False), sdata.Value (Address d), sdata.Value (Sint v)]"
   shows "inv' (state.Storage
            (storage_update STR ''voters'' (Map (voters (Address x := sdata.Array [sdata.Value (Sint 1), sdata.Value (Bool False), sdata.Value (Address d), sdata.Value (Sint v)])))
            (stack_update STR ''voter'' (kdata.Value (Address x))
            (balance_update (Balances s this + unat msg_value)
            s\<lparr>Stack := {$$}, Memory := [], Calldata := {$$}\<rparr>))) this)"
  unfolding inv'_def
proof ((rule allI | rule impI)+, erule conjE)
  fix xa y
  define sum1 where "sum1 = (\<lambda>(y::'a sdata list) i . THE ya. \<exists>p. y ! i = sdata.Array p \<and> ya = unat (valtype.sint (sdata.vt (p ! 1))))"
  define sum2 where "sum2 = (\<lambda>(xa::'a valtype \<Rightarrow> 'a sdata) ad. THE y. \<exists>v. xa (Address ad) = sdata.Array v \<and> y = unat (valtype.sint (sdata.vt (v ! 0))))"
  assume *:"state.Storage (storage_update STR ''voters'' (Map (voters(Address x := sdata.Array [sdata.Value (Sint 1), sdata.Value (Bool False), sdata.Value (Address d), sdata.Value (Sint v)])))
             (stack_update STR ''voter'' (kdata.Value (Address x))
             (balance_update (Balances s this + unat msg_value)
             s\<lparr>Stack := {$$}, Memory := [], Calldata := {$$}\<rparr>)))
            this STR ''voters'' = Map xa"
     and **: "state.Storage (storage_update STR ''voters'' (Map (voters(Address x := sdata.Array [sdata.Value (Sint 1), sdata.Value (Bool False), sdata.Value (Address d), sdata.Value (Sint v)])))
               (stack_update STR ''voter'' (kdata.Value (Address x))
               (balance_update (Balances s this + unat msg_value)
               s\<lparr>Stack := {$$}, Memory := [], Calldata := {$$}\<rparr>)))
              this STR ''proposals'' = sdata.Array y"
  show "(\<Sum>i = 0..length y. sum1 y i) \<le> (\<Sum>ad | \<exists>v. xa (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 xa ad)"
  proof -
    from assms have "(\<Sum>i = 0..length proposals. sum1 proposals i) \<le> (\<Sum>ad | \<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 voters ad)" unfolding inv'_def sum1_def sum2_def by simp
    moreover have "(\<Sum>i = 0..length proposals. sum1 proposals i) = (\<Sum>i = 0..length y. sum1 y i)" using assms ** unfolding sum1_def by (simp add:wpsimps)
    moreover have "(\<Sum>ad | \<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 voters ad) = (\<Sum>ad | \<exists>v. xa (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 xa ad)"
    proof -
      from assms have " \<nexists>v. voters (Address x) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))" by simp
      then have "(\<Sum>ad | \<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 voters ad) = 
                 (\<Sum>ad | (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x. sum2 voters ad)" using sum_addr3[of x "{ad.  \<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))}" "sum2 voters"] by simp
      moreover have "\<not> (\<exists>v. xa (Address x) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)))" using * by (auto simp add:wpsimps)
      then have "(\<Sum>ad | \<exists>v. xa (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 xa ad) = 
                 (\<Sum>ad | (\<exists>v. xa (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x. sum2 xa ad)" using sum_addr3[of x "{ad.  \<exists>v. xa (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))}" "sum2 xa"] by simp
      moreover have "(\<Sum>ad | (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x. sum2 voters ad)
                   = (\<Sum>ad | (\<exists>v. xa (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x. sum2 xa ad)"
      proof (rule sum.mono_neutral_cong_right)
        show "finite {ad. (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x}" using finite finite_subset subset_UNIV by blast
        show "{ad. (\<exists>v. xa (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x}
        \<subseteq> {ad. (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x}" using * by (auto simp add:wpsimps)
        show " \<forall>i\<in>{ad. (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x} -
        {ad. (\<exists>v. xa (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x}.
         sum2 voters i = 0" using * by (auto simp add:wpsimps)
        show " \<And>xb. xb \<in> {ad. (\<exists>v. xa (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> x} \<Longrightarrow> sum2 voters xb = sum2 xa xb"  using * unfolding sum2_def by (auto simp add:wpsimps)
      qed
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma inv_1:
  assumes "state.Storage s this STR ''voters'' = Map voters"
      and "state.Storage s this STR ''proposals'' = sdata.Array proposals"
      and "inv' (state.Storage s this)"
      and "voters (Address msg_sender) = sdata.Array [sdata.Value (Sint w), sdata.Value (Bool False), sdata.Value (Address d), sdata.Value (Sint v)]"
      and "state.Storage sa this STR ''proposals'' = sdata.Array proposals"
      and "xa \<noteq> msg_sender"
      and "voters (Address xa) = sdata.Array [sdata.Value (Sint wb), sdata.Value (Bool False), sdata.Value (Address da), sdata.Value (Sint va)]"
      shows "inv' (state.Storage
          (storage_update STR ''voters'' (Map (voters
                  (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)],
                   Address xa := sdata.Array [sdata.Value (Sint (wb + w)), sdata.Value (Bool False), sdata.Value (Address xa), sdata.Value (Sint va)])))
          (storage_update STR ''voters'' (Map (voters
                  (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)],
                   Address xa := sdata.Array [sdata.Value (Sint wb), sdata.Value (Bool False), sdata.Value (Address xa), sdata.Value (Sint va)])))
          (storage_update STR ''voters'' (Map (voters
                (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)])))
          (stack_update STR ''delegate_'' (kdata.Storage STR ''voters'' [Address xa]) (stack_update STR ''delegate_'' (kdata.Storage STR '''' [])
          sa))))) this)"
  unfolding inv'_def
proof ((rule allI | rule impI)+, erule conjE)
  fix x y
  define sum1 where "sum1 = (\<lambda>(y::'a sdata list) i . THE ya. \<exists>p. y ! i = sdata.Array p \<and> ya = unat (valtype.sint (sdata.vt (p ! 1))))"
  define sum2 where "sum2 = (\<lambda>(xa::'a valtype \<Rightarrow> 'a sdata) ad. THE y. \<exists>v. xa (Address ad) = sdata.Array v \<and> y = unat (valtype.sint (sdata.vt (v ! 0))))"
  assume *:"state.Storage
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)],
               Address xa := sdata.Array [sdata.Value (Sint (wb + w)), sdata.Value (Bool False), sdata.Value (Address xa), sdata.Value (Sint va)])))
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)],
               Address xa := sdata.Array [sdata.Value (Sint wb), sdata.Value (Bool False), sdata.Value (Address xa), sdata.Value (Sint va)])))
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)])))
            (stack_update STR ''delegate_'' (kdata.Storage STR ''voters'' [Address xa])
            (stack_update STR ''delegate_'' (kdata.Storage STR '''' [])
            sa))))) this STR ''voters'' = Map x"
    and **: " state.Storage
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)],
               Address xa := sdata.Array [sdata.Value (Sint (wb + w)), sdata.Value (Bool False), sdata.Value (Address xa), sdata.Value (Sint va)])))
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)],
               Address xa := sdata.Array [sdata.Value (Sint wb), sdata.Value (Bool False), sdata.Value (Address xa), sdata.Value (Sint va)])))
            (storage_update STR ''voters'' (Map (voters
              (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)])))
            (stack_update STR ''delegate_'' (kdata.Storage STR ''voters'' [Address xa])
            (stack_update STR ''delegate_'' (kdata.Storage STR '''' [])
            sa))))) this STR ''proposals'' = sdata.Array y"
  show "(\<Sum>i = 0..length y. sum1 y i) \<le> (\<Sum>ad | \<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 x ad)"
  proof -
    from assms have "(\<Sum>i = 0..length proposals. sum1 proposals i) \<le> (\<Sum>ad | \<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 voters ad)" unfolding inv'_def sum1_def sum2_def by simp
    moreover have "(\<Sum>i = 0..length y. sum1 y i) = (\<Sum>i = 0..length proposals. sum1 proposals i)"
      using * ** assms by (simp add:wpsimps)
    moreover have "(\<Sum>ad | \<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 voters ad) \<le> (\<Sum>ad | \<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 x ad)"
    proof -
      have "(\<Sum>ad | (\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender. sum2 x ad) = (\<Sum>ad | (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender. sum2 voters ad)"
      proof (rule sum.mono_neutral_cong_right)
        show "finite {ad. (\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender}"  using finite finite_subset subset_UNIV by blast
        show "{ad. (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender}
              \<subseteq> {ad. (\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender}" using * by (auto simp add:wpsimps)
        show "\<forall>i\<in>{ad. (\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender} -
              {ad. (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender}.
              sum2 x i = 0"  using * by (auto simp add:wpsimps)
        show "\<And>x'. x' \<in> {ad. (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender} \<Longrightarrow> sum2 x x' = sum2 voters x'"  using * unfolding sum2_def by (auto simp add:wpsimps)
      qed
      moreover have "(\<Sum>ad | (\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender. sum2 x ad)
                     = (\<Sum>ad | (\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 x ad)" using * ** by (auto simp add:wpsimps)
      moreover have "(\<Sum>ad | (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)) \<and> ad \<noteq> xa) \<and> ad \<noteq> msg_sender. sum2 voters ad)
                     = (\<Sum>ad | (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 voters ad)" using assms(7) apply (simp add:wpsimps) unfolding sum2_def
        by (metis (no_types, lifting) nth_Cons_0 nth_Cons_Suc sdata.inject(2) sdata.sel(1) valtype.sel(1))
      ultimately have "(\<Sum>ad | (\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 x ad)
                    = (\<Sum>ad | (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 voters ad)" by simp
      moreover have "sum2 voters msg_sender = sum2 x msg_sender" using * assms unfolding sum2_def by (auto simp add:wpsimps)
      moreover have "(\<Sum>ad | \<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 voters ad)
                      = (\<Sum>ad | (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 voters ad)"
      proof -
        have "\<not> (\<exists>v. voters (Address msg_sender) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)))" using assms by (auto simp add:wpsimps)
        then have "(\<Sum>ad | \<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 voters ad) = 
                 (\<Sum>ad | (\<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 voters ad)" using sum_addr3[of msg_sender "{ad.  \<exists>v. voters (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))}" "sum2 voters"] by simp
        then show ?thesis by simp
      qed
      moreover have "(\<Sum>ad | \<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 x ad)
                      = (\<Sum>ad | (\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 x ad) + sum2 x msg_sender"
      proof -
        have "(\<exists>v. x (Address msg_sender) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)))" using assms * by (auto simp add:wpsimps)
        then have "(\<Sum>ad | \<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1)). sum2 x ad) = 
                   (\<Sum>ad | (\<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))) \<and> ad \<noteq> msg_sender. sum2 x ad) + sum2 x msg_sender" using sum_addr2[of msg_sender "{ad.  \<exists>v. x (Address ad) = sdata.Array v \<and> valtype.bool (sdata.vt (v ! 1))}" "sum2 x"] by simp
        then show ?thesis by simp
      qed
      ultimately show ?thesis by simp
    qed
    ultimately show ?thesis by simp
  qed
qed

lemma wp_assign_storage[wprule]:
  assumes "\<And>y. updateStore is (K (sdata.Value v)) (state.Storage s this i) = Some y \<Longrightarrow> P Empty (storage_update i y s)"
      and "updateStore ([] @ is) (K (sdata.Value v)) (state.Storage s this i) = None \<Longrightarrow> E Err s"
    shows "wp (assign_storage i is (rvalue.Value v)) P E s"
  apply vcg using assms by auto

lemma slookup_some[wpdrules]:
  assumes "proposals $ x \<bind> slookup [Sint 1] = Some yp"
  shows "x \<le> length proposals \<and> slookup [Sint 1] (proposals ! x) = Some yp"
  using assms unfolding nth_safe_def by (auto split:if_split_asm simp add:wpsimps)
    
lemma kdplus_safe_storage_none[wpsimps]:
  shows "kdplus_safe x (rvalue.Storage y z) = None"
  unfolding kdplus_safe_def by simp

lemma kdplus_safe_storage_some_false[wpdrules]:
  assumes "kdplus_safe x (rvalue.Storage y z) = Some a"
  shows "False"
  using assms by (simp add:wpsimps)

lemma winningProposal:
    fixes call:: "'a ballot \<Rightarrow> 'a expression_monad"
  assumes "effect (winningProposal call x) s r"
      and "inv_state sum_votes s"
    shows "inv r (inv_state sum_votes) (inv_state TT)"
  using assms
  apply (erule_tac inv_wp)
  unfolding winningProposal_def inv_state_def
  apply (wp)
  apply (wp)
  apply (wp)
  apply (rule_tac voters=voters and x="Address msg_sender" in obtain_voters,assumption)
  apply (auto simp add:wpsimps intro!:wprule dest!:wpdrules elim!:wperule)
  apply (rule_tac iv ="\<lambda>s'. state.Storage s' = state.Storage s
                \<and> (\<exists>x. (Stack s' $$ STR ''p'' = Some (kdata.Value (Sint x))))
                \<and> (\<exists>x. (Stack s' $$ STR ''winningVoteCount'' = Some (kdata.Value (Sint x))))
                \<and> (\<exists>x. (Stack s' $$ STR ''winningProposalu'' = Some (kdata.Value (Sint x))))" in wpwhile)
  apply (auto simp add:wpsimps intro!:wprule dest!:wpdrules elim!:wperule)
  apply (auto simp add:wpsimps)[1]
  apply (rule_tac voters=voters and proposals=a in sum_votesI,assumption)
  by (simp add:wpsimps)+

lemma vote:
    fixes call:: "'a ballot \<Rightarrow> 'a expression_monad"
  assumes "effect (vote call x) s r"
      and "inv_state sum_votes s"
    shows "inv r (inv_state sum_votes) (inv_state TT)"
  using assms
  apply (erule_tac inv_wp)
  unfolding vote_def inv_state_def
  apply (wp)
  apply (wp)
  apply (wp)
  apply (rule_tac voters=voters and x="Address msg_sender" in obtain_voters,assumption)
  by (auto simp add:wpsimps intro!: wprule)+

lemma kdequals2[wpdrules]:
  assumes "kdequals x y = Some (rvalue.Value (Bool True))"
  shows "x = y"
  using assms
  apply (cases x;simp add: kdequals_def)
  apply (cases y;simp add: kdequals_def)
  by (case_tac x4;case_tac x4a;simp add: kdequals_def)

lemma wp_less_monad[wprule]:
  assumes "wp lm (\<lambda>a. wp (rm \<bind> (\<lambda>rv. option Err (K (kdless a rv)) \<bind> return)) P E) E s"
  shows "wp (less_monad lm rm) P E s"
  unfolding less_monad_def apply (rule wp_lift_op_monad) using assms .

lemma kdnot_true:
  assumes "kdnot y = Some (rvalue.Value (Bool True))"
  shows "y=rvalue.Value (Bool False)"
  using assms apply (cases y;simp add:assms kdnot_def)
  by (case_tac x4;simp add:assms vtnot_def)

lemma list_update_safe_simps1[wpsimps]:
  assumes "i < length xs"
  shows "list_update_safe xs i a = Some (list_update xs i a)"
  unfolding list_update_safe_def using assms by simp

lemma delegate:
    fixes call:: "'a ballot \<Rightarrow> 'a expression_monad"
  assumes "effect (delegate call x) s r"
      and "inv_state sum_votes s"
    shows "inv r (inv_state sum_votes) (inv_state TT)"
  using assms
  apply (erule_tac inv_wp)
  unfolding delegate_def inv_state_def
  apply wp
  apply wp
  apply wp
  apply (rule_tac voters=voters and x="Address msg_sender" in obtain_voters,assumption)
  apply (wp)+
  apply (auto simp add:wpsimps intro!: wpthrow)
  apply (rule_tac iv ="\<lambda>s'. state.Storage s' this STR ''voters'' = state.Storage s this STR ''voters'' \<and>
                            state.Storage s' this STR ''proposals'' = state.Storage s this STR ''proposals'' \<and>
                            state.Storage s' this STR ''chairperson'' = state.Storage s this STR ''chairperson'' \<and>
                            state.Stack s' $$ (STR ''sender'') = Some (kdata.Storage STR ''voters'' [Address msg_sender]) \<and>
                            (\<exists>x. (Stack s' $$ STR ''to'' = Some (kdata.Value (Address x)) \<and> x \<noteq> msg_sender))"  in wpwhile)
  apply (wp)+
  apply (auto simp add:wpsimps intro!: wpthrow)
  apply (wp)+
  apply (auto simp add:wpsimps intro!: wpthrow)
  apply (rule_tac voters=voters and x="Address xa" in obtain_voters,assumption)
  apply (auto simp add:wpsimps sender_neq_null intro!: wpthrow)[1]
  apply (rule_tac voters=voters and x="Address xa" in obtain_voters,assumption)
  apply (wp)+
  apply (auto simp add:wpsimps intro!: wpthrow)
  apply (wp)+
  apply (auto simp add:wpsimps intro!: wpthrow)
  apply (rule_tac voters="voters
              (Address msg_sender := sdata.Array [sdata.Value (Sint w), sdata.Value (Bool True), sdata.Value (Address d), sdata.Value (Sint v)],
               Address xa := sdata.Array [sdata.Value (Sint (wa + w)), sdata.Value (Bool False), sdata.Value (Address xa), sdata.Value (Sint va)])" in sum_votesI)
  apply (auto simp add:wpsimps intro!: wpthrow)
  apply (rule inv_1;assumption)
  apply (rule_tac voters=voters and x="Address xa" in obtain_voters,assumption)
  apply (wp)+
  apply (auto simp add:wpsimps intro!: wpthrow)
  apply (auto simp add:wpsimps dest: kdnot_true kdequals_false)[1]
  done

lemma sym2[wpdrules]:
  assumes "sdata.Value v = y"
    shows "y = sdata.Value v"
  using assms by simp

lemma giveRightToVote:
    fixes call:: "'a ballot \<Rightarrow> 'a expression_monad"
  assumes "effect (giveRightToVote call x) s r"
      and "inv_state sum_votes s"
    shows "inv r (inv_state sum_votes) (inv_state TT)"
  using assms
  apply (erule_tac inv_wp)
  unfolding giveRightToVote_def inv_state_def
  apply (wp | auto simp add:wpsimps)+
  apply (rule_tac voters=voters and x="Address x" in obtain_voters,assumption)
  apply (wp | auto simp add:wpsimps)+
  apply (rule_tac voters="voters(Address x := sdata.Array [sdata.Value (Sint 1), sdata.Value (Bool False), sdata.Value (Address d), sdata.Value (Sint v)])" in sum_votesI)
  apply (wp | auto simp add:wpsimps)+
  apply (rule inv_0;assumption)
  apply (wp | auto simp add:wpsimps)+
  apply (rule_tac voters=voters and x="Address x" in obtain_voters,assumption)
  by (wp | auto simp add:wpsimps)+

invariant sum_votes: sum_votes "TT::(String.literal \<Rightarrow> 'a sdata) \<times> nat \<Rightarrow> bool" for Ballot
  apply -
  using constructor_ballot apply blast
  using giveRightToVote apply blast
  using delegate apply blast
  using vote apply blast
  using winningProposal apply blast
  done

end

end