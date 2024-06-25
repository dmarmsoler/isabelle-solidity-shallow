theory Utils
imports
  Main
  "HOL-Library.Finite_Map"
  "HOL-Library.Monad_Syntax"
begin

fun fold_map where
    "fold_map _ [] y = ([], y)"
  | "fold_map f (x # xs) y =
      (let (x', y') = f x y in
       (let (xs', y'') = fold_map f xs y'
      in (x' # xs', y'')))"

lemma fold_map_cong [fundef_cong]:
  "a = b \<Longrightarrow> xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x)
    \<Longrightarrow> fold_map f xs a = fold_map g ys b"
  by (induct ys arbitrary: a b xs) simp_all

definition length_append where "length_append m x = (length m, m@[x])"

primrec ofold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b option) \<Rightarrow> 'a list \<Rightarrow> 'b \<Rightarrow> 'b option" where
  fold_Nil:  "ofold f [] = Some" |
  fold_Cons: "ofold f (x # xs) b = ofold f xs b \<bind> f x"

lemma ofold_cong [fundef_cong]:
  "a = b \<Longrightarrow> xs = ys \<Longrightarrow> (\<And>x. x \<in> set xs \<Longrightarrow> f x = g x)
    \<Longrightarrow> ofold f xs a = ofold g ys b"
  by (induct ys arbitrary: a b xs) simp_all

fun K where "K f _ = f"

fun append (infixr "@@" 65) where "append xs x = xs @ [x]"

abbreviation case_list where "case_list l a b \<equiv> List.case_list a b l"

definition nth_safe :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" (infixl "$" 100)
  where "nth_safe xs i = (if i < length xs then Some (xs!i) else None)"

lemma nth_safe_some[simp]: "i < length xs \<Longrightarrow> xs $ i = Some (xs!i)" unfolding nth_safe_def by simp
lemma nth_safe_none[simp]: "i \<ge> length xs \<Longrightarrow> xs $ i = None" unfolding nth_safe_def by simp
lemma nth_safe_length: "xs $ i = Some x \<Longrightarrow> i < length xs" unfolding nth_safe_def by (simp split: if_split_asm)

definition list_update_safe :: "'a list \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> ('a list) option"
  where "list_update_safe xs i a = (if i < length xs then Some (list_update xs i a) else None)"

section \<open>Some Basic Lemmas for Finite Maps\<close>

lemma fmfinite: "finite ({(ad, x). fmlookup y ad = Some x})"
proof -
  have "{(ad, x). fmlookup y ad = Some x} \<subseteq> dom (fmlookup y) \<times> ran (fmlookup y)"
  proof
    fix x assume "x \<in> {(ad, x). fmlookup y ad = Some x}"
    then have "fmlookup y (fst x) = Some (snd x)" by auto
    then have "fst x \<in> dom (fmlookup y)" and "snd x \<in> ran (fmlookup y)" using Map.ranI by (blast,metis)
    then show "x \<in> dom (fmlookup y) \<times> ran (fmlookup y)" by (simp add: mem_Times_iff)
  qed
  thus ?thesis by (simp add: finite_ran finite_subset)
qed

lemma fmlookup_finite:
  fixes f :: "'a \<Rightarrow> 'a"
    and y :: "('a, 'b) fmap"
  assumes "inj_on (\<lambda>(ad, x). (f ad, x)) {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
  shows "finite {(ad, x). (fmlookup y \<circ> f) ad = Some x}"
proof (cases rule: inj_on_finite[OF assms(1), of "{(ad, x)|ad x. (fmlookup y) ad = Some x}"])
  case 1
  then show ?case by auto
next
  case 2
  then have *: "finite {(ad, x) |ad x. fmlookup y ad = Some x}" using fmfinite[of y] by simp
  show ?case using finite_image_set[OF *, of "\<lambda>(ad, x). (ad, x)"] by simp
qed

section "Address class with example instantiation"

class address = finite +
  fixes null :: 'a

definition aspace_carrier where "aspace_carrier={0::nat, 1, 2, 3, 4, 5, 6, 7, 8, 9}"

lemma aspace_carrier_finite: "finite aspace_carrier" unfolding aspace_carrier_def by simp

typedef aspace = aspace_carrier
  unfolding aspace_carrier_def
  by (rule_tac x = 0 in exI) simp

setup_lifting type_definition_aspace

lift_definition A0 :: aspace is 0 unfolding aspace_carrier_def by simp
lift_definition A1 :: aspace is 1 unfolding aspace_carrier_def by simp
lift_definition A2 :: aspace is 2 unfolding aspace_carrier_def by simp
lift_definition A3 :: aspace is 3 unfolding aspace_carrier_def by simp
lift_definition A4 :: aspace is 4 unfolding aspace_carrier_def by simp
lift_definition A5 :: aspace is 5 unfolding aspace_carrier_def by simp
lift_definition A6 :: aspace is 6 unfolding aspace_carrier_def by simp
lift_definition A7 :: aspace is 7 unfolding aspace_carrier_def by simp
lift_definition A8 :: aspace is 8 unfolding aspace_carrier_def by simp
lift_definition A9 :: aspace is 9 unfolding aspace_carrier_def by simp

lemma aspace_finite: "finite (UNIV::aspace set)"
  using finite_imageI[OF aspace_carrier_finite, of Abs_aspace]
    type_definition.Abs_image[OF type_definition_aspace] by simp

lemma A1_neq_A0[simp]: "A1 \<noteq> A0"
  by transfer simp

instantiation aspace :: address
begin
  definition null_def: "null = A0"
  instance proof
    show "finite (UNIV::aspace set)" using aspace_finite by simp
  qed
end

instantiation aspace :: equal
begin

definition "HOL.equal (x::aspace) y \<longleftrightarrow> Rep_aspace x = Rep_aspace y"

instance apply standard by(simp add: Rep_aspace_inject equal_aspace_def)

end

section "Common lemmas for sums"

lemma sum_addr:
  fixes f::"('a::address)\<Rightarrow>nat"
  shows "(\<Sum>ad\<in>UNIV. f ad) = (\<Sum>ad|ad \<noteq> addr. f ad) + f addr"
proof -
  have "finite {ad \<in> UNIV. ad \<noteq> addr}" and "finite {ad \<in> UNIV. ad = addr}" using finite by simp+
  moreover have "UNIV = {ad \<in> UNIV. ad \<noteq> addr} \<union> {ad \<in> UNIV. ad = addr}" by auto
  moreover have "{ad \<in> UNIV. ad \<noteq> addr} \<inter> {ad \<in> UNIV. ad = addr} = {}" by auto
  ultimately have "sum f UNIV = sum f {ad \<in> UNIV. ad \<noteq> addr} + sum f {ad \<in> UNIV. ad = addr}"
    using sum_Un_nat[of "{ad\<in>UNIV. ad \<noteq> addr}" "{ad\<in>UNIV. ad = addr}" f] by simp
  moreover have "sum f {ad \<in> UNIV. ad = addr} = f addr" by simp
  ultimately show ?thesis by simp
qed

lemma sum_addr2:
  fixes f::"'a::address\<Rightarrow>nat"
  assumes "addr \<in> A"
  shows "(\<Sum>ad\<in>A. f ad) = (\<Sum>ad|ad\<in>A \<and> ad \<noteq> addr. f ad) + f addr"
proof -
  have "finite {ad \<in> A. ad \<noteq> addr}" and "finite {ad \<in> A. ad = addr}" using finite by simp+
  moreover have "A = {ad \<in> A. ad \<noteq> addr} \<union> {ad \<in> A. ad = addr}" by auto
  moreover have "{ad \<in> A. ad \<noteq> addr} \<inter> {ad \<in> A. ad = addr} = {}" by auto
  ultimately have "(\<Sum>ad\<in>A. f ad) = (\<Sum>ad|ad\<in>A \<and> ad \<noteq> addr. f ad) + (\<Sum>ad|ad\<in>A \<and> ad = addr. f ad)"
    using sum_Un_nat[of "{ad\<in>A. ad \<noteq> addr}" "{ad\<in>A. ad = addr}" f] by simp
  moreover have "{ad \<in> A. ad = addr} = {addr}" using assms by auto
  then have "sum f {ad \<in> A. ad = addr} = f addr" by simp
  ultimately show ?thesis by simp
qed

lemma sum_addr3:
  fixes f::"'a::address\<Rightarrow>nat"
  assumes "addr \<notin> A"
  shows "(\<Sum>ad\<in>A. f ad) = (\<Sum>ad|ad\<in>A \<and> ad \<noteq> addr. f ad)"
proof -
  have "finite {ad \<in> A. ad \<noteq> addr}" and "finite {ad \<in> A. ad = addr}" using finite by simp+
  moreover have "A = {ad \<in> A. ad \<noteq> addr} \<union> {ad \<in> A. ad = addr}" by auto
  moreover have "{ad \<in> A. ad \<noteq> addr} \<inter> {ad \<in> A. ad = addr} = {}" by auto
  ultimately have "(\<Sum>ad\<in>A. f ad) = (\<Sum>ad|ad\<in>A \<and> ad \<noteq> addr. f ad) + (\<Sum>ad|ad\<in>A \<and> ad = addr. f ad)"
    using sum_Un_nat[of "{ad\<in>A. ad \<noteq> addr}" "{ad\<in>A. ad = addr}" f] by simp
  moreover have "{ad \<in> A. ad = addr} = {}" using assms by simp
  then have "sum f {ad \<in> A. ad = addr} = 0" by simp
  ultimately show ?thesis by simp
qed

end