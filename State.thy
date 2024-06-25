theory State
imports Finite_Map_Extras Utils "HOL-Library.Word"
begin

section \<open>Value Types\<close>

subsection \<open>Definition\<close>

type_synonym bytes = String.literal
type_synonym id = String.literal

datatype ('a::address) valtype =
  Bool (bool: bool)
| Sint (sint: "256 word")
| Address 'a
| Bytes bytes

subsection \<open>Default values\<close>

definition sint where "sint = Sint 0"

definition bytes where "bytes = Bytes (STR ''0000000000000000000000000000000000000000000000000000000000000000'')"

definition address where "address = Address null"

definition bool where "bool = Bool False"

definition mapping where "mapping x = (\<lambda>_. x)"

subsection \<open>Common functions\<close>

fun lift_bool_unary::"(bool \<Rightarrow> bool) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_bool_unary op (Bool b) = Some (Bool (op b))"
| "lift_bool_unary _ _ = None"

definition vtnot where
  "vtnot = lift_bool_unary Not"

fun lift_bool_binary::"(bool \<Rightarrow> bool \<Rightarrow> bool) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_bool_binary op (Bool l) (Bool r) = Some (Bool (op l r))"
| "lift_bool_binary _ _ _ = None"

definition vtand where
  "vtand = lift_bool_binary (\<and>)"

definition vtor where
  "vtor = lift_bool_binary (\<or>)"

fun vtequals where
  "vtequals (Sint l) (Sint r) = Some (Bool (l = r))"
| "vtequals (Address l) (Address r) = Some (Bool (l = r))"
| "vtequals (Bool l) (Bool r) = Some (Bool (l = r))"
| "vtequals (Bytes l) (Bytes r) = Some (Bool (l = r))"
| "vtequals _ _ = None"

fun lift_int_comp::"(256 word \<Rightarrow> 256 word \<Rightarrow> bool) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_int_comp op (Sint l) (Sint r) = Some (Bool (op l r))"
| "lift_int_comp _ _ _ = None"

definition vtless where
  "vtless = lift_int_comp (<)"

fun lift_int_binary::"(256 word \<Rightarrow> 256 word \<Rightarrow> 256 word) \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "lift_int_binary op (Sint l) (Sint r) = Some (Sint (op l r))"
| "lift_int_binary _ _ _ = None"

definition vtplus where
  "vtplus = lift_int_binary (+)"

fun vtplus_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtplus_safe (Sint l) (Sint r) = (if unat l + unat r < 2^256 then Some (Sint (l + r)) else None)"
| "vtplus_safe _ _ = None"

declare vtplus_safe.simps[simp del]

definition vtminus where
  "vtminus = lift_int_binary (-)"

fun vtminus_safe::"('a::address) valtype \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) valtype option" where
  "vtminus_safe (Sint l) (Sint r) = (if r \<le> l then Some (Sint (l - r)) else None)"
| "vtminus_safe _ _ = None"

declare vtminus_safe.simps[simp del]

definition vtmult where
  "vtmult = lift_int_binary (*)"

definition vtmod where
  "vtmod = lift_int_binary (mod)"

subsection \<open>Examples\<close>

definition "vt_true = Bool True"
definition "vt_false = Bool False"
definition "vt_sint_m10 = Sint (-10)"
definition "vt_sint_1 = Sint 1"
definition "vt_sint_2 = Sint 2"
definition "vt_sint_10 = Sint 10"
definition "vt_address = Address null"

section \<open>Storage\<close>

subsection \<open>Definition\<close>

subsubsection \<open>Definition\<close>

datatype ('a::address) sdata =
  is_Value: Value (vt:"('a::address) valtype")
| is_Array: Array (ar: "('a::address) sdata list")
| is_Map: Map (mp: "('a::address) valtype \<Rightarrow> ('a::address) sdata")

abbreviation storage_check where "storage_check sd vf af mf \<equiv> case_sdata vf af mf sd"

subsubsection \<open>Examples\<close>

definition "sd_true = Value vt_true"
definition "sd_false = Value vt_false"
definition "sd_sint8_m10 = Value vt_sint_m10"
definition "sd_uint8_10 = Value vt_sint_10"
definition "sd_address = Value vt_address"
definition "(sd_Array_3_true::aspace sdata) = Array [sd_true,sd_true,sd_true]"
definition "(sd_Array_3_false::aspace sdata) = Array [sd_false,sd_false,sd_false]"
definition "(sd_Array_2_3_true_false::aspace sdata) = Array [sd_Array_3_true, sd_Array_3_false]"
definition "(sd_Array_2_3_false_false::aspace sdata) = Array [sd_Array_3_false, sd_Array_3_false]"

subsection \<open>Lookup\<close>

subsubsection \<open>Definition\<close>

text \<open>
  slookup is sd navigates storage sd according to the index sequence is.
\<close>
fun slookup :: "('a::address) valtype list \<Rightarrow> ('a::address) sdata \<Rightarrow> ('a::address) sdata option" where
  "slookup [] s = Some s"
| "slookup (valtype.Sint i # is) (sdata.Array xs) = xs $ unat i \<bind> slookup is"
| "slookup (i # is) (Map f) = slookup is (f i)"
| "slookup _ _ = None"

subsubsection \<open>Examples\<close>

lemma "P (slookup [vt_sint_1, vt_sint_2::aspace valtype] sd_Array_2_3_true_false) = P (Some (Value (Bool False)))"
  by normalization

subsection \<open>Update\<close>

subsubsection \<open>Definition\<close>

fun updateStore :: "('a::address) valtype list \<Rightarrow> (('a::address) sdata \<Rightarrow> ('a::address) sdata) \<Rightarrow> ('a::address) sdata \<Rightarrow> ('a::address) sdata option" where
  "updateStore [] f v = Some (f v)"
| "updateStore (valtype.Sint i # is) f (sdata.Array xs) = xs $ (unat i) \<bind> updateStore is f \<bind> list_update_safe xs (unat i) \<bind> Some \<circ> sdata.Array"
| "updateStore (i # is) f (Map m) = updateStore is f (m i) \<bind> Some \<circ> sdata.Map \<circ> fun_upd m i"
| "updateStore _ _ _ = None"

subsubsection \<open>Examples\<close>

lemma "P (updateStore [vt_sint_1,vt_sint_2] (K sd_true) sd_Array_2_3_true_false)
  = P (Some (Array [Array [Value (Bool True), Value (Bool True), Value (Bool True)], Array [Value (Bool False), Value (Bool False), Value (Bool True)]]))"
  by normalization

section \<open>Memory\<close>

subsection \<open>Definition\<close>

subsubsection \<open>Definition\<close>

type_synonym location = nat

datatype ('a::address) mdata =
  is_Value: Value (vt: "('a::address) valtype")
| is_Array: Array (ar: "location list")

definition case_memory where
  "case_memory m l vf af \<equiv>
    (case m$l of
      Some (mdata.Value v) \<Rightarrow> vf v
    | Some (mdata.Array xs) \<Rightarrow> af xs
    | None \<Rightarrow> None)"

lemma case_memory_cong[fundef_cong]:
  assumes "\<And>v. m$l = Some (mdata.Value v) \<Longrightarrow> vf1 v = vf2 v"
      and "\<And>xs. m$l = Some (mdata.Array xs) \<Longrightarrow> af1 xs = af2 xs"
    shows "case_memory m l vf1 af1 = case_memory m l vf2 af2"
  unfolding case_memory_def using assms by (simp split: option.split mdata.split) 

subsubsection \<open>Examples\<close>

definition "md_true = Value vt_true"
definition "md_false = Value vt_false"
definition "md_sint_m10 = Value vt_sint_m10"
definition "md_uint_10 = Value vt_sint_10"
definition "md_address = Value vt_address"

type_synonym 'a memory = "'a mdata list"
definition "mem_Array_2_3_true_false = [md_true,md_true,md_true,Array [0,1,2],md_false,md_false,md_false,Array [4,5,6],Array [3,7]]"
definition "mem_Array_2_3_false_false = [md_false,md_false,md_false,Array [0,1,2],md_false,md_false,md_false,Array [4,5,6],Array [3,7]]"
definition "mem_sint_m10_uint_10= [md_sint_m10,md_uint_10]"

subsection \<open>Lookup\<close>

subsubsection \<open>Definition\<close>

fun marray_lookup :: "('a::address) memory \<Rightarrow> ('a::address) valtype list \<Rightarrow> location \<Rightarrow> (location \<times> location list \<times> nat) option" where
  "marray_lookup _ [] _  = None"
| "marray_lookup m [Sint i] l =
    case_memory m l
      (K None)
      (\<lambda>xs. Some (l, xs, unat i))"
| "marray_lookup m (Sint i # is) l =
    case_memory m l
      (K None)
      (\<lambda>xs. xs $ unat i \<bind> marray_lookup m is)"
| "marray_lookup _ _ _ = None"

fun mlookup :: "('a::address) memory \<Rightarrow> ('a::address) valtype list \<Rightarrow> location \<Rightarrow> (location \<times> ('a::address) mdata) option" where
  "mlookup m [] l = m $ l \<bind> (\<lambda>v. Some (l,v))"
| "mlookup m xs l = marray_lookup m xs l \<bind> (\<lambda>(_, xs', i). nth_safe m (xs'!i) \<bind> (\<lambda>v. Some (xs'!i,v)))"

fun update::"('a::address) memory \<Rightarrow> location \<Rightarrow> (location \<times> location list \<times> nat) \<Rightarrow> ('a::address) memory" where
"update m l' (l, ls, n) = m[l:=mdata.Array (ls[n:=l'])]"

fun marray_update :: "('a::address) valtype list \<Rightarrow> location \<Rightarrow> location \<Rightarrow> ('a::address) memory \<Rightarrow> ('a::address) memory option" where
  "marray_update xs l l' m = marray_lookup m xs l \<bind> Some \<circ> update m l'"

fun mvalue_update :: "('a::address) valtype list \<Rightarrow> location \<Rightarrow> ('a::address) valtype \<Rightarrow> ('a::address) memory \<Rightarrow> ('a::address) memory option" where
  "mvalue_update xs l v m = marray_lookup m xs l \<bind> (\<lambda>(x, ls, i). ls$i \<bind> (\<lambda>i'. Some (list_update m i' (mdata.Value v))))"

subsubsection \<open>Examples\<close>

lemma "mlookup mem_Array_2_3_true_false [Sint 1, Sint 2] 8 = Some (6, mdata.Value (Bool False))" by normalization

lemma "mlookup mem_Array_2_3_true_false [Sint 0] 8 = Some (3, mdata.Array [0, 1, 2])" by normalization

lemma "marray_update [Sint 1, Sint 2] 8 2 mem_Array_2_3_true_false = Some (mem_Array_2_3_true_false[7:=mdata.Array [4, 5, 2]])" by normalization

section \<open>Calldata\<close>

subsection \<open>Definition\<close>

subsubsection \<open>Definition\<close>

datatype ('a::address) cdata =
  is_Value: Value (vt: "('a::address) valtype")
| is_Array: Array (ar: "('a::address) cdata list")

abbreviation case_cdata where "case_cdata cd vf af \<equiv> cdata.case_cdata vf af cd"

subsubsection \<open>Examples\<close>

definition "cd_true = Value vt_true"
definition "cd_false = Value vt_false"
definition "cd_sint8_m10 = Value vt_sint_m10"
definition "cd_uint8_10 = Value vt_sint_10"
definition "cd_address = Value vt_address"
definition "cd_Array_3_true = Array [cd_true,cd_true,cd_true]"
definition "cd_Array_3_false = Array [cd_false,cd_false,cd_false]"
definition "cd_Array_2_3_true_false = Array [cd_Array_3_true, cd_Array_3_false]"
definition "cd_Array_2_3_false_false = Array [cd_Array_3_false, cd_Array_3_false]"

subsection \<open>Lookup\<close>

subsubsection \<open>Definition\<close>

text \<open>
  clookup is cd navigates calldata cd according to the index sequence is.
\<close>
fun clookup :: "('a::address) valtype list \<Rightarrow> ('a::address) cdata \<Rightarrow> ('a::address) cdata option" where
  "clookup [] s = Some s"
| "clookup (valtype.Sint i # is) (cdata.Array xs) = xs $ unat i \<bind> clookup is"
| "clookup _ _ = None"

subsubsection \<open>Examples\<close>

lemma "clookup [vt_sint_1, vt_sint_2] cd_Array_2_3_true_false = Some (cdata.Value (Bool False))" by normalization

subsection \<open>Update\<close>

subsubsection \<open>Definition\<close>

fun updateCalldata :: "('a::address) valtype list \<Rightarrow> ('a::address) cdata \<Rightarrow> ('a::address) cdata \<Rightarrow> ('a::address) cdata option" where
  "updateCalldata [] v _ = Some v"
| "updateCalldata (valtype.Sint i # is) v (cdata.Array xs) = (xs $ (unat i) \<bind> updateCalldata is v) \<bind> Some \<circ> cdata.Array \<circ> list_update xs (unat i)"
| "updateCalldata _ _ _ = None"

subsubsection \<open>Examples\<close>

lemma "updateCalldata [vt_sint_1, vt_sint_2::aspace valtype] cd_true cd_Array_2_3_true_false =
  Some (cdata.Array [cd_Array_3_true, cdata.Array [cd_false, cd_false, cd_true]])"
  by (normalization)

section \<open>Initialize Memory\<close>

function minit :: "('a::address) cdata \<Rightarrow> ('a::address) memory \<Rightarrow> nat \<times> ('a::address) memory" where
  "minit (cdata.Value x) m = length_append m (mdata.Value x)"
| "minit (cdata.Array ds) m = (let (ns, m') = fold_map minit ds m in (length_append m' (mdata.Array ns)))"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(s,b). size (s))") apply auto
  by (meson Suc_n_not_le_n leI size_list_estimation')

lemma "minit (cdata.Array [cdata.Value (Sint 0), cdata.Value (Sint 0), cdata.Value (Sint 0)]) ([]::aspace mdata list)
      = (3, [mdata.Value (Sint 0), mdata.Value (Sint 0), mdata.Value (Sint 0), mdata.Array [0, 1, 2]])"
  by eval

section \<open>Copy Between Stores\<close>

subsection \<open>Termination Lemmas\<close>

lemma card_less_card:
  assumes "m $ p1 = Some a"
      and "p1 |\<notin>| s1"
    shows "card ({0..length m} - insert p1 (fset s1)) < card ({0..length m} - fset s1)"
proof -
  have "card ({0..length m} - insert p1 (fset s1)) = card ({0..length m}) - card ({0..length m} \<inter> insert p1 (fset s1))"
   and "card ({0..length m} - fset s1) = card ({0..length m}) - card ({0..length m} \<inter> (fset s1))" by (rule card_Diff_subset_Int, simp)+
  moreover from assms(2) have "card ({0..length m} \<inter> insert p1 (fset s1)) = Suc (card ({0..length m} \<inter> (fset s1)))" using nth_safe_length[OF assms(1)] by simp
  moreover have "card ({0..length m}) \<ge> card ({0..length m} \<inter> insert p1 (fset s1))" by (rule card_mono, auto)
  ultimately show ?thesis by simp
qed

subsection \<open>Copy from Memory to Storage\<close>

subsubsection \<open>Definition\<close>

function copy_memory_storage_safe :: "location fset \<Rightarrow> ('a::address) memory \<Rightarrow> location \<Rightarrow> ('a::address) sdata option" where
  "copy_memory_storage_safe s m l = 
   (if l |\<in>| s then None else
      case_memory m l
        (\<lambda>v. Some (sdata.Value v))
        (\<lambda>xs. those (map (copy_memory_storage_safe (finsert l s) m) xs) \<bind> Some \<circ> sdata.Array))"
by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(s,m,_). card ({0..length m} - fset s))")
  using card_less_card by auto

definition "copy_memory_storage = copy_memory_storage_safe {||}"

subsubsection \<open>Examples\<close>

lemma "P (copy_memory_storage mem_Array_2_3_true_false 8) = P (Some sd_Array_2_3_true_false)" by normalization

subsection \<open>Copy from Memory to Calldata\<close>

subsubsection \<open>Definition\<close>

(*This is similar to memory storage. Can we use a type class to abstract it?*)
function copy_memory_calldata_safe :: "location fset \<Rightarrow> ('a::address) memory \<Rightarrow> location \<Rightarrow> ('a::address) cdata option" where
  "copy_memory_calldata_safe s m l = 
   (if l |\<in>| s then None else
      case_memory m l
        (\<lambda>v. Some (cdata.Value v))
        (\<lambda>xs. those (map (copy_memory_calldata_safe (finsert l s) m) xs) \<bind> Some \<circ> cdata.Array))"
by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(s,m,_). card ({0..length m} - fset s))")
  using card_less_card by auto

definition "copy_memory_calldata = copy_memory_calldata_safe {||}"

subsubsection \<open>Examples\<close>

lemma "P (copy_memory_storage mem_Array_2_3_true_false 8) = P (Some sd_Array_2_3_true_false)" by normalization

subsection \<open>Copy from Storage to Memory\<close>

subsubsection \<open>Definition\<close>

function copy_storage_memory :: "(('a::address) sdata \<times> location) \<Rightarrow> ('a::address) memory \<Rightarrow> ('a::address) memory option" where
  "copy_storage_memory (sdata.Value v, l) m = list_update_safe m l (mdata.Value v)"
| "copy_storage_memory (sdata.Array xs, l) m =
    case_memory m l
      (K None)
      (\<lambda>ys. if length xs = length ys then ofold copy_storage_memory (zip xs ys) m else None)"
| "copy_storage_memory (sdata.Map _, _) _ = None"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(s,b). size (fst s))") apply auto
  by (metis less_irrefl_nat not_less_eq set_zip_leftD size_list_estimation)

subsubsection \<open>Examples\<close>

lemma "P (copy_storage_memory (sd_Array_2_3_true_false, 8) mem_Array_2_3_false_false) = P (Some (mem_Array_2_3_true_false))" by normalization


subsection \<open>Copy from Calldata to Memory\<close>

subsection \<open>Definition\<close>

function copy_calldata_memory :: "(('a::address) cdata \<times> location) \<Rightarrow> ('a::address) memory \<Rightarrow> ('a::address) memory option" where
  "copy_calldata_memory (cdata.Value v, l) m = list_update_safe m l (mdata.Value v)"
| "copy_calldata_memory (cdata.Array xs, l) m =
    case_memory m l
      (K None)
      (\<lambda>ys. if length xs = length ys then ofold copy_calldata_memory (zip xs ys) m else None)"
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(s,b). size (fst s))") apply auto
  by (metis less_irrefl_nat not_less_eq set_zip_leftD size_list_estimation)

fun copy_calldata_storage :: "('a::address) cdata \<Rightarrow> ('a::address) sdata" where
  "copy_calldata_storage (cdata.Value v) = sdata.Value v"
| "copy_calldata_storage (cdata.Array xs) = sdata.Array (map copy_calldata_storage xs)"

subsection \<open>Examples\<close>

section \<open>Stack\<close>

subsection \<open>Definition\<close>

datatype ('a::address) kdata =
  Storage id "('a::address) valtype list" |
  Memory location |
  Calldata id "('a::address) valtype list" |
  Value (vt: "('a::address) valtype")

section \<open>State\<close>

subsection \<open>Definition\<close>

subsubsection \<open>Definition\<close>

type_synonym 'a stack = "(id, 'a kdata) fmap"
type_synonym 'a balances = "'a \<Rightarrow> nat"
type_synonym 'a storage = "'a \<Rightarrow> id \<Rightarrow> 'a sdata"
type_synonym 'a calldata = "(id, 'a cdata) fmap"

record ('a::address) state =
  Memory:: "('a::address) memory"
  Calldata:: "('a::address) calldata"
  Storage:: "('a::address) storage"
  Stack:: "('a::address) stack"
  Balances::"('a::address) balances"

subsection \<open>Update Function\<close>

datatype ex = Err

definition balances_update:: "('a::address) \<Rightarrow> nat \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "balances_update i n s = s\<lparr>Balances := (Balances s)(i := n)\<rparr>"

definition calldata_update:: "id \<Rightarrow> ('a::address) cdata \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "calldata_update i d = Calldata_update (fmupd i d)"

definition stack_update:: "id \<Rightarrow> ('a::address) kdata \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "stack_update i d = Stack_update (fmupd i d)"

definition memory_update:: "location \<Rightarrow> ('a::address) mdata \<Rightarrow> ('a::address) state \<Rightarrow> ('a::address) state" where
  "memory_update i d s = s\<lparr>Memory := (Memory s)[i := d]\<rparr>"

end