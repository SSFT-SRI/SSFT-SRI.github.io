(* incomplete, see solutions.zip for a complete version *)

theory Reg
imports Main
begin

-- {* conc, star, alt, letter, not *}

datatype reg =
  Letter char |
  Conc reg reg |
  Alt reg reg |
  Star reg |
  Not reg

term "{f x | x. P x}"

definition
  "conc l1 l2 = {xs @ ys | xs ys. xs \<in> l1 \<and> ys \<in> l2}"

inductive_set star :: "string set \<Rightarrow> string set" for L
where
   "[] \<in> star L" |
   "\<lbrakk> xs \<in> L; ys \<in> star L \<rbrakk> \<Longrightarrow> xs @ ys \<in> star L"

fun lang :: "reg \<Rightarrow> string set"
where
"lang (Letter c) = {[c]}" |
"lang (Alt r1 r2) = lang r1 \<union> lang r2" |
"lang (Conc r1 r2) = conc (lang r1) (lang r2)" |
"lang (Star r1) = star (lang r1)" |
"lang (Not r) = (-(lang r))"

term "x :: char"

definition
  "U = Alt (Letter CHR ''x'') (Not (Letter CHR ''x''))"

definition
  "E = Not U"

thm U_def

lemma [simp]: "lang U = UNIV"
  by (auto simp: U_def)

lemma [simp]: "lang E = {}"
  by (simp add: E_def)

fun reverse :: "reg \<Rightarrow> reg"
where
"reverse (Letter x) = Letter x" |
"reverse (Conc r1 r2) = Conc (reverse r2) (reverse r1)" |
"reverse (Alt r1 r2) = Alt (reverse r1) (reverse r2)" |
"reverse (Star r) = Star (reverse r)" |
"reverse (Not r) = Not (reverse r)"

definition
  "epsilon = Star E"

fun String :: "string \<Rightarrow> reg"
where
"String [] = epsilon" |
"String (x # xs) = Conc (Letter x) (String xs)"

lemma [simp]: "reverse epsilon = epsilon"
  by (simp add: epsilon_def E_def U_def)

lemma [simp]: "lang epsilon = {[]}" sorry

lemma "lang (reverse (Not (String ''abc''))) = lang (Not (String ''cba''))"
apply (simp add: conc_def)
done

lemma conc_rev [simp]:
  "conc (rev ` B) (rev ` A) = rev ` conc A B"
  apply (simp add: conc_def)
  apply (rule equalityI)
   apply clarsimp
   apply (rule_tac x="xb@xa" in rev_image_eqI)
    apply clarsimp
    apply auto[1]
   apply simp
  apply clarsimp
  apply (rule_tac x="rev ys" in exI)
  apply simp
  done

lemma star_rev [simp]:
  "star (rev ` lang r) = rev ` star (lang r)"
  apply auto
  sorry

lemma "lang (reverse r) = rev ` (lang r)"
apply (induct r)
apply auto
apply (metis ComplI rev_image_eqI rev_swap)
done

end
