theory Chap2 
  imports Main
begin

datatype cbool = Ctrue | Cfalse

fun conj :: "cbool \<Rightarrow> cbool \<Rightarrow> cbool" where
  "conj Ctrue Ctrue = Ctrue" |
  "conj _ _ = Cfalse"

datatype cnat = C | Csuc cnat

fun add :: "cnat \<Rightarrow> cnat \<Rightarrow> cnat" where 
  "add C m = m" |
  "add (Csuc n) m = Csuc (add n m)"

lemma add_n_0 [simp] : "add m C = m"
proof (induction m)
  case C thus ?case by simp
  case (Csuc n) thus ?case by simp
qed
 
datatype 'a clist = Cnil | Ccons 'a "'a clist"

fun app :: "'a clist \<Rightarrow> 'a clist \<Rightarrow> 'a clist" where
 "app Cnil ys = ys" |
 "app (Ccons x xs) ys = Ccons x (app xs ys)" 

fun revt :: "'a clist \<Rightarrow> 'a clist" where
  "revt Cnil = Cnil" |
  "revt (Ccons x xs) = app (revt xs) (Ccons x Cnil)" 

theorem app_nil [simp] : "app xs  Cnil = xs"
  apply (induction xs)
   apply auto
  done

theorem app_assoc [simp] : "app xs (app ys zs) = app (app xs ys) zs"
  apply (induction xs)
   apply auto
  done 

theorem rev_app [simp] : "revt (app xs ys) = app (revt ys) (revt xs)" 
  apply (induction xs)
   apply auto
  done

theorem rev_rev : "revt (revt xs) = xs"
  apply (induction xs)
   apply auto
  done

value "1 + (2 :: nat)"
value "1 + (2 :: int)"
value "1 - (2 :: nat)"
value "1 - (2 :: int)"

theorem add_suc [simp] : "add n (Csuc m) = Csuc (add n m)"
  apply (induction n)
   apply auto
  done

theorem add_commutative : "add m n = add n m"
  apply (induction m)
   apply auto
  done

theorem add_assoc : "add m (add n p) = add (add m n) p"
  apply (induction m)
   apply auto
  done

fun double :: "cnat \<Rightarrow> cnat" where
 "double C = C" |
 "double (Csuc n) = Csuc (Csuc (double n))"

theorem double_correct : "double m = add m m"
  apply (induction m)
   apply auto
  done

(* From here onwards, use the datatype given by Isabelle *)
fun count :: "'a \<Rightarrow>  'a list \<Rightarrow> nat" where
  "count _ Nil = 0" |
  "count x (y # ys) =
   (if x = y then Suc (count x ys)
    else count x ys)" 

fun length :: "'a list \<Rightarrow> nat" where
 "length Nil = 0" |
 "length (_ # xs) = Suc (length xs)"

theorem count_correct : "count x xs \<le> length xs" 
  apply (induction xs)
   apply auto
  done  

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc Nil x = [x]" |
  "snoc (y # ys) x = y # (snoc ys x)" 

fun reverse :: "'a list \<Rightarrow> 'a list" where
 "reverse Nil = Nil" |
 "reverse (x # xs) = snoc (reverse xs) x" 

theorem rev_snoc [simp] :  "reverse (snoc xs a) = a # reverse xs"
  apply (induction xs)
   apply auto
  done


theorem reverse_reverse : "reverse (reverse xs) = xs"
  apply (induction xs)
   apply auto
  done

fun sum_upto :: "nat \<Rightarrow> nat" where
 "sum_upto 0 = 0" | 
 "sum_upto (Suc n) = Suc n + sum_upto n"

theorem sum_upto_n : "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
   apply auto 
  done

datatype 'a tree = Tip | Node "'a tree" 'a "'a tree"

fun mirror :: "'a tree \<Rightarrow> 'a tree" where 
 "mirror Tip = Tip" |
 "mirror (Node l v r) = Node (mirror r) v (mirror l)"

theorem mirror_correct : "mirror (mirror t) = t"
  apply (induction t rule : mirror.induct)
   apply auto
  done

fun div2 :: "nat \<Rightarrow> nat" where 
  "div2 0 = 0" | 
  "div2 (Suc 0) = 0" |
  "div2 (Suc (Suc n)) = Suc (div2 n)"

theorem div_2 : "div2 n = n div 2"
  apply (induction n rule: div2.induct)
    apply auto
  done

fun content :: "'a tree \<Rightarrow> 'a list" where
 "content Tip = Nil" |
 "content (Node l v r) = content l @ [v] @ content r"

fun sum_tree :: "nat tree \<Rightarrow> nat" where
 "sum_tree Tip = 0" |
 "sum_tree (Node l v r) = sum_tree l + v + sum_tree r"

fun sum_list :: "nat list \<Rightarrow> nat" where 
 "sum_list [] = 0" |
 "sum_list (x # xs) = x + sum_list xs"

theorem sum_list_dist [simp] : "sum_list t1 + x2 + sum_list t2 =
       sum_list (t1 @ x2 # t2)" 
proof (induction t1)
  case Nil thus ?case by simp
  case (Cons x xs) thus ?case by simp
qed

theorem sum_tree_correct : "sum_tree t = sum_list (content t)"
proof (induction t)
  case Tip thus ?case by simp
  case (Node l v r) thus ?case by simp
qed

datatype 'a tree2 = Tip 'a | Node "'a tree2" "'a tree2" 

fun mirror2 ::"'a tree2 \<Rightarrow> 'a tree2" where
  "mirror2 (Tip x) = Tip x" |
  "mirror2 (Node x y) = Node (mirror2 y) (mirror2 x)" 

fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
 "pre_order (Tip x) = [x]" |
 "pre_order (Node x y) = pre_order x @ pre_order y"

fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
 "post_order (Tip x) = [x]" |
 "post_order (Node x y) = post_order x @ post_order y"

theorem pre_post_tree2 : "pre_order (mirror2 t) = rev (post_order t)"
proof (induction t)
  case (Tip x) 
  then show ?case by simp
  case (Node x y) 
  then show ?case by auto
qed


fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse _ [] = []" |
  "intersperse _ [x] = [x]" |
  "intersperse t (x # xs) = x # t # intersperse t xs"

theorem map_intersperse : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
proof (induction xs rule: intersperse.induct)
  case (1 uu)
  then show ?case by simp  
  case (2 uu x) 
  then show ?case by simp
  case (3 t x v va) 
  then show ?case by auto
qed





  
 




 

  


  
 









