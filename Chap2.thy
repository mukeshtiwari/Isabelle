theory Chap2
  imports Main
begin
value "1 + (2 :: nat)"
value "1 + (2 :: int)"
value "1 - (2 :: nat)"
value "1 - (2 :: int)"
  
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "add 0 n = n" |
  "add (Suc m) n = Suc (add m n)"
  
lemma add_z [simp] : "add m 0 = m"
  apply (induction m)
   apply auto
  done
    
lemma add_p [simp] : "add m (Suc n) = Suc (add m n)"
  apply (induction m)
  apply auto
  done
    
theorem add_comm : "add m n = add n m"
  apply (induction m)
   apply auto
  done

theorem add_assoc : "add (add m n) p = add m (add n p)"
  apply (induction m)
   apply auto
  done
    
fun double :: "nat \<Rightarrow> nat" where
  "double 0 = 0" |
  "double (Suc n) = Suc (Suc (double n))"
  
value "double 3"
  
theorem double_correctness : "double m = add m m"
  apply (induction m)
   apply auto
  done
 
fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count _ [] = 0" |
  "count e (x # xs) = 
    (if e = x then Suc (count e xs)
     else count e xs)"
  
theorem count_correctness : "count x xs \<le> length xs"
  apply (induction xs)
   apply auto
  done
    
fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "snoc [] a = [a]" |
  "snoc (x # xs) a = x # (snoc xs a)"
  
fun reverse :: "'a list \<Rightarrow> 'a list" where
  "reverse [] = []" |
  "reverse (x # xs) = snoc (reverse xs) x"

lemma rev_snoc [simp] : "reverse ( snoc xs x ) = x # ( reverse xs )"
  apply (induction xs)
   apply auto
  done
    
theorem  snoc_rev : "reverse (reverse xs) = xs"
  apply (induction xs)
   apply auto
  done
    
fun sum_upto :: "nat \<Rightarrow> nat" where
  "sum_upto 0 = 0"|
  "sum_upto (Suc n) = Suc n + sum_upto n"
  
  value "sum_upto 3"
    
theorem sum_correctness : "sum_upto n = n * (n + 1) div 2"
  apply (induction n)
   apply auto
  done
    
datatype 'a tree = 
  Tip
  | Node "'a tree" 'a "'a tree"
    
fun mirror :: "'a tree \<Rightarrow> 'a tree" where
  "mirror Tip = Tip"|
  "mirror (Node x a y) = Node (mirror y) a (mirror x)"
  
theorem mirror_correctness : "mirror (mirror t) = t"
  apply (induction t)
   apply auto
  done
    
fun div2 :: "nat \<Rightarrow> nat" where
  "div2 0 = 0"|
  "div2 (Suc 0) = 0"|
  "div2 (Suc (Suc n)) = Suc (div2 n)"
  
theorem div2_correctness : "div2 n = n div 2"
  apply (induction n rule: div2.induct)
    apply auto
  done
    
    
fun contents :: "'a tree \<Rightarrow> 'a list" where
  "contents Tip = []"|
  "contents (Node l a r) = contents l @ [a] @ contents r"
  
fun treesum :: "nat tree \<Rightarrow> nat" where
  "treesum Tip = 0"|
  "treesum (Node l x r) = treesum l + x + treesum r"
  
fun listsum :: "nat list \<Rightarrow> nat" where
  "listsum [] = 0"|
  "listsum (x # xs) = x + listsum xs" 
  
theorem treelistsum : "treesum t = sum_list (contents t)"
  apply (induction t)
   apply auto
  done
    
datatype 'a tree2 = 
  Leaf 'a 
  | Node "'a tree2" 'a "'a tree2"
  
fun mirror2 :: "'a tree2 \<Rightarrow> 'a tree2" where
  "mirror2 (Leaf a) = Leaf a"|
  "mirror2 (Node l a r) = Node (mirror2 r) a (mirror2 l)"
  
fun pre_order :: "'a tree2 \<Rightarrow> 'a list" where
  "pre_order (Leaf a) = [a]"|
  "pre_order (Node l a r) = a # (pre_order l) @ (pre_order r)"
  
fun post_order :: "'a tree2 \<Rightarrow> 'a list" where
  "post_order (Leaf a) = [a]"|
  "post_order (Node l a r) = post_order l @ post_order r @ [a]"
  
theorem pre_post : "pre_order (mirror2 t) = rev (post_order t)"
  apply (induction t)
   apply auto
  done
    
fun intersperse :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "intersperse a [] = [a]"|
  "intersperse a (x # xs) = x # a # intersperse a xs"
  
theorem mapinter : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
   apply auto
  done
    
fun itrev :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "itrev [] ys = ys"|
  "itrev (x # xs) ys = itrev xs (x # ys)"
  
lemma "itrev xs ys = rev xs @ ys"
  apply (induction xs arbitrary: ys)
   apply auto
  done
    
fun itadd :: "nat \<Rightarrow> nat \<Rightarrow> nat" where 
  "itadd 0 n = n"|
  "itadd (Suc m) n = itadd m (Suc n)"
  
lemma "itadd m n = add m n"
  apply (induction m arbitrary: n)
   apply auto
  done
    
datatype tree0 = 
  E | 
  Node tree0 tree0
  
fun nodes :: "tree0 => nat" where
  "nodes E = 0"|
  "nodes (Node l r) = 1 + nodes l + nodes r"
  
fun explode :: "nat \<Rightarrow> tree0 \<Rightarrow> tree0" where
  "explode 0 t = t"|
  "explode (Suc n) t = explode n (Node t t)"
  
lemma rel : "nodes (explode n t) = 2 ^ n * (nodes t + 1) - 1"
  apply (induction n arbitrary: t)
   apply simp
  apply (simp add : algebra_simps)
  done
    
datatype exp = 
  Var |
  Const int | 
  Add exp exp |
  Mult exp exp
  
fun eval :: "exp \<Rightarrow> int \<Rightarrow> int" where
  "eval Var t = t"|
  "eval (Const i) t = i"|
  "eval (Add e1 e2) t = eval e1 t + eval e2 t"|
  "eval (Mult e1 e2) t = eval e1 t * eval e2 t"
  
fun evalp :: "int list \<Rightarrow> int \<Rightarrow> int" where
  "evalp [] t = 0"|
  "evalp (h # ts) t = h + t * (evalp ts t)"
  
fun addpoly :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "addpoly [] ys = ys"|
  "addpoly xs [] = xs"|
  "addpoly (x # xs) (y # ys) = (x + y) # addpoly xs ys"
  
lemma [simp]: "evalp (addpoly xs ys) x = evalp xs x + evalp ys x"
  apply (induction xs ys rule: addpoly.induct)
    apply (auto simp add: algebra_simps)
  done

fun multone :: "int \<Rightarrow> int list \<Rightarrow> int list" where
  "multone _ [] = []"|
  "multone c (x # xs) = (c * x) # multone c xs"
    
fun multpoly :: "int list \<Rightarrow> int list \<Rightarrow> int list" where
  "multpoly [] _ = []"|
  "multpoly (x # xs) ys = addpoly (multone x ys) (0 # multpoly xs ys)"  

fun coeffs :: "exp \<Rightarrow> int list" where
  "coeffs Var = [0, 1]"|
  "coeffs (Const i) = [i]"|
  "coeffs (Add e1 e2) = addpoly (coeffs e1) (coeffs e2)"|
  "coeffs (Mult e1 e2) = multpoly (coeffs e1) (coeffs e2)"
  
lemma [simp] : "evalp (multone c e) x = c * (evalp e x)"
  apply (induction e)
   apply (auto simp add: algebra_simps)
  done
    
lemma [simp]: "evalp (multpoly e1 e2) x = evalp e1 x * evalp e2 x"
  apply (induction e1)
    apply (auto simp add: algebra_simps)
  done
    
  
theorem "evalp (coeffs e) x = eval e x"
  apply (induction e rule: exp.induct)
    apply (auto simp add: algebra_simps)
  done
    
    
  
    
    
  
  
  

    
  
    
    
    
  
  
    
    
    
    
  
    
    
    

    
    
  
    