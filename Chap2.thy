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
    
    
  
  
    
    
    
    
  
    
    
    

    
    
  
    