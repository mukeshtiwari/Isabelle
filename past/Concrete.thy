theory Concrete
imports Main
begin  
datatype bool = True | False

fun conj :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"

datatype nat = Z | Succ nat
  
fun add :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"add Z n = n" |
"add (Succ m) n = Succ (add m n)"

lemma add_02: "add m Z = m"
  apply (induction m)
   apply simp
  apply simp
  done
    
datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "app Nil ys = ys" |
  "app (Cons x xs) ys = Cons x (app xs ys)"
  
fun rev :: "'a list \<Rightarrow> 'a list" where
  "rev Nil = Nil" |
  "rev (Cons x xs) = app (rev xs) (Cons x Nil)"
  
theorem app_Nil2 [simp] : "app xs Nil = xs"
  apply (induction xs)
   apply auto
  done
    
theorem  app_assoc [simp] : "app (app xs ys) zs = app xs (app ys zs)"
  apply (induction xs)
   apply auto
  done
    
  
theorem rev_app [simp] : "rev (app xs ys) = app (rev ys) (rev xs)"
  apply (induction xs)
   apply auto
  done
    
  
theorem rev_rev [simp] : "rev (rev xs) = xs"
  apply (induction xs)
   apply auto
  done
    
fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map f Nil = Nil" | 
  "map f (Cons x xs) = Cons (f x) (map f xs)"
  
     
    
   
    
  