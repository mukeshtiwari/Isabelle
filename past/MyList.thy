theory MyList
  imports Main
begin
(* My efforts to formalize 
   http://hackage.haskell.org/package/base-4.12.0.0/docs/Data-List.html
*)

datatype 'a List =  
  Nil 
  | Cons (head : 'a) (tail : "'a List") 


fun append :: "'a List \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  appendNil: "append Nil ys = ys" |
  appendCon: "append (Cons x xs) ys = Cons x (append xs ys)"


lemma append_associative [simp] : "append xs (append ys zs) = append (append xs ys) zs"
  apply (induction xs)
   apply auto
  done

fun map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a List \<Rightarrow> 'b List" where
   mapNil: "map f Nil = Nil" |
   mapCon: "map f (Cons x xs) = Cons (f x) (map f xs)" 

lemma append_map [simp] : "append (map f xs) (map f ys) = map f (append xs ys)"
  apply (induction xs)
   apply auto
  done

fun rev :: "'a List \<Rightarrow> 'a List" where
  "rev Nil = Nil " |
  "rev (Cons x xs) = append (rev xs) (Cons x Nil)" 

lemma append_Nil[simp] : "append xs Nil = xs"
  apply (induction xs)
   apply auto
  done

lemma rev_append[simp] : "rev (append xs ys) = append (rev ys) (rev xs)"
  apply (induction xs)
   apply auto
  done

lemma rev_rev_identity[simp]: "rev (rev xs) = xs" 
  apply (induction xs)
   apply auto
  done

(* Snoc List where we add in the Last *)
datatype 'a SList = 
    SNil
    | SCons (stail : "'a SList") (shead : 'a)

(* Let's Write a function which convert List <-> SList *)
fun list_to_snoc :: "'a List \<Rightarrow> 'a SList" where
  "list_to_snoc Nil = SNil" |
  "list_to_snoc (Cons x xs) = SCons (list_to_snoc xs) x" 

lemma compute_simp : "list_to_snoc (Cons 1 (Cons 2 (Cons 3 Nil))) = 
                      (SCons (SCons (SCons SNil 3) 2) 1)" 
  by simp

fun snoc_to_list :: "'a SList \<Rightarrow> 'a List" where
  "snoc_to_list SNil = Nil" |
  "snoc_to_list (SCons xs x) = Cons x (snoc_to_list xs)" 

lemma snoc_cons_id : "snoc_to_list (list_to_snoc xs) = xs"
  apply (induction xs)
   apply auto
  done


lemma cons_snoc_identity : "list_to_snoc (snoc_to_list xs) = xs" 
  apply (induction xs)
   apply auto
  done

fun intersperse :: "'a \<Rightarrow> 'a List \<Rightarrow> 'a List" where
  "intersperse _ Nil = Nil" |
  "intersperse x (Cons y Nil) = (Cons y Nil)" |
  "intersperse x (Cons y ys) = Cons y (Cons x (intersperse x ys))" 


lemma map_intersperse: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs)
  subgoal by simp
  subgoal for x xs (* something like intros in Coq *)
    apply (cases xs) (* something like case in Coq *)
     apply simp_all
    done
  done

lemma map_intersperse1 : "map f (intersperse a xs) = intersperse (f a) (map f xs)"
  apply (induction xs rule: intersperse.induct)
    apply auto  
  done

lemma map_intersperse3: "map f (intersperse a xs) = intersperse (f a) (map f xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case by (cases xs) simp_all
qed

fun intercalate :: "'a List \<Rightarrow> ('a List) List \<Rightarrow> 'a List" where
  "intercalate _ Nil = Nil" |
  "intercalate x (Cons y Nil) = (Cons y Nil)" |
  "intercalate x (Cons y ys) = append (append y x) (intercalate x ys)" 




 
  
  
  

