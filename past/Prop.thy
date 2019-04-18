theory Prop
imports Main
begin
datatype bool = True | False
fun conj :: "bool => bool \<Rightarrow> bool" where
"conj True True = True" |
"conj _ _ = False"

fun disjunc :: "bool \<Rightarrow> bool \<Rightarrow> bool" where
"disjunc False False = False" |
"disjunc _ _ = True"

datatype natt = Z | Succ natt

fun addd :: "natt \<Rightarrow> natt \<Rightarrow> natt" where
 "addd Z n = n" |
 "addd (Succ m) n = Succ (addd m n)"

lemma addzeroright[simp] : "addd m Z = m"
apply (induction m) apply (auto)
done

lemma addassociativity[simp] : "addd (addd m n) p = addd m (addd n p)"
apply (induction m)  apply auto
done
lemma addsucc[simp] : "addd x (Succ y) = Succ (addd x y)"
apply (induction x) apply auto done
 
lemma addcommutative[simp] : "addd x y = addd y x"
apply (induction x)  apply auto done
 
fun double :: "natt \<Rightarrow> natt" where
  "double Z = Z" |
  "double (Succ n) = Succ (Succ (double n))"

lemma add_double : "addd n n = double n"
apply (induction n) apply auto done

datatype 'a list = Nil | Cons 'a "'a list"

fun app :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
"app Nil ys = ys" |
"app (Cons x xs) ys = Cons x (app xs ys)"

fun rev :: "'a list \<Rightarrow> 'a list" where
"rev Nil = Nil" |
"rev (Cons x xs) = app (rev xs) (Cons x Nil)"

value "rev (Cons True (Cons False Nil))"
value "rec (Cons a (Cons b Nil))"

(* if you don't add [simp] then use apply (simp add: lemmaOne lemmaTow) *)
lemma app_nil[simp] : "app xs Nil = xs"
apply (induction xs) apply auto  done

lemma app_associate[simp] : "app (app xs ys) zs = app xs (app ys zs)"
apply (induction xs) apply auto done

lemma rev_app[simp] : "rev (app xs ys) = app (rev ys) (rev xs)"
apply (induction xs) apply auto
done

theorem rev_rev[simp] : "rev (rev xs) = xs"
apply (induction xs)
apply auto done

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> natt" where
  "count x Nil = Z" |
  "count x (Cons y ys) = 
    (if x = y then Succ (count x ys) else (count x ys))"

fun length :: "'a list \<Rightarrow> natt" where
  "length Nil = Z" |
  "length (Cons x xs) = Succ (length xs)"
              
value "length (Cons a (Cons b (Cons c Nil)))"
end