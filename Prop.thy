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
end