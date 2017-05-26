theory Chap3
  imports Main
begin
  
type_synonym vname = string
datatype aexp = 
  N int |
  V vname |
  Plus aexp aexp
  
type_synonym val = int
type_synonym state = vname \<Rightarrow> val  
  
  
  
  