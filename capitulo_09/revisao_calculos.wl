results={};
check[id_,value_]:=AppendTo[results,<|"id"->id,"passed"->TrueQ[value]|>];
check["indicator_numeric_cases",Resolve[ForAll[{p,q},Implies[(q==0||q==1)&&(q!=1||p==1),p q==q]],Reals]];
Print[ExportString[<|"checks"->Length[results],"passed"->And@@Lookup[results,"passed"],"results"->results|>,"RawJSON"]];
Exit[If[And@@Lookup[results,"passed"],0,1]];
