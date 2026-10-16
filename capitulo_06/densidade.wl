ClearAll["Global`*"];
results={};
check[id_,condition_]:=AppendTo[results,<|"id"->id,"passed"->TrueQ[condition]|>];
check["zero_width",FullSimplify[a-a==0,Element[a,Reals]]];
check["point_mass_zero",Integrate[f[t],{t,a,a},Assumptions->Element[a,Reals]]==0];
report=<|"backend"->"Wolfram Language","checks"->Length[results],"passed"->And@@Lookup[results,"passed"],"results"->results|>;
Print[ExportString[report,"RawJSON"]];
Exit[If[report["passed"],0,1]];
