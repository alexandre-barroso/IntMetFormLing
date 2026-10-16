ClearAll[check];
results={};
check[name_,condition_]:=If[TrueQ[condition],AppendTo[results,name],Print[name];Exit[1]];
check["three_regions",292+103==395&&292+491==783&&292+103+491==886];
check["precision_rounding",Abs[100 (292/395)-739/10]<1/20];
check["coverage_rounding",Abs[100 (292/783)-373/10]<1/20];
check["unknown_exterior",Resolve[ForAll[{s,t},s>=0&&t>s\[Implies](292+s)/(886+s)<(292+t)/(886+t)],Reals]];
check["exterior_membership",TautologyQ[(ss&&! (pp||qq))\[Equivalent](ss&&!pp&&!qq),{ss,pp,qq}]];
Print[ExportString[<|"passed"->True,"checks"->Length[results],"results"->results|>,"RawJSON"]];
