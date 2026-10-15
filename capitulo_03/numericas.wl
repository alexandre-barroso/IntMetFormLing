ClearAll["Global`*"];
results={};
check[id_,value_]:=AppendTo[results,<|"id"->id,"passed"->TrueQ[value]|>];

check["c03.e0018.1", (((-1*2)+(3+3))) == (4)];
check["c03.e0057.1", ((4*(4^(-1)))) == (1)];
check["c03.e0061.1", ((3*(4^(-1)))) == ((3/4))];
check["c03.e0065.1", ((2*(4^(-1)))) == ((1/2))];
check["c03.e0066.1", ((158*(200^(-1)))) == ((79/100))];
check["c03.e0067.1", ((72*(200^(-1)))) == ((9/25))];
check["c03.e0068.1", ((5*5)) == (25)];
check["c03.e0097.1", ((1+(3+(1+(1+2))))) == (8)];
check["c03.e0188.1", ((2+4)) == (6)];
check["c03.e0324.1", ((69+(-1*59))) == (10)];
check["c03.e0325.1", (((8651/100)+(-1*85))) == ((151/100))];
check["c03.e0326.1", ((96+(-1*72))) == (24)];
report=<|"backend"->"Wolfram","checks"->Length[results],"passed"->AllTrue[results,TrueQ[#["passed"]]&],"results"->results|>;
Print[ExportString[report,"RawJSON"]];
Exit[If[TrueQ[report["passed"]],0,1]];
