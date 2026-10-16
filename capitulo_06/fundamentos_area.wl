BeginPackage["AreaFoundations`"];
ClearAll[AreaFoundations`verifyCertificates];
If[!ValueQ[AreaFoundations`$LibraryMode], AreaFoundations`$LibraryMode=False];
Begin["`Private`"];
Block[{AnalysisProof`$LibraryMode=True}, Get[FileNameJoin[{DirectoryName[$InputFileName], "..", "capitulo_02", "analise_geral.wl"}]]];
certificateGzipBase64 = "H4sIAAAAAAACE7VWaY/aMBD9K64/gWogTpZT3ZXQSm2lynyqVAmWZgOYEpFrk9DuxX/v2A4mhNDl2HJIk4k98/zmeewXHIQznuDeaIR9HxMcBMbqGZPRWP3gr/z8wZ2Be4T78FBBw+HNNbpHDFXxuDg0gI+hx7KdAU6SrHwO7tcaTOZ1NBhgOTHCxCSWMF0/st0gjUM16nsdk6tDMCooUEEM9Fq7QcLRRz/BWUUNsD8ARGGL7z1aZmDV5KXMK6xAWktlbYAWUFQAB2rc3UGQLF8Vk9YhWMeCysHJpVYR5+lvx9Mx+xLj5xOjw5SBXmqgs7xFQGevVGXLl2OCmc09FwBTg9BNIbuESps/JE/ilZlf1bS4qG8KSx5XmVr6IvPt7SYtBKFNkWeTlF4RKgsS8z+xm8IsahHaPraWtJMDOfU87l/OfZHxPLtS8MBZ84DkTarxuEBCEnluepHwz1sCgymGFhKT1o+9DgDOITghqFaSUle0ABOWs+WAadUV9ce0j5VoEqgiTdImtEtMc7tN0nhVaFaCV4uYuZYxh41kXl7N5dk7SWJqZbXW8jSbxGwf3UEqyJkkgKgPeE7uJW/G3o3OctGZjP5Yl4OodDP0EayqBrKbnJWU9XBfFVI/1PUVX7ttaAvzk40oPhTRynccbzW5vPpfzi4LTP76/3jPGGblEn3XLdghZpdYBrEoseCsvtLatppiv41hNzrxL57CbeIF88coDHiQuo5nJzx2eWLP+DT0ozBxUzcMxBhx9cA9s0PwPIz9lefgnqoyTM5IuYYnqL+tenUFGaher0suahkXp/dCoDEfctvIzokFRwdePEVhuuCJvEflz6rda86alLGSOq5nT8IVHGmaEqu1R4nSyTviFhuoXIKZ6DZya8injSbhJcu0V7LwvQ1K/kHHev0XR0a3An4KAAA=";
AreaFoundations`verifyCertificates[] := Module[{report,check,results={}},
report=AnalysisProof`verifyProofGraph[ImportString[ImportByteArray[BaseDecode[certificateGzipBase64], {"GZIP", "Text"}], "RawJSON"]];
If[!TrueQ[report["passed"]],Return[report]];
check[id_,formula_,hypotheses_]:=AppendTo[results,<|"id"->id,"passed"->TrueQ[report["targets"][id]["formula"]===formula && Sort[report["targets"][id]["hypotheses"]]===Sort[hypotheses]],"formula"->formula,"hypotheses"->hypotheses|>];
check["exponential_series_decomposition","|- ( exp ` A ) = ( sum_ k e. ( 0 ... ( M - 1 ) ) ( ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) ) ` k ) + sum_ k e. ( ZZ>= ` M ) ( ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) ) ` k ) )",{"|- A e. CC","|- M e. NN"}];
check["exponential_series_tail_bound","|- ( abs ` sum_ k e. ( ZZ>= ` M ) ( ( n e. NN0 |-> ( ( A ^ n ) / ( ! ` n ) ) ) ` k ) ) <_ ( ( ( abs ` A ) ^ M ) x. ( ( M + 1 ) / ( ( ! ` M ) x. M ) ) )",{"|- ( abs ` A ) <_ 1","|- A e. CC","|- M e. NN"}];
AssociateTo[report,<|"checks"->Length[results],"results"->results,"passed"->And@@Lookup[results,"passed"]|>];report];
If[!TrueQ[AreaFoundations`$LibraryMode] && Length[$ScriptCommandLine]>0 && ExpandFileName[First[$ScriptCommandLine]]===ExpandFileName[$InputFileName], report=AreaFoundations`verifyCertificates[]; Print[ExportString[KeyDrop[report,{"targets"}],"RawJSON"]];Exit[If[TrueQ[report["passed"]],0,1]]];
End[];
EndPackage[];
