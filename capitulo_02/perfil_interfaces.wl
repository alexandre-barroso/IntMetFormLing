BeginPackage["ProfileInterfaces`"];
ClearAll[ProfileInterfaces`verifyCertificates];
If[!ValueQ[ProfileInterfaces`ProfileInterfaces`$LibraryMode], ProfileInterfaces`ProfileInterfaces`$LibraryMode=False];
Begin["`Private`"];
Block[{AnalysisProof`$LibraryMode=True}, Get[FileNameJoin[{DirectoryName[$InputFileName], "analise_geral.wl"}]]];
certificateGzipBase64 = "H4sIAAAAAAACE81U30/CMBD+V5o+SVJwHSBIggmS8OQTGl9g4mAFlnTr0g2dP/jfvXZQOxjokzFZsuvX69133137gWMRsBT3JhPsp+kmYpjgzzoaItZA4zH2yASHUTIL40yKYuuhgYmj8CgCQLJFHGACxwewGuoDyRpMcPNgAR/1jHcmN1hj6tNogolLmifStBRu0xo0UK6YDdAFGqFnWNQsorbnBQRAl9Pp3r9WeMTBjPEQqHQIVYD0Od8hV6RbQeM4Drk+zrXb/KzfWMQ0tbsnekpESo0u4ZxHG75wjZADfegWLBNPI0Mj8iNYu7qN3mDnYOZaebsjyhoZKzehRsYqsJE53SbUIdQ1TaLNoksF3Wz13+m2LbrLhYjTLEqyCr5OJY3C9uz+OPZha4JL46k6HogIvQiODZUuoXpkJHuVYQautENcxxbz/YDYKToe3CBfrlgGF/YDJ1IsQ87UWLGV9Odgpgufh/FK7ap7jXu0BeULCd3yca9iVocob5RG1gwtweu3RGRrlurn4Tdz/sMVLT8sW3JYAK+gf3VEXzO+L8efBfrX3+NHVSmHv6zonUlh9eW7IJee64dzVv7ydJ3Ixq1c7kEurY5TqNVHzmEOb7vdfgEdjkf3EAYAAA==";
ProfileInterfaces`verifyCertificates[] := Module[{report,check,results={}},
report=AnalysisProof`verifyProofGraph[ImportString[ImportByteArray[BaseDecode[certificateGzipBase64], {"GZIP", "Text"}], "RawJSON"]];
If[!TrueQ[report["passed"]],Return[report]];
check[id_,formula_,hypotheses_]:=AppendTo[results,<|"id"->id,"passed"->TrueQ[report["targets"][id]["formula"]===formula && Sort[report["targets"][id]["hypotheses"]]===Sort[hypotheses]],"formula"->formula,"hypotheses"->hypotheses|>];
check["profile_integrable_scaling","|- ( x e. A |-> ( C x. ( F ` x ) ) ) e. L^1",{"|- ( x e. A |-> ( F ` x ) ) e. L^1","|- A. x e. A ( F ` x ) e. RR","|- C e. RR"}];
check["profile_integral_scaling","|- ( C x. S. A ( F ` x ) _d x ) = S. A ( C x. ( F ` x ) ) _d x",{"|- ( x e. A |-> ( F ` x ) ) e. L^1","|- A. x e. A ( F ` x ) e. RR","|- C e. RR"}];
check["profile_zero_integrable","|- ( x e. A |-> 0 ) e. L^1",{"|- A e. dom vol"}];
check["profile_zero_integral","|- S. A 0 _d x = 0",{}];
AssociateTo[report,{"checks"->Length[results],"results"->results,"passed"->And@@Lookup[results,"passed"]}];report];
If[!TrueQ[ProfileInterfaces`ProfileInterfaces`$LibraryMode] && Length[$ScriptCommandLine]>0 && ExpandFileName[First[$ScriptCommandLine]]===ExpandFileName[$InputFileName], report=ProfileInterfaces`verifyCertificates[]; Print[ExportString[KeyDrop[report,{"targets"}],"RawJSON"]];Exit[If[TrueQ[report["passed"]],0,1]]];
End[];
EndPackage[];
