BeginPackage["InformationFoundations`"];
ClearAll[InformationFoundations`verifyCertificates];
If[!ValueQ[InformationFoundations`$LibraryMode], InformationFoundations`$LibraryMode=False];
Begin["`Private`"];
Block[{AnalysisProof`$LibraryMode=True}, Get[FileNameJoin[{DirectoryName[$InputFileName], "..", "capitulo_02", "analise_geral.wl"}]]];
certificateGzipBase64 = "H4sIAAAAAAACE61Y227bOBD9FUFPCTpJROoebAvY3s0+7MMC2aAvgeE6Np0IsCVFkl23Tf59h5TEiy3FdlLABiSSM3N45kKOftlpNmelfX1/b69WNtgFW2aP82RjA44McGBgj+HeHuLT0B6P29H6mf/taVmuVwzHXi6sgcUurdvbT/buxNCYSOeongAV8qvcBgdc8SgRrNbL4xFwDb6mgeSEURQf1z8+zp7LHzgVyjVo47FyHqQRWqtrNfIltMhNJdxODMRRhpbVjp1ksZjwZYQAoUD4UMG+F0mFPERAXN0+2dHOh9lzMpeYzqwtp+0MaT2Dc+Tw3Hq5+ILvxLrCqXPr3OQD6qet5GurccS1LzarXCBu9UvFUkQqFyMjHJl8FY83RwLCpVtp+hA0EuyF0K4FW6LPNmwrsRNdUwPvyvBhE2XIeiy9R0Kgwn3JKp8kaVVkPUaBEs0n7JnoXjlMg/VNUthNKldyZmEQ4EoufyHfBkL+Ct+H1kX9JqTyJ77XPXKOIJnSsZZc24ckmfaGgLBy/A6tz9Y7dlLqlLxLxfERRl09/AssdaYMX9nWpZs6L/crAVuKUmAUno7q1xQ5FbHLqiqknCPtDWQY9BU0LuwUrKtA6FAGBpS29rgOEHCaFJiwZYJyrhpBaRqDS4GGMi9oBK67J0H2y/sf1lAr4S5W3UAqcT1wQ81ICG5kAKMBuHGtVbz64DkHncNj8B7GMkLrOsTD4+UbP1F2k8Bga/2QzGb0hJOkyZGih2IO28Nt0u7Fw/3FAadZxcOSnXCw1hwbjvIi8GJ55jmcfrnSQz5D8Ila7IJP5QsF3+1he3BcKnCTPpCDSj7ksuWpLuOoIm2jPnIQa/4p8cyT6tr9DTtq32ivUh9fZhT+JMvKErdwYtAZeb3tKkH9tDTYT0GKtgKvCaXO01f3X5u/gQ9BsFtZghAcI8APlDwd5XY32OvCFEQKZAyhUl/keGd7IzXD5sploCNKfehC6KnVBEJfTQYRhIFRrwJc3sj33RdamiCMOpbdXeKEisWyLOYb4+jVWdbTTxzDKH1aEEaOipeqWO9fXiMCEdXgVEVy4DJoQhy1EHfCOKAQucpnaMVT+TCbpVVxWj5HQVvluIb5RrQEQsW2JzvMa/Ndlv+bsxQvEKPRYjlv6o0hUT1ionodB+zcKGq79eJQWcPhf/og4Nx/QqV4vBPLqiz/W6wqpqmgf780RjHEmmOnW8RXztIO6IuyG3hjkXtvNHqrIhvaZulssXhL3zFKhOf2wPI+yoNYS744gFi1g7ELsXaTiCnEkaYzx0TquhthqDUzJ8QacUhbB+uGwcHrk0O1ohTznk+Fd4wXI8czOztsMhzfHMLC4QTmEJ6dTthTJuorRccE7ZUI9EOOe+uQ8999LouGVuS4fHMb93UAI0Rl/3yFp+/jCR3nV9Vxnnj6HmzpiHYreGTpoR6o7U9QzcmACAk15gL8Rxol7FmzfXtrTf6UDVDrCP6guUs2PsPf/VmAA6Q84iMjVgnBoKekz8NUnSKrTfXUey25abrJN7f2gROPOAiTIHz+vYVgflFX25bXnHZqVw4mKjUTNUBpaiaqjw6r004NeThkUuTxTzyx0d/gImy+eLG2qynGWFXa17/4PXqSZ2VSJRs2eV5nVcLSik/wT2/2tYeFOytW6+XUvuYEt70v5+iqcf5nrUMeGB1yzSDYTz/yrHpipfiWZ3yK2/n+9gomoLzI5uuZhid4A8/2sgfQpw8Dqr5nEpQCQ3bZcbAFVYgIGiZdBlutWcomPxnGrtLo9+yPiG05fZpWbJpONtPlWkeHTbKp7K/L/eR8/6eOThZ5Cw69hCKfr6//A6pB3dvWFQAA";
InformationFoundations`verifyCertificates[] := Module[{report,check,results={}},
report=AnalysisProof`verifyProofGraph[ImportString[ImportByteArray[BaseDecode[certificateGzipBase64], {"GZIP", "Text"}], "RawJSON"]];
If[!TrueQ[report["passed"]],Return[report]];
check[id_,formula_,hypotheses_]:=AppendTo[results,<|"id"->id,"passed"->TrueQ[report["targets"][id]["formula"]===formula && Sort[report["targets"][id]["hypotheses"]]===Sort[hypotheses]],"formula"->formula,"hypotheses"->hypotheses|>];
check["log_positive_quotient","|- ( log ` ( A / B ) ) = ( ( log ` A ) - ( log ` B ) )",{"|- A e. RR+","|- B e. RR+"}];
check["log_positive_product","|- ( log ` ( A x. B ) ) = ( ( log ` A ) + ( log ` B ) )",{"|- A e. RR+","|- B e. RR+"}];
check["log_two_positive","|- 0 < ( log ` ( 1 + 1 ) )",{}];
check["log_one_zero","|- ( log ` 1 ) = 0",{}];
check["log_mean_value","|- E. x e. ( A (,) B ) ( 1 / x ) = ( ( ( log ` B ) - ( log ` A ) ) / ( B - A ) )",{"|- A < B","|- A e. RR+","|- B e. RR"}];
AssociateTo[report,{"checks"->Length[results],"results"->results,"passed"->And@@Lookup[results,"passed"]}];report];
If[!TrueQ[InformationFoundations`$LibraryMode] && Length[$ScriptCommandLine]>0 && ExpandFileName[First[$ScriptCommandLine]]===ExpandFileName[$InputFileName], report=InformationFoundations`verifyCertificates[]; Print[ExportString[KeyDrop[report,{"targets"}],"RawJSON"]];Exit[If[TrueQ[report["passed"]],0,1]]];
End[];
EndPackage[];
