results = Map[Function[pair, <|"id" -> "c03_r01_membership_" <> ToString[Boole[pair[[1]]]] <> ToString[Boole[pair[[2]]]], "passed" -> (Boole[Or @@ pair] + Boole[And @@ pair] == Total[Boole /@ pair])|>], Tuples[{False, True}, 2]];
report = <|"backend" -> "Wolfram", "checks" -> Length[results], "passed" -> AllTrue[results, TrueQ[#["passed"]] &], "results" -> results|>;
Print[ExportString[report, "RawJSON"]];
Exit[If[TrueQ[report["passed"]], 0, 1]];
