ClearAll[check, results, r, d, u, p, q, a, b, t, x, y, colorModel];
results = {};
check[id_, condition_] := AppendTo[results, <|"id" -> id, "passed" -> TrueQ[condition]|>];
colorModel[prior_, meaning_, encoder_] := Module[{nm, nw, nu, pw, pu, joint, decoder, sourceInformation, wordInformation, distortion, pair},
  nm = Length[prior];
  If[nm == 0 || Length[meaning] != nm || Length[encoder] != nm || Length[First[meaning]] == 0 || Length[First[encoder]] == 0, Return[$Failed]];
  nw = Length[First[encoder]]; nu = Length[First[meaning]];
  If[!AllTrue[meaning, Length[#] == nu &] || !AllTrue[encoder, Length[#] == nw &], Return[$Failed]];
  If[!AllTrue[Flatten[{prior, meaning, encoder}], # >= 0 &] || !AllTrue[Join[{prior}, meaning, encoder], Total[#] == 1 &], Return[$Failed]];
  pw = Table[Sum[prior[[m]] encoder[[m, w]], {m, nm}], {w, nw}];
  pu = Table[Sum[prior[[m]] meaning[[m, u]], {m, nm}], {u, nu}];
  joint = Table[Sum[prior[[m]] encoder[[m, w]] meaning[[m, u]], {m, nm}], {w, nw}, {u, nu}];
  decoder = Table[If[pw[[w]] == 0, 0, joint[[w, u]]/pw[[w]]], {w, nw}, {u, nu}];
  sourceInformation = Sum[If[prior[[m]] meaning[[m, u]] == 0, 0, prior[[m]] meaning[[m, u]] Log[2, meaning[[m, u]]/pu[[u]]]], {m, nm}, {u, nu}];
  wordInformation = Sum[If[joint[[w, u]] == 0, 0, joint[[w, u]] Log[2, decoder[[w, u]]/pu[[u]]]], {w, nw}, {u, nu}];
  distortion = 0;
  Do[pair = prior[[m]] encoder[[m, w]];
    If[pair > 0, Do[If[meaning[[m, u]] > 0,
      If[decoder[[w, u]] <= 0 || pu[[u]] <= 0, Return[$Failed]];
      distortion += pair meaning[[m, u]] Log[2, meaning[[m, u]]/decoder[[w, u]]]], {u, nu}]], {m, nm}, {w, nw}];
  {sourceInformation, wordInformation, distortion, pw, pu, joint, decoder}
];
check["positive_log_split", FullSimplify[Log[2, r/d] == Log[2, r/u] - Log[2, d/u], r > 0 && d > 0 && u > 0]];
check["weighted_log_split", FullSimplify[t Log[2, r/d] == t Log[2, r/u] - t Log[2, d/u], r > 0 && d > 0 && u > 0 && Element[t, Reals]]];
check["zero_weight_branch", 0 x == 0];
check["mutual_information_cancel_prior", FullSimplify[p r/(p u) == r/u, p > 0 && u > 0]];
check["mutual_information_decoder_ratio", FullSimplify[(q/p)/u == q/(p u), p > 0 && u > 0]];
check["finite_aggregation_induction_step", Expand[(a + b) t - a t - b t] == 0];
check["finite_aggregation_empty", Total[{}] == 0];
check["posterior_decoder_summand", FullSimplify[p q r/d == (p q/d) r, d > 0]];
check["fixed_source_difference", Expand[(t - x) - (t - y) - (y - x)] == 0];
models = {
  {{1/2, 1/2}, {{1, 0}, {0, 1}}, {{1, 0}, {0, 1}}},
  {{1/2, 1/2}, {{1, 0}, {0, 1}}, {{1}, {1}}},
  {{1, 0}, {{1/3, 2/3, 0}, {0, 0, 1}}, {{1, 0}, {0, 1}}},
  {{1/3, 2/3}, {{1/4, 3/4}, {1/2, 1/2}}, {{1/2, 1/2, 0}, {1/3, 2/3, 0}}}
};
evaluated = colorModel @@@ models;
check["finite_models_information_identity", And @@ (FullSimplify[#[[3]] == #[[1]] - #[[2]]] & /@ evaluated)];
check["finite_models_probability_marginals", AllTrue[evaluated, Total[#[[4]]] == 1 && Total[#[[5]]] == 1 && Total[Flatten[#[[6]]]] == 1 &]];
check["finite_models_decoder_normalization", And @@ Flatten[Table[If[v[[4, w]] == 0, True, Total[v[[7, w]]] == 1], {v, evaluated}, {w, Length[v[[4]]]}]]];
check["finite_models_zero_probability_boundaries", evaluated[[3, 4, 2]] == 0 && evaluated[[3, 5, 3]] == 0 && evaluated[[4, 4, 3]] == 0];
check["different_vocabulary_order", FullSimplify[evaluated[[1, 1]] == evaluated[[2, 1]] && evaluated[[1, 3]] < evaluated[[2, 3]] && evaluated[[1, 2]] > evaluated[[2, 2]]]];
check["invalid_normalization_rejected", colorModel[{1}, {{1}}, {{2}}] === $Failed];
report = <|"backend" -> "Wolfram Language", "checks" -> Length[results], "passed" -> And @@ Lookup[results, "passed"], "results" -> results|>;
Print[ExportString[report, "RawJSON"]];
If[!TrueQ[report["passed"]], Exit[1]];
