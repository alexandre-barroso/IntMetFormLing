ClearAll[transition, final, outputs, target, inductionCertificate, check];
alphabet = {"t", "a", "d"};
transition[2, _] := {};
transition[q : (0 | 1), "t"] := {{0, "t"}};
transition[q : (0 | 1), "a"] := {{0, "a"}};
transition[q : (0 | 1), "d"] := {{1, "d"}, {2, "t"}};
final = {0, 2};
outputs[q_, {}] := If[MemberQ[final, q], {{}}, {}];
outputs[q_, word_List] /; Length[word] > 0 := Flatten[Map[Function[edge, Prepend[#, edge[[2]]] & /@ outputs[edge[[1]], Rest[word]]], transition[q, First[word]]], 1];
target[{}] := {};
target[word_List] /; Length[word] > 0 := Append[Most[word], If[Last[word] === "d", "t", Last[word]]];
inductionCertificate[] := Module[{tail, expanded},
 If[! And @@ Table[transition[0, c] === transition[1, c], {c, alphabet}], Return[False]];
 If[! And @@ Table[transition[2, c] === {}, {c, alphabet}], Return[False]];
 If[outputs[0, {}] =!= {{}}, Return[False]];
 If[! And @@ Table[outputs[0, {c}] === {target[{c}]}, {c, alphabet}], Return[False]];
 tail = {SymbolicDevoicedNonemptyTail};
 And @@ Table[
  expanded = Flatten[Map[Function[edge, If[MemberQ[{0, 1}, edge[[1]]], {Prepend[tail, edge[[2]]]}, {}]], transition[0, c]], 1];
  expanded === {Prepend[tail, c]}, {c, alphabet}]
];
results = {};
check[name_, condition_] := If[TrueQ[condition], AppendTo[results, name], Print[name]; Exit[1]];
check["finite_transition_structural_induction", inductionCertificate[]];
check["published_tad", outputs[0, Characters["tad"]] === {Characters["tat"]}];
check["published_tada", outputs[0, Characters["tada"]] === {Characters["tada"]}];
check["empty_input", outputs[0, {}] === {{}}];
check["terminal_state_cannot_continue", And @@ Table[transition[2, c] === {}, {c, alphabet}]];
final = {0, 1, 2};
check["changed_acceptance_rejected", ! inductionCertificate[]];
final = {0, 2};
transition[2, "a"] = {{0, "a"}};
check["continuation_after_devoicing_rejected", ! inductionCertificate[]];
Print[ExportString[<|"passed" -> True, "checks" -> Length[results], "results" -> results, "scope" -> "Exhaustive finite transition cases and a symbolic arbitrary nonempty tail establish the structural induction; no upper bound on word length is sampled."|>, "RawJSON"]];
