(* ::Package:: *)

(* ::Section:: *)
(*Kinematic Graphs*)


topologyRepresentative[KinematicGraph[{m_,___},__]] := With[{nE = countExternals[m]},
CanonicalGraph@reduceMultigraph[IncidenceGraph[Abs[m]]][[2]]
];


(* ::Subsection::Closed:: *)
(*Graph Building*)


(* ::Text:: *)
(*Graphs will be represented as incidence matrices, this will allow for multiple edges between two vertices. The edges will be associated to propagators and external lines. They are ordered as*)
(*{prop1, ..., external1, ..., -Total[externals]}.*)


findCircuitsExplicit[m_?MatrixQ, minValence_Integer, maxValence_Integer] := Module[{subsets = {}, testSubsets},
   Do[
   testSubsets = Subsets[Range[Length@m], {i}];
   testSubsets = Fold[DeleteCases[#1, _?(x |-> SubsetQ[x, #2])]&, testSubsets, subsets[[;;,1]]];
   testSubsets = MapAt[First,2] /@ Select[# -> NullSpace[Transpose@m[[#]]]& /@ testSubsets, #[[2]] != {}&];
   subsets = Join[subsets, testSubsets],
   {i, 2, maxValence}];
   Select[Length[#[[1]]] >= minValence&]@subsets
];


findIncidenceMatrices::usage = "Constructs all possible incidence matrices corresponding to the given set of propagators. The columns are indexed by the propagator lines and then by the external lines. Rows correspond to vertices.";
findIncidenceMatrices[props_List, loopMomenta: {_Symbol..}, externalMomenta: {_Symbol..}]:= 
  Module[{lineMomenta = Join[props, externalMomenta, {-Total[externalMomenta]}], possibleVertices, al, possibleGraphs, possibleIncidenceMatrices, matrs},
    (* Finds all possible (internal) vertices. They are in (orientated) incidence form *)
    possibleVertices = Normal@SparseArray[#, {Length[props] + Length[externalMomenta] + 1}]& /@ findCircuitsExplicit[CoefficientArrays[lineMomenta, Join[loopMomenta, externalMomenta]][[2]], 3, 1+Length[loopMomenta] + Length[externalMomenta]];
    (* Put into unorientated incidence form*)
    possibleVertices = Abs[possibleVertices];
    (* All possible graphs are combinations of vertices where externals show up once and propagators show up twice. *)
    possibleGraphs = Solve[(Table[al[i], {i, 1, Length@possibleVertices}] . possibleVertices) == Join[ConstantArray[2, Length@props], ConstantArray[1, Length[externalMomenta] + 1]], NonNegativeIntegers][[;;,;;,2]];
    (* Vertices can only show up at most once, however, and the above procedure over counts. *)
    possibleGraphs = Select[possibleGraphs, FreeQ[#,_?(#>1&)]&];
    
    (* Build incidence matrices of possible graphs, including external vertices. *)
    possibleIncidenceMatrices = Join[DeleteCases[# * possibleVertices, {0..}], ArrayFlatten[{{ConstantArray[0, {Length[externalMomenta] + 1, Length@props}], IdentityMatrix[Length[externalMomenta] + 1]}}]]& /@ possibleGraphs;
   
    (* This over counts by restricted higher loop diagrams, so we make sure that the number of loops is correct.*)
    matrs = Select[possibleIncidenceMatrices, Length[EdgeCycleMatrix@DirectedGraph[#, "Random"]&@*IncidenceGraph@#] == Length@loopMomenta &];
    
    (* The procedure then overcomputes if there is any way to relabel *fully* internal vertices and get the same graph, so we remove isomorphic things*)
    DeleteDuplicates[matrs, isomorphicQ[IncidenceGraph[#1], IncidenceGraph[#2]]&]
];


(* ::Subsection:: *)
(*Graph Routing.*)


ClearAll[orientateIncidenceMatrix];
orientateIncidenceMatrix::usage = "Takes the unorientated incidence matrix of a graph, with associated propagators and internal/external momenta and returns an orientated version.";
orientateIncidenceMatrix[m_?MatrixQ, propagators_List, internalMomenta : {_Symbol..}, externalMomenta : {_Symbol..}] := 
  Module[{IM, directionConstraints, zeroConstraints, vertexConservation, incomingConstraints, numVertices, numEdges, orientatedMatrix},
    numVertices = Length@m;
    numEdges = Length@m[[1]];
    directionConstraints = With[{edges = SparseArray[m] // Transpose // Map[First /@ #["NonzeroPositions"]&]}, 
        Table[IM[edges[[i]][[1]], i] + IM[edges[[i]][[2]], i]==0, {i, 1, Length@edges}]
    ];
    zeroConstraints = Thread[Complement[Join@@Table[IM[i,j], {i, numVertices}, {j, numEdges}], Variables[directionConstraints[[;;,1]]]]==0];
    vertexConservation = With[{internalVertices = SparseArray[m][[;;-(Length[externalMomenta]+1+1)]] // Map[First /@ #["NonzeroPositions"]&]}, 
        Join@@Table[Thread[CoefficientArrays[Sum[IM[i,j]*Join[propagators, externalMomenta, {-Total[externalMomenta]}][[j]], {j, internalVertices[[i]]}], Join[internalMomenta, externalMomenta]][[2]]["NonzeroValues"] == 0], {i, 1, Length@internalVertices}]
    ];
    incomingConstraints = Table[IM[numVertices - (i-1), numEdges - (i-1)] == -1, {i, 1, Length[externalMomenta]+1}];
    orientatedMatrix = Table[IM[i,j], {i, 1, numVertices}, {j, 1, numEdges}] /. Solve[Join[directionConstraints, zeroConstraints, vertexConservation, incomingConstraints], Join@@Table[IM[i,j], {i,1, numVertices}, {j,1, numEdges}]][[1]];
    orientatedMatrix
];


findOrientatedIncidenceMatrices::usage = "findOrientatedIncidenceMatrices[propagators_List, internalMomenta : {_Symbol..}, externalMomenta : {_Symbol..}
Finds orientated incidence matrices which correpspond to the given set of propagators.";
findOrientatedIncidenceMatrices[propagators_List, internalMomenta : {_Symbol..}, externalMomenta : {_Symbol..}] :=
    orientateIncidenceMatrix[#, propagators, internalMomenta, externalMomenta]& /@ findIncidenceMatrices[propagators, internalMomenta, externalMomenta];


(* ::Subsection:: *)
(*Graph Labelling Data Type*)


countExternals[m_?MatrixQ] := Count[Normal[m], _?(Total[Abs[#]]==1&)];


externalLabels[n_Integer] := Symbol["p" <> ToString[#]] & /@ Range[n];


cleanLabellings[incidenceMatrix_, props_, internals_] := With[{ls = labellings[incidenceMatrix, props], ints = Alternatives@@internals}, Join[Cases[ls, HoldPattern[_ -> ints]], ls[[-countExternals[incidenceMatrix];;]]]];
labellings[incidenceMatrix_, props_] := Thread[EdgeList@IncidenceGraph[incidenceMatrix] -> Join[props, externalLabels[countExternals@incidenceMatrix]]];
externalLabellings[incidenceMatrix_] := With[{nEx = countExternals@incidenceMatrix}, Thread[EdgeList[IncidenceGraph[incidenceMatrix]][[-nEx;;]] -> externalLabels[nEx]]];


Format[KinematicGraph[{m_?MatrixQ,___}, props_List, internals : {_Symbol..}]] := IncidenceGraph[m, EdgeLabels -> cleanLabellings[m, props, internals]];
Format[KinematicGraph[{m_?MatrixQ,___}, props_List, internals : {_Symbol..}, "LabellingStyle" -> "All"]] := IncidenceGraph[m, EdgeLabels -> labellings[m, props]];


(* ::Subsection:: *)
(*Isomorphisms (Clunky)*)


(* ::Text:: *)
(*We take a graph isomorphism as a remapping of the vertices and edges of a graph g1 to a graph g2. *)
(*For our purposes, Mathematica's graph isomorphism tools are too limited for two reasons:*)
(*- They find remappings only of the *vertices* between two graphs.*)
(*- They do not allow us to easily restrict to isomorphisms which leave a subset of the vertices invariant, as necessary for Feynman Graphs*)
(**)
(*We attempt to fix this here.*)


toUndirectedGraph[g_?DirectedGraphQ] := IncidenceGraph[Abs[IncidenceMatrix[g]]];


ClearAll[reduceMultigraph];
repeatedEdge[g_Graph] := With[{edges = Transpose@IncidenceMatrix@g},
  First/@edges[[First@FirstCase[{_,__}]@Utility`positionDuplicates[edges]]]["NonzeroPositions"]
];

reduceMultigraph[g_Graph] /; !MultigraphQ[g] := {{}, g};
reduceMultigraph[g_Graph] := {repeatedEdge[g], IncidenceGraph[Transpose@DeleteDuplicates@Transpose@IncidenceMatrix@g]};


applyVertexEdgeMap[{vMap_, eMap_}, m_?MatrixQ] := Transpose[Transpose[m[[InversePermutation[vMap[[;;, 2]]]]]][[InversePermutation[eMap[[;;, 2]]]]]];

ClearAll[findLoopIsomorphisms, findVertexIsomorphisms];
findVertexIsomorphisms::usage = "findVertexIsomorphisms[g1_?UndirectedGraphQ, g2_?UndirectedGraphQ, fixedVertices] returns a (potentially empty) list 
of vertex isomorphisms that keep a subset of the vertices relabelled.  Each vertex isomorphism is a list of rules 
to convert the vertex indices of g1 to the vertex indices of g2.";

findVertexIsomorphisms[g1_?UndirectedGraphQ, g2_?UndirectedGraphQ, fixedVertices : {_Integer...}] /; MultigraphQ[g1] && MultigraphQ[g2] := 
    findVertexIsomorphisms[reduceMultigraph[g1][[2]], reduceMultigraph[g2][[2]], fixedVertices];

findVertexIsomorphisms[g1_?UndirectedGraphQ, g2_?UndirectedGraphQ, fixedVertices : {_Integer...}] := 
    With[{isomorphisms = Normal@FindGraphIsomorphism[g1, g2, All]},
    Cases[isomorphisms, _?(Length@Intersection[#, # -> # & /@ fixedVertices] == Length[fixedVertices]&)]
];

associatedEdgeIsomorphism::usage = "Builds an edge isomorphism associated to a given vertex isomorphism. Note: only returns one. 
Edge list indices are associated to Transpose of incidence matrix. Result is the form of a replacement rule for edge indices of g1 to give the edge indices of g2.";
associatedEdgeIsomorphism[g1_Graph, g2_Graph, vertexIsomorphism : {_Rule..}] := Module[{m1 = IncidenceMatrix[g1], t1, m2 = IncidenceMatrix[g2], t2},
    t1 = Normal@Transpose[m1[[InversePermutation[Range[Length@vertexIsomorphism] /. vertexIsomorphism]]]];
    t2 = Normal@Transpose[m2];
    If[Sort[t1] =!= Sort[t2], Return[$Failed]];
    
    (* Work out map from t1 to t2 by mapping both to the canonical ordering. *)
    Thread[Range[Length@t1] -> InversePermutation[Ordering[t1][[InversePermutation@Ordering[t2]]]]]
];

findIsomorphisms::usage = "Finds a list of {vertexRelabelling, edgeRelabelling} that permutes the IncidenceMatrix[g1] into IncidenceMatrix[g2].";
findIsomorphisms[g1_Graph, g2_Graph, fixedVertices : {_Integer...}] := 
    DeleteCases[{#, associatedEdgeIsomorphism[g1, g2, #]}& /@ findVertexIsomorphisms[g1, g2, fixedVertices], {_, $Failed}];

findLoopIsomorphisms::usage = "Finds a list of {vertexRelabelling, edgeRelabelling} that permutes the IncidenceMatrix[g1] into IncidenceMatrix[g2], 
maintaining the external vertex labels.";
findLoopIsomorphisms[g1_Graph, g2_Graph] := With[{nExternals = countExternals[IncidenceMatrix[g1]], nVertices = Length@VertexList@g1},
        findIsomorphisms[g1, g2,  Range[nVertices - nExternals + 1, nVertices]]
    ];


ClearAll[isomorphicQ];

isomorphicQ[KinematicGraph[m1s : {_?MatrixQ..}, _, _], KinematicGraph[{g2_,___}, _, _]] := Or@@(isomorphicQ[IncidenceGraph@#, IncidenceGraph@g2]& /@ m1s);

isomorphicQ[g1_?DirectedGraphQ, g2_?DirectedGraphQ] := isomorphicQ[toUndirectedGraph@g1, toUndirectedGraph@g2];
(* Check if the multigraphness is preserved by the isomorphism. *)
isomorphicQ[g1_Graph, g2_Graph] /; MultigraphQ[g1] != MultigraphQ[g2] := False;

isomorphicQ[g1_Graph, g2_Graph] /; MultigraphQ[g1] && MultigraphQ[g2] := Module[{r1 = reduceMultigraph[g1], r2 = reduceMultigraph[g2], mappings},
    mappings = findLoopIsomorphisms[r1[[2]], r2[[2]]][[;;, 1]];
    (* Check if the repeated edge is preserved by the isomorphism. Note that edges are unordered, but stored as lists so must be sorted. *)
    If[Length@mappings > 0, Sort[(r1[[1]] /. First[mappings])] === Sort[r2[[1]]], False]
];

(* We have to hack this together a little, as mathematica cannot find isomorphisms for multigraphs. *)
isomorphicQ[g1_Graph, g2_Graph] := Length[findLoopIsomorphisms[g1, g2]] > 0;


(* ::Subsection::Closed:: *)
(*External Remappings*)


findExternalIsomorphisms[KinematicGraph[{m1_, ___}, _, _], KinematicGraph[{m2_, ___}, _, _]] := 
    With[{g1 = IncidenceGraph@Abs@m1, g2 = IncidenceGraph@Abs@m2, nExt = countExternals[m1], nVertices = Length[m1]},
        findVertexIsomorphisms[g1, g2, {}][[;;, -nExt;;]] /. i_Integer :> i-nVertices + nExt
    ];


(* ::Subsection::Closed:: *)
(*Loop Momentum Remappings*)


ClearAll[findLoopRemappings];
findLoopRemappings::usage = "findLoopRemappings[g1_?DirectedGraphQ, g2_?DirectedGraphQ, props1_List, props2_List, internals : {_Symbol..}, externals : {_Symbol..}].
findLoopRemappings[props1_List, props2_List, internals : {_Symbol..}, externals : {_Symbol..}]

Finds remappings of the loop momenta of the first integrand onto the second integrand.
";

(*isomorphismToRerouting[{vMap_, eMap_}, g1_?DirectedGraphQ, g2_?DirectedGraphQ, props1_List, props2_List, internals : {_Symbol..}] := 
    Module[{loopEdgeRemap, loopEdges1, loopEdges2, remappingSigns},
    loopEdgeRemap = eMap[[First@FirstPosition[props1, #, Missing["NotFound"], {1}, Heads->False]]]& /@ internals;
    loopEdges1 = EdgeList[g1][[#]] & /@ loopEdgeRemap[[;;, 1]];
    loopEdges2 = EdgeList[g2][[#]] & /@ loopEdgeRemap[[;;, 2]];
    remappingSigns = If[#, 1, -1]& /@ SameQ@@@Thread[{loopEdges1 /. vMap, loopEdges2}];
    remappingSigns*(props2[[#]]& /@ loopEdgeRemap[[;;,2]])
];*)

isomorphismSigns::usage = "isomorphismSigns[{vMap, eMap}, g1_?DirectedGraphQ, g2_?DirectedGraphQ] finds a list of signs that need to be 
applied alongside the isomorphism to match the directions of the edges.";
isomorphismSigns[{vMap_, eMap_}, g1_?DirectedGraphQ, g2_?DirectedGraphQ] := Module[{m1=IncidenceMatrix[g1], m2=IncidenceMatrix[g2]},
    Which[#[[1]] == #[[2]], 1, #[[1]] == -#[[2]], -1, True, $Failed]& /@ Thread[{Transpose[applyVertexEdgeMap[{vMap, eMap}, m1]], Transpose[m2]}]
];

isomorphismToRerouting[{vMap_, eMap_}, g1_?DirectedGraphQ, g2_?DirectedGraphQ, props1_List, props2_List, internals : {_Symbol..}] := 
    Module[{signs, eqs, nExternals = countExternals[IncidenceMatrix[g1]], internalSymbols = Unique[]& /@ internals},
        signs = isomorphismSigns[{vMap, eMap}, g1, g2][[;; -(nExternals + 1)]];
        eqs = (props1 /. Thread[internals -> internalSymbols]) == (signs*props2)[[eMap[[;; -(nExternals + 1),2]]]];
        Solve[eqs, internalSymbols][[1, ;;, 2]]
];

findLoopRemappings[g1_?DirectedGraphQ, g2_?DirectedGraphQ, props1_List, props2_List, internals : {_Symbol..}] := 
    Module[{graphRemappings},
    graphRemappings = findLoopIsomorphisms[toUndirectedGraph@g1, toUndirectedGraph@g2];
    isomorphismToRerouting[#, g1, g2, props1, props2, internals]& /@ graphRemappings
];

findLoopRemappings[props1_List, props2_List, internals : {_Symbol..}, externals : {_Symbol..}] := 
    findLoopRemappings[#1, #2, props1, props2, internals]&@@(
        graphFromPropagators[#, internals, externals, "LabelStyle" -> "All", "Orientated" -> True]& /@ {props1, props2}
    );
    
findLoopRemappings[KinematicGraph[m1s : {_?MatrixQ..}, props1_List, internals : {_Symbol..}], 
                  KinematicGraph[{m2_?MatrixQ,___}, props2_List, internals : {_Symbol..}]] :=              
    Join @@ (findLoopRemappings[IncidenceGraph@#, IncidenceGraph@m2, props1, props2, internals]& /@ m1s);


(* ::Subsection::Closed:: *)
(*Edge Contraction*)


(* ::Text:: *)
(*Mainly simple stuff built to work on the incidence matrix.*)


edgeIndices[m_?MatrixQ, i_\[UndirectedEdge]j_] := With[{edges = Normal[Transpose[m]]}, First /@ Position[edges, ReplacePart[{i->Except[0], j->Except[0]}]@ConstantArray[0,Length@First@edges]]];


removeEdge[m_?MatrixQ, edge_Integer] := Transpose@Delete[Transpose[m], edge];


contractEdge[m_?MatrixQ, edge_Integer] := removeEdge[With[{vs = Position[Normal[Transpose[m]][[edge]], Except[0], {1}, Heads->False]}, Append[Total[m[[#[[1]]]]& /@ vs]]@Delete[m, Reverse@Sort@vs]],edge];
contractEdges[m_?MatrixQ, edges : {_Integer..}] := Fold[contractEdge[#1, #2]&, m, Reverse@Sort@edges];


loopIndices[m_?MatrixQ] := Join@@(DeleteDuplicatesBy[#, Sort]&@*Select[CountDistinct@#==Length@#&]@*Tuples@*Map[edgeIndices[m, #]&] /@ FindCycle[IncidenceGraph@m, Infinity, All]);
loopContractions[m_?MatrixQ] := contractEdges[m, #]& /@ loopIndices[m];


(* ::Subsection:: *)
(*Interface*)


(* ::Subsubsection:: *)
(*Simplistic*)


ClearAll[graphFromPropagators];
(* Label only one edge per loop. *)
graphFromPropagators[props_, internals_, externals_] := IncidenceGraph[#, EdgeLabels -> cleanLabellings[#, props, internals]]& @ findOrientatedIncidenceMatrices[props, internals, externals][[1]];


(* ::Subsubsection:: *)
(*KinematicGraph Interface*)


buildKinematicGraph[propagators_List, internals : {_Symbol..}, externals : {_Symbol..}] := 
    KinematicGraph[SparseArray /@ findOrientatedIncidenceMatrices[propagators, internals, externals], propagators, internals];


denominators[KinematicGraph[_, dens_, _]] := dens;
