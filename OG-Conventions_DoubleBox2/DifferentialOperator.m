(* ::Package:: *)

invariantsnod={mTsq,s15,s23,s45};
invariantsnodUpperCase={MTsq,S15,S23,S45};

p4conv={p[4]->-(p[1]+p[2]+p[3])};


(* ::Title:: *)
(*Differential Operator Ansatz*)


diffOpAnsatz[expr_] := Module[{v1},
	  v1 = Sum[da[j, i]*p[j]*D[expr, p[i]], {i, 1, 4}, {j, 1, 3}];
	  v1 = v1 + Sum[ds[invariantsnodUpperCase[[i]]]*D[expr, invariantsnod[[i]]], {i, 1, Length[invariantsnod]}];
	  Return[v1];
	  ];


diffOpAnsatz2 =Sum[da[j, i]*p[j]*del[p[i]], {i, 1, 4}, {j, 1, 3}] + Sum[ds[invariantsnodUpperCase[[i]]]*del[invariantsnod[[i]]], {i, 1, Length[invariantsnod]}];


(* ::Title:: *)
(*Constraints*)


operatorConstraints={
s15-(p[1]+p[4])^2,
s45-(p[1]+p[2])^2,
s45-(p[1]+p[2])^2,
mTsq-(p[1])^2,
s23-(p[2])^2,
(p[3])^2,
(p[4])^2
};
diffOpConst=Expand[Thread[diffOpAnsatz[operatorConstraints]]/.p4conv];
p4diffopConst=Table[Expand[p[i]diffOpAnsatz[p[1]+p[2]+p[3]+p[4]]/.p4conv],{i,1,3}];
EQNSystemDiffOp=Join[diffOpConst,p4diffopConst];
solsetDiffOp=Cases[EQNSystemDiffOp,_da,Infinity]//DeleteDuplicates;


(* ::Title:: *)
(*Solve Linear System*)


getDifferentialOperator[tpoint_] := Module[{EQNSystemDiffOpT,solDiffOp,kinematicsT,mandelstamScalarProductsT,NullsetDiffOp,NullRulesDiffOp,differentialOperator},
	mandelstamScalarProductsT=Expand[mandelstamScalarProducts/.tpoint,Modulus->$P];
	EQNSystemDiffOpT=Expand[EQNSystemDiffOp/.mandelstamScalarProductsT,Modulus->$P];
	Thread[EQNSystemDiffOpT==0];
	solDiffOp=Quiet[Solve[Thread[EQNSystemDiffOpT==0],solsetDiffOp,Modulus->$P][[1]]];
	NullsetDiffOp=Cases[solDiffOp[[All,2]],_da,Infinity]//DeleteDuplicates;
	NullRulesDiffOp=Thread[Rule[NullsetDiffOp,0]];
	solDiffOp=Join[solDiffOp/.NullRulesDiffOp,NullRulesDiffOp];
	differentialOperator=diffOpAnsatz2/.solDiffOp;
	Return[differentialOperator];
];


(* ::Title:: *)
(*Test Differential Operator*)


checkDifferentialOperator[tpoint_,diffop_] := Module[{diffopS,invariantsnod2,InvariantsConstraintsCheck,InvariantsMandsCheck,CheckMatrix,kinematicsT,mandelstamScalarProductsT},
	invariantsnod2={mTsq,s15,s23,s45};
	mandelstamScalarProductsT=Expand[mandelstamScalarProducts/.tpoint,Modulus->$P];
	InvariantsConstraintsCheck={(p[1])^2,(p[3])^2,(p[4])^2,(p[1]+p[4])^2,(p[2])^2,(p[1]+p[2])^2};
	InvariantsMandsCheck={mTsq,0,0,s15,s23,s45};
	For[i=1,i<=Length[invariantsnod2],i++,
		diffopS[invariantsnod2[[i]]]=Coefficient[Expand[diffop],ds[invariantsnodUpperCase[[i]]]];
	];
	CheckMatrix=Table[diffopS[invariantsnod2[[j]]]/.del[x_]:>D[InvariantsConstraintsCheck[[i]],x],{i,1,Length[InvariantsConstraintsCheck]},{j,1,Length[invariantsnod2]}];
	CheckMatrix=Expand[Expand[CheckMatrix/.p4conv]/.mandelstamScalarProductsT,Modulus->$P];
	MatrixPlot[CheckMatrix,GridLines->Automatic,FrameTicks -> 
   {{Transpose[ArrayReshape[Append[Range[1,6],InvariantsMandsCheck]//Flatten,{2,6}]], Transpose[ArrayReshape[Append[Range[1,6],InvariantsMandsCheck]//Flatten,{2,6}]]}, {Transpose[ArrayReshape[Append[Range[1,Length[invariantsnod2]],invariantsnod2]//Flatten,{2,Length[invariantsnod2]}]], Transpose[ArrayReshape[Append[Range[1,Length[invariantsnod2]],invariantsnod2]//Flatten,{2,Length[invariantsnod2]}]]}}]//Echo;
	CheckMatrix//MatrixForm//Echo;
]
