(* ::Package:: *)

invariantsnod={mTsq,s12,s16,s345};
invariantsnodUpperCase={MTsq,S12,S16,S345};

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
s12-(p[1]+p[2])^2,
s16-(p[2]+p[3])^2,
mTsq-(p[4])^2,
s345-(p[3])^2,
(p[1])^2,
(p[2])^2
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
	invariantsnod2={mTsq,s12,s16,s345};
	mandelstamScalarProductsT=Expand[mandelstamScalarProducts/.tpoint,Modulus->$P];
	InvariantsConstraintsCheck={(p[1])^2,(p[2])^2,(p[3])^2,(p[4])^2,(p[1]+p[2])^2,(p[2]+p[3])^2};
	InvariantsMandsCheck={0,0,s345,mTsq,s12,s16};
	For[i=1,i<=Length[invariantsnod2],i++,
		diffopS[invariantsnod2[[i]]]=Coefficient[Expand[diffop],ds[invariantsnodUpperCase[[i]]]];
	];
	CheckMatrix=Table[diffopS[invariantsnod2[[j]]]/.del[x_]:>D[InvariantsConstraintsCheck[[i]],x],{i,1,Length[InvariantsConstraintsCheck]},{j,1,Length[invariantsnod2]}];
	CheckMatrix=Expand[Expand[CheckMatrix/.p4conv]/.mandelstamScalarProductsT,Modulus->$P];
	MatrixPlot[CheckMatrix,GridLines->Automatic,FrameTicks -> 
   {{Transpose[ArrayReshape[Append[Range[1,6],InvariantsMandsCheck]//Flatten,{2,6}]], Transpose[ArrayReshape[Append[Range[1,6],InvariantsMandsCheck]//Flatten,{2,6}]]}, {Transpose[ArrayReshape[Append[Range[1,Length[invariantsnod2]],invariantsnod2]//Flatten,{2,Length[invariantsnod2]}]], Transpose[ArrayReshape[Append[Range[1,Length[invariantsnod2]],invariantsnod2]//Flatten,{2,Length[invariantsnod2]}]]}}]//Echo;
	CheckMatrix//MatrixForm//Echo;
]
