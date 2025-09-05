(* ::Package:: *)

kinematics={p[1]^2->0,p[2]^2->0,p[3]^2->0,p[4]^2->0,p[5]^2->mt2};
mandelstamScalarProducts=Get[FileNameJoin[{Directory[],"files/mandelstam_scalarproducts.txt"}]];
mandelstamScalarProducts=Join[kinematics,mandelstamScalarProducts]
invariantsnod={mt2,s12,s123,s16,s23,s234,s34,s345,s45,s56};
invariantsnodUpperCase={Mt2,S12,S123,S16,S23,S234,S34,S345,S45,S56};

p4conv={p[6]->-(p[1]+p[2]+p[3]+p[4]+p[5])};
$P=2^31-1;


(* ::Title:: *)
(*Differential Operator Ansatz*)


diffOpAnsatz[expr_] := Module[{v1},
	  v1 = Sum[da[j, i]*p[j]*D[expr, p[i]], {i, 1, 6}, {j, 1, 4}];
	  v1 = v1 + Sum[ds[invariantsnodUpperCase[[i]]]*D[expr, invariantsnod[[i]]], {i, 1, Length[invariantsnod]}];
	  Return[v1];
	  ];


diffOpAnsatz2 =Sum[da[j, i]*p[j]*del[p[i]], {i, 1, 6}, {j, 1, 4}] + Sum[ds[invariantsnodUpperCase[[i]]]*del[invariantsnod[[i]]], {i, 1, Length[invariantsnod]}];


(* ::Title:: *)
(*Constraints*)


operatorConstraints={
s12-(p[1]+p[2])^2,
s23-(p[2]+p[3])^2,
s34-(p[3]+p[4])^2,
s45-(p[4]+p[5])^2,
s56-(p[5]+p[6])^2,
s16-(p[1]+p[6])^2,
s123-(p[1]+p[2]+p[3])^2,
s234-(p[2]+p[3]+p[4])^2,
s345-(p[3]+p[4]+p[5])^2,
(p[1])^2,
(p[2])^2,
(p[3])^2,
(p[4])^2,
mt2-(p[5])^2,
mt2-(p[6])^2
};
diffOpConst=Expand[Thread[diffOpAnsatz[operatorConstraints]]/.p4conv];
p4diffopConst=Table[Expand[p[i]diffOpAnsatz[p[1]+p[2]+p[3]+p[4]+p[5]+p[6]]/.p4conv],{i,1,4}];
EQNSystemDiffOp=Join[diffOpConst,p4diffopConst];
solsetDiffOp=Cases[EQNSystemDiffOp,_da,Infinity]//DeleteDuplicates;
solsetDiffOp=Join[solsetDiffOp,{ds[S16]}]


(* ::Title:: *)
(*Solve Linear System*)


getDifferentialOperator[tpoint_] := Module[{EQNSystemDiffOpT,solDiffOp,kinematicsT,mandelstamScalarProductsT,NullsetDiffOp,NullRulesDiffOp,differentialOperator},
	kinematicsT=Expand[kinematics/.tpoint,Modulus->$P];
	mandelstamScalarProductsT=Expand[mandelstamScalarProducts/.tpoint,Modulus->$P];
	EQNSystemDiffOpT=Expand[EQNSystemDiffOp/.kinematicsT/.mandelstamScalarProductsT,Modulus->$P];
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
	(*invariantsnod2={s12,s23,s34,s45,s56,s16,s123,s234,s345,mt2};*)
	invariantsnod2={mt2,s12,s123,s16,s23,s234,s34,s345,s45,s56};
	kinematicsT=Expand[kinematics/.tpoint,Modulus->$P];
	mandelstamScalarProductsT=Expand[mandelstamScalarProducts/.tpoint,Modulus->$P];
	InvariantsConstraintsCheck={(p[1]+p[2])^2,(p[2]+p[3])^2,(p[3]+p[4])^2,(p[4]+p[5])^2,(p[5]+p[6])^2,(p[1]+p[6])^2,(p[1]+p[2]+p[3])^2,(p[2]+p[3]+p[4])^2,(p[3]+p[4]+p[5])^2,(p[1])^2,
	(p[2])^2,(p[3])^2,(p[4])^2,(p[5])^2,(p[6])^2};
	InvariantsMandsCheck={s12,s23,s34,s45,s56,s16,s123,s234,s345,0,0,0,0,mt2,mt2};
	For[i=1,i<=Length[invariantsnod2],i++,
		diffopS[invariantsnod2[[i]]]=Coefficient[Expand[diffop],ds[invariantsnodUpperCase[[i]]]];
	];
	CheckMatrix=Table[diffopS[invariantsnod2[[j]]]/.del[x_]:>D[InvariantsConstraintsCheck[[i]],x],{i,1,Length[InvariantsConstraintsCheck]},{j,1,Length[invariantsnod2]}];
	CheckMatrix=Expand[Expand[CheckMatrix/.p4conv]/.kinematicsT/.mandelstamScalarProductsT,Modulus->$P];
	MatrixPlot[CheckMatrix,GridLines->Automatic,FrameTicks -> 
   {{Transpose[ArrayReshape[Append[Range[1,15],InvariantsMandsCheck]//Flatten,{2,15}]], Transpose[ArrayReshape[Append[Range[1,15],InvariantsMandsCheck]//Flatten,{2,15}]]}, {Transpose[ArrayReshape[Append[Range[1,Length[invariantsnod2]],invariantsnod2]//Flatten,{2,Length[invariantsnod2]}]], Transpose[ArrayReshape[Append[Range[1,Length[invariantsnod2]],invariantsnod2]//Flatten,{2,Length[invariantsnod2]}]]}}]//Echo;

	loopMomentumScalarProducts=Get[FileNameJoin[{Directory[],"files/loopmomentum_scalarproducts.txt"}]];
	momenta={p[1],p[2],p[3],p[4],p[5]};
	SixPointGram=Expand[Det[Table[momenta[[i]] momenta[[j]],{i,1,5},{j,1,5}]/.kinematics/.mandelstamScalarProducts/.loopMomentumScalarProducts]];
	
	SixPointGram=Expand[Det[Table[momenta[[i]] momenta[[j]],{i,1,5},{j,1,5}]/.kinematics/.mandelstamScalarProducts/.loopMomentumScalarProducts]];	
	Print[StringForm["\[CapitalDelta]6=``",Expand[SixPointGram/.tpoint,Modulus->$P]]];
	For[i=1,i<=Length[invariantsnod2],i++,
		dSixPointGram=Expand[((diffopS[invariantsnod2[[i]]]/.del[x_]:>D[SixPointGram,x])/.p4conv//Expand)/.kinematics/.mandelstamScalarProducts/.tpoint,Modulus->$P];	
		Print[StringForm["\!\(\*SubscriptBox[\(\[PartialD]\), \(``\)]\)\[CapitalDelta]6=``",invariantsnod2[[i]],dSixPointGram]];
	];
	
]
