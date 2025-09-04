(* ::Package:: *)

kinematics={p[1]^2->0,p[2]^2->0,p[3]^2->0,p[4]^2->0,p[5]^2->mt2};
p4cons={p[6]->-p[1]-p[2]-p[3]-p[4]-p[5]};
loopMomentumScalarProducts=Get[FileNameJoin[{Directory[],"files/loopmomentum_scalarproducts.txt"}]];
mandelstamScalarProducts=Get[FileNameJoin[{Directory[],"files/mandelstam_scalarproducts.txt"}]];
LaportaBasis=ReadList[FileNameJoin[{Directory[],"files/D4MIs_Sorted.txt"}]];
LinSysAna=ReadList[FileNameJoin[{Directory[],"files/LinearSystem.txt"}]];
allMIs=ReadList[FileNameJoin[{Directory[],"files/G60Masters.txt"}]];
invariants={d,mt2,s12,s123,s16,s23,s234,s34,s345,s45,s56};

InvariantsConvChange={p1s->s56,s12->s123,s23->s34,s34->s23,s45->s12,s15->s234};
tr5Exp = Sqrt[(-s12*s15 + s12*s23 + p1s*s34 + s15*s45 -s34*s45 -s23*s34)^2 - 4*s23*s34*s45*(p1s - s12 - s15 + s34)]/.InvariantsConvChange; (* \sqrt{\Delta_5}*)
sqrtG3Exp = Sqrt[p1s^2 + (s23 - s45)^2 - 2*p1s*(s23 + s45)]/.InvariantsConvChange;

invariantConvChange={s23->s345,s45->s12,s15->s16,mTsq->mt2};
sqrtG3DB=Sqrt[(-mTsq+s23-s45)^2-4 mTsq s45]/.invariantConvChange;

Ureduce=ReadList[FileNameJoin[{Directory[],"KIRA/UReduList.txt"}]];






(* ::Title:: *)
(*Generate Random PhaseSpace Point*)


momenta={p[1],p[2],p[3],p[4],p[5]};
SixPointGram=Expand[Det[Table[momenta[[i]] momenta[[j]],{i,1,5},{j,1,5}]/.kinematics/.mandelstamScalarProducts/.loopMomentumScalarProducts]];
sqrtSet={tr5Exp,sqrtG3Exp,sqrtG3DB}/.Sqrt[x_]:>x
GetRandomPT[NMin_,NMax_]:=Module[{tPoint,tPointReplacements,sqrtSetT,roots,NMAXIT,s16Sol},    
    NMAXIT=1000000;
    For[i = 0, i < NMAXIT, i++,
		tPoint=RandomInteger[{NMin,NMax},Length[DeleteElements[invariants,{s16}]]];
		tPointReplacements=Thread[Rule[DeleteElements[invariants,{s16}],tPoint]];
		s16Sol=Solve[Expand[SixPointGram/.tPointReplacements,Modulus->$P]==0,s16,Modulus->$P];
		If[Length[s16Sol]>0, 
		sqrtSetT = Expand[sqrtSet /. tPointReplacements, Modulus -> $P];
        roots = JacobiSymbol[#, $P] & /@ sqrtSetT;
        If[Total[roots] == Length[roots],
            Return[SortBy[Join[tPointReplacements,{s16Sol[[1,1]]}],First]];];
		];
 ];
 Return[{}];
]



(* ::Title:: *)
(*KIRA SET UP*)


DeleteOldKiraRun[]:=Module[{},
	Quiet[DeleteFile[FileNameJoin[{Directory[],"KIRA/kira.log"}]]];
	Quiet[DeleteDirectory[FileNameJoin[{Directory[],"KIRA/tmp"}],DeleteContents -> True]];
	Quiet[DeleteDirectory[FileNameJoin[{Directory[],"KIRA/sectormappings"}],DeleteContents -> True]];
	Quiet[DeleteDirectory[FileNameJoin[{Directory[],"KIRA/results"}],DeleteContents -> True]];
	Quiet[DeleteDirectory[FileNameJoin[{Directory[],"KIRA/splitres"}],DeleteContents -> True]];
	Quiet[DeleteFile[FileNameJoin[{Directory[],"KIRA/numerics"}]]];
];
WriteNumericsFile[tPointReplacements_]:=Module[{vars,vals,file,varsString,valsString},
	vars=tPointReplacements[[All,1]];
	vals=tPointReplacements[[All,2]];
	varsString=StringDrop[ToString[StringJoin[Table[StringJoin[ToString[vars[[i]]]," "],{i,1,Length[vars]}]]],-1];
	valsString=StringDrop[ToString[StringJoin[Table[StringJoin[ToString[vals[[i]]]," "],{i,1,Length[vals]}]]],-1];	
	file=OpenAppend[FileNameJoin[{Directory[],"/KIRA/numerics"}]];
	WriteString[file,ToString[StringForm["prime ``\n",$P]]];
	WriteString[file,ToString[StringForm["``\n",varsString]]];
	WriteString[file,ToString[StringForm["``\n",valsString]]];
	Close[file];
];
AddToNumericsFile[tPointReplacements_]:=Module[{vars,vals,file,varsString,valsString},
	vars=tPointReplacements[[All,1]];
	vals=tPointReplacements[[All,2]];
	varsString=StringDrop[ToString[StringJoin[Table[StringJoin[ToString[vars[[i]]]," "],{i,1,Length[vars]}]]],-1];
	valsString=StringDrop[ToString[StringJoin[Table[StringJoin[ToString[vals[[i]]]," "],{i,1,Length[vals]}]]],-1];		
	file=OpenAppend[FileNameJoin[{Directory[],"/KIRA/numerics"}]];
	WriteString[file,ToString[StringForm["``\n",valsString]]];
	Close[file];
];


GenerateSectorsFromReductionList[filePath_]:=Module[{ReduList,ReduListT,Sectors,SectorInts,r,s,d,sectorString,file,pos,sectorpath,directorypath},
ReduList=ReadList[filePath];
ReduListT=ReduList/.hxb[n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_,n10_,n11_,n12_,n13_]:>{n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13};
Sectors=ReduListT/.( n_Integer:>0/;n<0)/.( n_Integer:>1/;n>1) //DeleteDuplicates;
directorypath=StringDrop[filePath,Last[Last[StringPosition[filePath,"/"]]];;];
sectorpath=StringJoin[{directorypath,"/",FileBaseName[filePath],"_sector"}];
Quiet[DeleteFile[sectorpath]];

For[pos=1,pos<=Length[Sectors],pos++,
	Sectors[[pos]];
	SectorInts=ReduListT[[Sequence@@#]]&/@Position[ReduListT/.( n_Integer:>0/;n<0)/.( n_Integer:>1/;n>1) ,Sectors[[pos]]];
	SectorInts;
	r=Max[Table[Total[Select[SectorInts[[i]],Positive]],{i,1,Length[SectorInts]}]];
	s=Max[-Table[Total[Select[SectorInts[[i]],Negative]],{i,1,Length[SectorInts]}]];
	d=Max[Total[Thread[((SectorInts-1)/.( n_Integer:>0/;n<0))]]];
	sectorString=StringForm["b``",ToString[StringJoin[Table[ToString[Sectors[[pos,i]]],{i,1,Length[Sectors[[pos]]]}]]]];
	
	file=OpenAppend[sectorpath];
	WriteString[file,ToString[StringForm["      - {topologies: [hxb], sectors: [``],r: ``,s: ``,d: ``}\n",sectorString,r,s,d]]];
	Close[file];
];
];
WriteJobFile[redulists_]:=Module[{filePath,directorypath,sectorpath,lists,redufilesectors,readline,i},
	filePath=FileNameJoin[{Directory[],"KIRA/jobs.yaml"}];
	directorypath=StringDrop[filePath,Last[Last[StringPosition[filePath,"/"]]];;];
	DeleteFile[filePath];
	file=OpenAppend[filePath];
	WriteString[file,"jobs:\n"];
	WriteString[file," - reduce_sectors:\n"];
	WriteString[file,"    reduce:\n"];
	For[lists=1,lists<=Length[redulists],lists++,
		redufilesectors=OpenRead[StringJoin[{directorypath,"/",redulists[[lists]],"_sector"}]];
		For[i=1,i<=10000,i++,
			readline=ReadLine[redufilesectors];
			If[readline===EndOfFile,
				Break[];
				Close[redufilesectors];,
				WriteString[file,StringJoin[readline,"\n"]];
			];
			];
				
	];
	WriteString[file,"    select_integrals:\n"];
	WriteString[file,"     select_mandatory_list:\n"];
	For[lists=1,lists<=Length[redulists],lists++,
		WriteString[file,ToString[StringForm["      - [``.txt]\n",redulists[[lists]]]]];	
	];
	WriteString[file,"    run_initiate: true\n"];
	WriteString[file,"    numerical_points: numerics\n"];
	WriteString[file,"    run_firefly: true\n"];
];


(* ::Title:: *)
(*Solve LinearSystem from Extra Relations*)


GetExtraRelationReplacementsFromPath[numericalpath_,tPointReplacements_]:=Module[{ReduList,LinSys,Reduction,subset,Remove1L,solset,linsysBasis,sortedBasis,LinSysMatrix,NS,RemBasisN,RemBasis,SubsInts,D4ExtraRelations},
	LinSys=LinSysAna/.tPointReplacements//EchoFunction[Length];
	Reduction=GetReductionTableFromFile[numericalpath];
	Return[GetExtraRelationReplacements[Reduction,tPointReplacements]];
];
GetExtraRelationReplacements[Reduction_,tPointReplacements_]:=Module[{ReduList,LinSys,subset,Remove1L,solset,linsysBasis,sortedBasis,LinSysMatrix,NS,RemBasisN,RemBasis,SubsInts,D4ExtraRelations},
	LinSys=LinSysAna/.tPointReplacements;
	LinSys=Expand[LinSys/.Reduction,Modulus->$P];
	subset=Cases[LinSys,hxb[___],Infinity]//DeleteDuplicates;
	Remove1L=Thread[Rule[Complement[subset,allMIs],0]];
	LinSys=LinSys/.Remove1L;
	solset={hxb[0,1,1,1,0,1,1,1,1,0,0,0,0],hxb[0,1,0,1,1,1,1,1,1,0,0,0,0],hxb[1,1,1,1,0,1,1,1,1,0,0,0,0],hxb[1,1,0,1,1,1,1,1,-1,0,0,0,0],hxb[1,1,1,1,0,1,1,1,-1,0,0,0,0],hxb[1,1,1,1,0,1,1,1,0,0,0,-1,0],hxb[1,1,1,1,1,0,0,1,1,0,0,0,0],hxb[1,1,1,1,1,0,1,0,1,0,0,0,0],hxb[1,1,1,1,1,1,1,1,0,0,-1,0,0],hxb[1,1,1,1,1,1,1,1,1,-1,0,0,0],hxb[1,1,1,1,1,1,1,1,1,0,0,0,-1],hxb[1,1,1,1,1,1,0,-1,1,0,0,0,0]};
	linsysBasis=Cases[LinSys,_hxb,Infinity]//DeleteDuplicates;
	sortedBasis=Join[solset,Complement[linsysBasis,solset]];
	LinSysMatrix=Table[Coefficient[LinSys[[j]],sortedBasis[[i]]],{j,1,Length[LinSys]},{i,1,Length[linsysBasis]}];
	NS=NullSpace[LinSysMatrix,Modulus->$P]; 
	RemBasisN=Table[Last[Position[NS[[i]],1]],{i,1,Length[NS]}];
	RemBasis=sortedBasis[[Sequence@@#]]&/@RemBasisN;
	SubsInts=Delete[sortedBasis,RemBasisN];
	D4ExtraRelations=Thread[Rule[SubsInts,Table[Total[RemBasis*NS[[All,i]]],{i,1,Length[SubsInts]}]]];
	Return[D4ExtraRelations]
];
GetReductionTableFromFile[numericalpath_]:=Module[{ReduList,Reduction},
	ReduList=Get[numericalpath];
	Reduction=Table[Rule[ReduList[[2,2,pos,1]],Sum[ReduList[[2,2,pos,i,1]]*ReduList[[2,2,pos,i,2]],{i,2,Length[ReduList[[2,2,pos]]]}]],{pos,1,Length[ReduList[[2,2]]]}];
	Return[Reduction];
];
GetReductionTableFromList[ReduSublist_]:=Module[{Reduction},
	Reduction=Table[Rule[ReduSublist[[pos,1]],Sum[ReduSublist[[pos,i,1]]*ReduSublist[[pos,i,2]],{i,2,Length[ReduSublist[[pos]]]}]],{pos,1,Length[ReduSublist]}];
	Return[Reduction];
];


(* ::Title:: *)
(*Propagators*)


Pr[1]=(k[1])^2
Pr[2]=(k[1]+p[1])^2
Pr[3]=(k[1]+p[1]+p[2])^2
Pr[4]=(k[2]-k[1])^2
Pr[5]=(k[2]+p[1]+p[2])^2
Pr[6]=(k[2]+p[1]+p[2]+p[3])^2
Pr[7]=(k[2]+p[1]+p[2]+p[3]+p[4])^2
Pr[8]=(k[2]+p[1]+p[2]+p[3]+p[4]+p[5])^2-mt2
Pr[9]=(k[2])^2
Pr[10]=(k[1]+p[3])^2
Pr[11]=(k[1]+p[4])^2
Pr[12]=(k[1]+p[5])^2
Pr[13]=(k[2]+p[1])^2

InternalMometa={k[1],k[2]}
ExternalMometa={p[1],p[2],p[3],p[4],p[5]}


(* ::Title:: *)
(*HXB Definitions*)


Propdiff[n_,q_,integral_]:=Module[{newint},
	newint=(integral/.{hxb->List});
	newint[[n]]-=q;
	Return[newint/.{List->hxb}];
]
hxb/:Power[PR[n_],q_]*hxb[n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_,n10_,n11_,n12_,n13_]:=Propdiff[n,q,hxb[n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13]];
hxb/:PR[n_]*hxb[n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_,n10_,n11_,n12_,n13_]:=Propdiff[n,1,hxb[n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13]];
hxb/: delHXB[x_]*hxb[n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_,n10_,n11_,n12_,n13_] := Sum[-{n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13}[[i]]*PR[i]^-1 hxb[n1,n2,n3,n4,n5,n6,n7,n8,n9,n10,n11,n12,n13]*D[Pr[i], x], {i, 1, 13}];


applyDifferentialOperatorPart[DiffInt_,difvar_]:=Module[{apearingintegrals,v1,constfactor,i,posconst,constDiff},
apearingintegrals=Cases[{DiffInt},_hxb,Infinity]//DeleteDuplicates;
constfactor=CoefficientRules[DiffInt,Join[apearingintegrals,{hxb[0,0,0,0,0,0,0,0,0,0,0,0,0]}]];
posconst=Position[constfactor,Table[0,{i,1,Length[apearingintegrals]+1}]];
constDiff=0;
If[Length[posconst]>0,
	constfactor=constfactor[[posconst[[1,1]],2]];
	constDiff=D[constfactor,difvar];
];
v1=Sum[D[Coefficient[Expand[DiffInt],apearingintegrals[[i]]],difvar]apearingintegrals[[i]]+Coefficient[Expand[DiffInt],apearingintegrals[[i]]]*delHXB[difvar]*apearingintegrals[[i]] ,{i,1,Length[apearingintegrals]}];
v1+=constDiff;
Return[v1];
];


applyDifferentialOperator[diffop_,DiffInt_]:=Module[{},
	Return[diffop/.del[x_]:>applyDifferentialOperatorPart[DiffInt,x]];
];


(* ::Title:: *)
(*Plotting*)


plotDiagram[diagram_]:=Module[{diagramPLot,PropagatorsPlot},
	Get[FileNameJoin[{Directory[],"KinematicGraphs.m"}]];
	diagramPLot=diagram/.{hxb->List};
	diagramPLot=diagramPLot/.( n_Integer:>0/;n<0)/.( n_Integer:>1/;n>1);
	PropagatorsPlot={k1,k1+p1,k1+p1+p2,k2-k1,k2+p1+p2,k2+p1+p2+p3,k2+p1+p2+p3+p4,k2+p1+p2+p3+p4+p5,k2};
	PropagatorsPlot=PropagatorsPlot[[Position[diagramPLot,1][[All,1]]]];
	Return[buildKinematicGraph[PropagatorsPlot,{k1,k2},{p1,p2,p3,p4,p5}]];
];
