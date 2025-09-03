(* ::Package:: *)

p4cons={p[4]->-p[1]-p[2]-p[3]};
loopMomentumScalarProducts=Get[FileNameJoin[{Directory[],"files/internalRepls.m"}]]/.prop[n_Integer]:>PR[n];
mandelstamScalarProducts=Get[FileNameJoin[{Directory[],"files/mands.m"}]]
(*LaportaBasis=ReadList[FileNameJoin[{Directory[],"masters"}]];
LaportaBasis=Cases[LaportaBasis,_DB,Infinity];*)
invariants={d,mTsq,s12,s16,s345};



invariantConvChange={s23->s345,s45->s12,s15->s16};
sqrtG3=Sqrt[(-mTsq+s23-s45)^2-4 mTsq s45]/.invariantConvChange;




(* ::Title:: *)
(*Generate Random PhaseSpace Point*)


(*momenta={p[1],p[2],p[3],p[4],p[5]};
SixPointGram=Expand[Det[Table[momenta[[i]] momenta[[j]],{i,1,5},{j,1,5}]/.kinematics/.mandelstamScalarProducts/.loopMomentumScalarProducts]];*)
sqrtSet={sqrtG3}/.Sqrt[x_]:>x
GetRandomPT[NMin_,NMax_]:=Module[{tPoint,tPointReplacements,sqrtSetT,roots,NMAXIT,s16Sol},    
    NMAXIT=1000000;
    For[i = 0, i < NMAXIT, i++,
		tPoint=RandomInteger[{NMin,NMax},Length[invariants]];
		tPointReplacements=Thread[Rule[invariants,tPoint]];
		sqrtSetT = Expand[sqrtSet /. tPointReplacements, Modulus -> $P];
        roots = JacobiSymbol[#, $P] & /@ sqrtSetT;
        If[Total[roots] == Length[roots],
            Return[tPointReplacements];];
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
ReduListT=ReduList/.DB[n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_]:>{n1,n2,n3,n4,n5,n6,n7,n8,n9};
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
	WriteString[file,ToString[StringForm["      - {topologies: [DB], sectors: [``],r: ``,s: ``,d: ``}\n",sectorString,r,s,d]]];
	Close[file];
];
];

GenerateSectors[ReduList_]:=Module[{ReduListT,Sectors,SectorInts,r,s,d,sectorString,file,pos,sectorpath,directorypath},
ReduListT=ReduList/.DB[n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_]:>{n1,n2,n3,n4,n5,n6,n7,n8,n9};
Sectors=ReduListT/.( n_Integer:>0/;n<0)/.( n_Integer:>1/;n>1) //DeleteDuplicates;

For[pos=1,pos<=Length[Sectors],pos++,
Sectors[[pos]]//Echo;
SectorInts=ReduListT[[Sequence@@#]]&/@Position[ReduListT/.( n_Integer:>0/;n<0)/.( n_Integer:>1/;n>1) ,Sectors[[pos]]];
SectorInts//Echo;
r=Max[Table[Total[Select[SectorInts[[i]],Positive]],{i,1,Length[SectorInts]}]]//Echo;
s=Max[-Table[Total[Select[SectorInts[[i]],Negative]],{i,1,Length[SectorInts]}]]//Echo;
d=Max[Total[Thread[(({{0,2,1,0,0,0,1,2,0,0,0},{0,1,1,0,0,0,1,2,0,0,0}}-1)/.( n_Integer:>0/;n<0))]]]//Echo;
];
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
WriteJobFile[redulists_]:=Module[{filePath,directorypath,sectorpath,lists,redufilesectors,readline,i},
	filePath=FileNameJoin[{Directory[],"KIRA/jobs.yaml"}];
	directorypath=StringDrop[filePath,Last[Last[StringPosition[filePath,"/"]]];;];
	Quiet[DeleteFile[filePath]];
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
(*Propagators*)


Pr[1]=(k[1])^2;
Pr[2]=(k[1]-p[1]-p[2]-p[3])^2-mTsq;
Pr[3]=(k[1]-p[1]-p[2])^2;
Pr[4]=(k[1]+k[2])^2;
Pr[5]=(k[2])^2;
Pr[6]=(k[2]+p[1])^2/.p4cons;
Pr[7]=(k[2]+p[1]+p[2])^2/.p4cons;
Pr[8]=(k[1]+p[2])^2/.p4cons;
Pr[9]=(k[2]+p[1]+p[2]+p[3])^2;


InternalMometa={k[1],k[2]};
ExternalMometa={p[1],p[2],p[3]};


(* ::Title:: *)
(*HXB Definitions*)


Propdiff[n_,q_,integral_]:=Module[{newint},
	newint=(integral/.{DB->List});
	newint[[n]]-=q;
	Return[newint/.{List->DB}];
]
DB/:Power[PR[n_],q_]DB[n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_]:=Propdiff[n,q,DB[n1,n2,n3,n4,n5,n6,n7,n8,n9]];
DB/:PR[n_]*DB[n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_]:=Propdiff[n,1,DB[n1,n2,n3,n4,n5,n6,n7,n8,n9]];
DB/: delHXB[x_]*DB[n1_,n2_,n3_,n4_,n5_,n6_,n7_,n8_,n9_] := Sum[-{n1,n2,n3,n4,n5,n6,n7,n8,n9}[[i]]*PR[i]^-1 DB[n1,n2,n3,n4,n5,n6,n7,n8,n9]*D[Pr[i], x], {i, 1, 9}];


applyDifferentialOperatorPart[DiffInt_,difvar_]:=Module[{apearingintegrals,v1,constfactor,i,posconst,constDiff},
apearingintegrals=Cases[{DiffInt},_DB,Infinity]//DeleteDuplicates;
constfactor=CoefficientRules[DiffInt,Join[apearingintegrals,{DB[0,0,0,0,0,0,0,0,0]}]];
posconst=Position[constfactor,Table[0,{i,1,Length[apearingintegrals]+1}]];
constDiff=0;
If[Length[posconst]>0,
	constfactor=constfactor[[posconst[[1,1]],2]];
	constDiff=D[constfactor,difvar];
];
v1=Sum[((D[Coefficient[Expand[DiffInt],apearingintegrals[[i]]],difvar]apearingintegrals[[i]])+Coefficient[Expand[DiffInt],apearingintegrals[[i]]]*delHXB[difvar]*apearingintegrals[[i]]),{i,1,Length[apearingintegrals]}];
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
	diagramPLot=diagram/.{DB->List};
	diagramPLot=diagramPLot/.( n_Integer:>0/;n<0)/.( n_Integer:>1/;n>1);
	PropagatorsPlot={k1^2,+(k1+p1)^2,+(k1+p1+p2)^2,(k1+p1+p2+p3)^2,(k1+k2)^2,k2^2,(k2-p1-p2-p3-p4)^2,(k2-p1-p2-p3)^2,(k1+p1+p2+p3+p4)^2,+(k2-p1-p2)^2,+(k2-p1)^2}/.x_^2:>x;
	PropagatorsPlot=PropagatorsPlot[[Position[diagramPLot,1][[All,1]]]];
	Return[buildKinematicGraph[PropagatorsPlot,{k1,k2},{p1,p2,p3,p4}]];
];
