(* ::Package:: *)

(* ::Subsubsection::Closed:: *)
(*Graph makers*)


CreateRandomGraph[nNodes_,nEdges_]:=Module[{g,conn},conn=True;
While[conn,g=RandomGraph[{nNodes,nEdges},DirectedEdges->False];
conn=Length[ConnectedComponents[g]]!=1;];
g];

CreateRandomWSGraph[nNodes_,nEdges_,p_]:=Module[{g,conn},conn=True;
While[conn,
g=RandomGraph[WattsStrogatzGraphDistribution[nNodes,p,Floor[nEdges/nNodes]]];
conn=EdgeCount[g]!=nEdges];
g];

CreateFullGraph[nNodes_]:=Module[{g},
g = CompleteGraph[nNodes];
g];

CreateFullGraphBP[nNodes1_,nNodes2_]:=Module[{g},
g = CompleteGraph[{nNodes1,nNodes2}];
g];



(* ::Subsubsection::Closed:: *)
(*Learning functions *)


RandomInitialParameters[ERange_,BRange_,FRange_,nNodes_,nEdges_]:=Module[{EjList,BijList,FijList},

(*Initialize lists for parameters*)
EjList=RandomReal[{-ERange,ERange},nNodes];
BijList=RandomReal[{-BRange,BRange},nEdges];
FijList=RandomReal[{-FRange,FRange},nEdges];

{EjList, BijList, FijList}];

UpdateWeightMatrix[g_,edges_,nEdges_, nNodes_,adjMat_,EjList_,BijList_,FijList_]:=Module[{WijMat,n1,n2,Bij,Fij,Ei,Ej,Wij,Wji},

(*Initialize the weight matrix*)
WijMat=ConstantArray[0,{nNodes,nNodes}];

(*Populate the weight matrix using given formulas*)
Do[n1=edges[[e]][[1]];
n2=edges[[e]][[2]];
Bij=BijList[[e]];
Fij=FijList[[e]];
Ei=EjList[[n1]];
Ej=EjList[[n2]];
Wij=Exp[-Bij+Ej+Fij/2];
WijMat[[n1,n2]]=Wij;
Wji=Exp[-Bij+Ei-Fij/2];
WijMat[[n2,n1]]=Wji;,{e,1,nEdges}];

(*Adjust the diagonal elements of the weight matrix*)
Do[WijMat[[i,i]]=-Total[WijMat[[;;,i]]];,{i,1,nNodes}];

(*Return the resulting weight matrix*)
WijMat];

GetEdgeFluxes[edges_,nEdges_,piVec_,WijMat_]:=Module[{fluxes,in,jn,i,j,Wij,Wji},

(*Initialize the weight matrix*)
fluxes = {};

(*Populate the weight matrix using given formulas*)
Do[
i=edges[[e]][[1]];
j=edges[[e]][[2]];
Wij=WijMat[[i,j]];
Wji=WijMat[[j,i]];
AppendTo[fluxes, piVec[[j]]*Wij-piVec[[i]]*Wji ]; (* flux from j to i *)

,
{e,1,nEdges}];

(*Return the resulting weight matrix*)
fluxes
];

GetEdgeFrenesies[edges_,nEdges_,piVec_,WijMat_]:=Module[{frenesies,in,jn,i,j,Wij,Wji},

(*Initialize the weight matrix*)
frenesies = {};

(*Populate the weight matrix using given formulas*)
Do[
i=edges[[e]][[1]];
j=edges[[e]][[2]];
Wij=WijMat[[i,j]];
Wji=WijMat[[j,i]];
AppendTo[frenesies, piVec[[j]]*Wij+piVec[[i]]*Wji ]; (* flux from j to i *)

,
{e,1,nEdges}];

(*Return the resulting weight matrix*)
frenesies
];

GetEP[edges_,nEdges_,piVec_,WijMat_]:=Module[{ep,in,jn,i,j,Wij,Wji},

(*Initialize the weight matrix*)
ep = 0;

(*Populate the weight matrix using given formulas*)
Do[
i=edges[[e]][[1]];
j=edges[[e]][[2]];
Wij=WijMat[[i,j]];
Wji=WijMat[[j,i]];
ep+=1/2 ( piVec[[j]]*Wij-piVec[[i]]*Wji )*Log[(Wij*piVec[[j]])/(Wji*piVec[[i]])];
,
{e,1,nEdges}];

(*Return the resulting weight matrix*)
ep
];


GetStationaryVector[WijMat_]:=Module[{vStat},
(*vStat=Eigenvectors[WijMat][[-1]];*)
vStat=Eigenvectors[WijMat,-1][[1]];
vStat=Re[vStat/Total[vStat]];
(*If[Max[Abs[WijMat.vStat//Chop]]!=0,Print["Bad"];];*)
vStat];

GetOutput[WijMat_,numOuts_]:=Module[{ret,vStat},
vStat=GetStationaryVector[WijMat];
ret = {};
Do[
AppendTo[ret,vStat[[numOuts[[i]]]]];
,{i,Length[numOuts]}];
ret
];

GetOutsLabels[nNodes_,numOuts_]:=Module[{outsLabels,outs},
outsLabels = {};
Do[
outs = ConstantArray[0,nNodes];
outs[[Flatten[numOuts]]]=1;
outs[[numOuts[[i]]]]=-1;
AppendTo[outsLabels,outs];
,{i,1,Length[numOuts]}
];
outsLabels
]

MapInputToWijMat[inputs_,inputInds_,signs_,g_,edges_,nEdges_,nNodes_,adjMat_,EjList_,BijList_,FijList_,BijBool_,repBool_:False]:=Module[
{tempFijList,tempBijList,tempWijMat},

tempBijList=BijList;
tempFijList=FijList;

Do[
Do[
If[BijBool,
If[repBool,
tempBijList[[inputInds[[e]][[m]]]]=signs[[m]]*inputs[[e]];,
tempBijList[[inputInds[[e]][[m]]]]+=signs[[m]]*inputs[[e]];
];
,
If[repBool,
tempFijList[[inputInds[[e]][[m]]]]=signs[[m]]*inputs[[e]];,
tempFijList[[inputInds[[e]][[m]]]]+=signs[[m]]*inputs[[e]];
];
];
,{m,1,Length[inputInds[[e]]]}];
,{e,1,Length[inputInds]}];
UpdateWeightMatrix[g,edges,nEdges, nNodes,adjMat, EjList, tempBijList,tempFijList]

(*tempBijList=BijList;
Do[
Do[
tempBijList[[inputInds[[e]][[m]]]]=signs[[m]]*inputs[[e]];
(*tempFijList[[inputInds[[e]][[m]]]]=signs[[m]]*inputs[[e]];*)
,{m,1,Length[inputInds[[e]]]}];
,{e,1,Length[inputInds]}];
UpdateWeightMatrix[g,edges,nEdges, nNodes,adjMat, EjList, tempBijList,FijList]*)
];

MapInputOutput[inputs_,inputInds_,signs_,numOuts_,g_,edges_,nEdges_,nNodes_,adjMat_,EjList_,BijList_,FijList_,BijBool_,repBool_:False]:=Module[{},
GetOutput[MapInputToWijMat[inputs,inputInds,signs,g,edges,nEdges,nNodes,adjMat,EjList,BijList,FijList,BijBool,repBool],numOuts]
];

nudgedStationaryVector[inputs_, inputInds_,signs_,numOuts_,nudgeDeltas_,g_,edges_,nEdges_,nNodes_,adjMat_,EjList_,BijList_,FijList_,BijBool_,repBool_:False]:=Module[{tempEjList,tempWijMat,nudgedpiVec},
(*Do[
tempEjList[[i]]+=nudgeDeltas[[i]];
,{i,1,Length[numOuts]}];*)

tempEjList=EjList;
tempEjList+=nudgeDeltas;

tempWijMat = MapInputToWijMat[inputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, tempEjList, BijList,FijList,BijBool,repBool];
nudgedpiVec=GetStationaryVector[tempWijMat];
{nudgedpiVec, GetEdgeFluxes[edges,nEdges,nudgedpiVec,tempWijMat],GetEdgeFrenesies[edges,nEdges,nudgedpiVec,tempWijMat]}
];

GetSigns[inputs_,inputInds_,inputInd_,signs_,g_,edges_,nEdges_,nNodes_,adjMat_,EjList_,BijList_,FijList_,d\[Alpha]_,BijBool_,repBool_:False]:=Module[
{WijMatP,WijMatM,vStatP,vStatM,tempInputs},
tempInputs=inputs;
WijMatM=MapInputToWijMat[tempInputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, EjList, BijList,FijList,BijBool,repBool];
vStatM=GetStationaryVector[WijMatM];
tempInputs[[inputInd]]+=d\[Alpha];
WijMatP=MapInputToWijMat[tempInputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, EjList, BijList,FijList,BijBool,repBool];
vStatP=GetStationaryVector[WijMatP];
Sign[vStatP-vStatM]
];


ComputepiAndPiprime[inputs_, inputInds_,signs_,g_,edges_,nEdges_,nNodes_,BBool_,EjList_,BijList_,FijList_,adjMat_,d\[Alpha]_,BijBool_,repBool_:False]:=Module[
{WijMatP,WijMatM,vStatP,vStatM,tempFijList,tempBijList,dPidFij},
dPidFij=ConstantArray[0,{nNodes,nEdges}];

tempFijList=FijList;
tempBijList=BijList;

Do[
If[BBool,
tempBijList[[e]]+=d\[Alpha];,
tempFijList[[e]]+=d\[Alpha];
];
WijMatP=MapInputToWijMat[inputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, EjList, tempBijList,tempFijList,BijBool,repBool];
If[BBool,
tempBijList[[e]]-=2*d\[Alpha];,
tempFijList[[e]]-=2*d\[Alpha];
];
WijMatM =MapInputToWijMat[inputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, EjList, tempBijList,tempFijList,BijBool,repBool];
vStatP=GetStationaryVector[WijMatP];
vStatM=GetStationaryVector[WijMatM];
dPidFij[[;;,e]]=(vStatP-vStatM)/(2 d\[Alpha]);
If[BBool,
tempBijList[[e]]+=d\[Alpha];,
tempFijList[[e]]+=d\[Alpha];
];
,{e,1,nEdges}];

Return[dPidFij];
];


ComputepiAndPiprimeE[inputs_, inputInds_,signs_,g_,edges_,nEdges_,nNodes_,EjList_,BijList_,FijList_,adjMat_,BijBool_,repBool_:False]:=Module[
{WijMat,vStat,dPidEj,dd},
dPidEj=ConstantArray[0,{nNodes,nNodes}];(* di /dj *)

WijMat =MapInputToWijMat[inputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, EjList, BijList,FijList,BijBool,repBool];
vStat=GetStationaryVector[WijMat];
Do[
Do[
If[i==k,
dd = -vStat[[i]]*(1-vStat[[i]]),
dd = vStat[[i]]*vStat[[k]]];
dPidEj[[i,k]]=dd;
,{k,1,nNodes}]
,{i,1,nNodes}];

Return[dPidEj];
];

ComputeInputDerivs[inputs_, inputInds_,signs_,g_,edges_,nEdges_,nNodes_,EjList_,BijList_,FijList_,adjMat_,d\[Alpha]_,BijBool_,repBool_]:=Module[
{dPidInputs,WijMatP,WijMatM,vStatP,vStatM,tempInputs},
dPidInputs=ConstantArray[0,{nNodes,Length[inputs]}];
tempInputs=inputs;
Do[
tempInputs[[e]]+=d\[Alpha];
WijMatP=MapInputToWijMat[tempInputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, EjList, BijList,FijList,BijBool,repBool];
tempInputs[[e]]-=2*d\[Alpha];
WijMatM =MapInputToWijMat[tempInputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, EjList, BijList,FijList,BijBool,repBool];
vStatP=GetStationaryVector[WijMatP];
vStatM=GetStationaryVector[WijMatM];

dPidInputs[[;;,e]]=(vStatP-vStatM)/(2 d\[Alpha]);
tempInputs[[e]]+=d\[Alpha];
,{e,1,Length[inputs]}];

Return[dPidInputs];
];

TestPredictions[meanLists_,stdLists_,nTest_,inputList_,inputInds_,signs_,numOuts_,g_,edges_,nEdges_,nNodes_,adjMat_,EjList_, BijList_, FijList_,BijBool_,repBool_:False]:=Module[{output, outputs, iter,newMeans, newStds,iRange},
newMeans = {};
newStds = {};

Do[
outputs ={};
Do[
iter=RandomInteger[Length[inputList[[i]]]-1]+1;
output = Mean[MapInputOutput[inputList[[i]][[iter]],inputInds,signs,numOuts,g,edges,nEdges,nNodes,adjMat,EjList, BijList, FijList,BijBool,repBool][[i]]];
AppendTo[outputs,output];
,{n,1,nTest}];

AppendTo[newMeans,Mean[outputs]];
AppendTo[newStds,StandardDeviation[outputs]];
,{i,Range[1,Length[numOuts]]}];

{newMeans, newStds}
];

GetAccuracy[nTest_,inputList_,inputInds_,signs_,numOuts_,g_,edges_,nEdges_,nNodes_,adjMat_,EjList_, BijList_, FijList_,BijBool_,repBool_:False]:=Module[{output, iter,i,prediction,acc},

acc={};
Do[
i = RandomInteger[1]+1;
iter=RandomInteger[Length[inputList[[i]]]-1]+1;
output = MapInputOutput[inputList[[i]][[iter]],inputInds,signs,numOuts,g,edges,nEdges,nNodes,adjMat,EjList, BijList, FijList,BijBool,repBool][[;;,1]];
(*prediction=Position[output[[1;;2]],Max[output[[1;;2]]]][[1,1]];
If[prediction==i,acc+=1];*)
AppendTo[acc,output[[i]]];
,{n,1,nTest}];

{Mean[acc],StandardDeviation[acc]}
];



(* ::Subsubsection::Closed:: *)
(*Graph drawing*)


DirectedWeightedGraph[edges_,nEdges_,fluxes_]:=Module[{directedEdges,edgeWeights},
directedEdges={};
edgeWeights = {};
Do[
If[fluxes[[e]]>0,
AppendTo[directedEdges, edges[[e]][[2]]\[DirectedEdge]edges[[e]][[1]]],
AppendTo[directedEdges, edges[[e]][[1]]\[DirectedEdge]edges[[e]][[2]]]
];
AppendTo[edgeWeights,Abs[fluxes[[e]]]]
,{e,1,nEdges}
];
{Graph[directedEdges,EdgeWeight->edgeWeights],directedEdges,edgeWeights}
];

DrawInputOutputGraph[inputs_,inputInds_,signs_,paramBool_,numOuts_,g_,edges_,nEdges_,nNodes_,adjMat_,EjList_,BijList_,FijList_,scFac_,arFac_,arMin_,edgeMin_,pMin_,pFac_,nodeCol_,edgeCol_,vCoords_,BijBool_,repBool_:False]:=Module[{WijMat,piVec,fluxes,dirG,directedEdges,edgeWeights,eColors,vColors,eStyles,vStyles,vSizes,ogCoords,coords,maxEdgeWeight},

If[paramBool,
WijMat=UpdateWeightMatrix[g,edges,nEdges,nNodes,adjMat,EjList, BijList, FijList];
piVec=Exp[-EjList]/Total[Exp[-EjList]];
fluxes= GetEdgeFluxes[edges,nEdges,ConstantArray[1,nNodes],WijMat];
Do[
Do[
fluxes[[inputInds[[e]][[m]]]]=signs[[m]]*inputs[[e]];
,{m,1,Length[inputInds[[e]]]}];
,{e,1,Length[inputInds]}];
, (* not paramBool *)
WijMat=MapInputToWijMat[inputs,inputInds,signs,g,edges,nEdges,nNodes,adjMat,EjList, BijList, FijList,BijBool,repBool];
piVec=GetStationaryVector[WijMat];
fluxes= GetEdgeFluxes[edges,nEdges,piVec,WijMat];
];

{dirG, directedEdges,edgeWeights}= DirectedWeightedGraph[edges,nEdges,fluxes];

eColors = Array[Black&,nEdges];
Do[
Do[
eColors[[inputInds[[e]]]]=edgeCol
,{m,1,Length[inputInds[[e]]]}];
,{e,1,Length[inputInds]}];

vColors =  Array[Black&,nNodes];
Do[
vColors[[numOuts[[n]]]]=nodeCol[[n]];
,{n,1,Length[nodeCol]}];


maxEdgeWeight=Max[edgeWeights];
eStyles =Table[directedEdges[[e]]->Directive[Arrowheads[arFac*edgeWeights[[e]]/maxEdgeWeight+arMin],Thickness[scFac*edgeWeights[[e]]/maxEdgeWeight+edgeMin],eColors[[e]],Opacity[1]],{e,1,nEdges}];
vStyles=Table[i->Directive[vColors[[i]],Opacity[1]],{i,1,nNodes}];
vSizes=Table[i->(pFac*piVec[[i]]+pMin),{i,1,nNodes}];

If[Length[vCoords]==0,
ogCoords=GraphEmbedding[g];
coords = Table[i->ogCoords[[i]],{i,1,nNodes}];
,
coords = vCoords;
];

DirectedGraph[dirG,
EdgeStyle->eStyles,
ImageSize->Large,
VertexStyle->vStyles,
VertexSize->vSizes,
VertexCoordinates->coords,
(*VertexLabels->{"Name"},*)
VertexLabelStyle->Directive[FontSize->16,FontFamily->"Arial"]
]
]

DrawParamGraph[inputs_,inputInds_,signs_,paramBool_,numOuts_,g_,edges_,nEdges_,nNodes_,adjMat_,EjList_,BijList_,FijList_,scFac_,arFac_,arMin_,edgeMin_,pMin_,pFac_,nodeCol_,edgeCol_,vCoords_,BijBool_,repBool_:False,imSize_:400]:=Module[{WijMat,piVec,fluxes,dirG,directedEdges,edgeWeights,eColors,vColors,eStyles,vStyles,vSizes,ogCoords,coords,maxFij,maxBij,minBij,maxVertexSize},

{dirG, directedEdges,edgeWeights}= DirectedWeightedGraph[edges,nEdges,FijList];

eColors = Array[Black&,nEdges];
vColors =  Array[Black&,nNodes];

Do[
vColors[[numOuts[[n]]]]=nodeCol[[n]];
,{n,1,Length[nodeCol]}];


maxFij=Max[Abs[FijList]]+10^-6;
maxBij=Max[BijList]+0;
minBij=Min[BijList]+0;
Print[minBij];
eStyles =Table[directedEdges[[e]]->Directive[
Arrowheads[arFac*Abs[FijList[[e]]]/maxFij+arMin],
(*Thickness[scFac*BijList[[e]]/maxBij+edgeMin],Black,Opacity[1]],{e,1,nEdges}];*)
(*Thickness[scFac*Exp[BijList[[e]]]+edgeMin],Black,Opacity[1]],{e,1,nEdges}];*)
Thickness[-scFac*(BijList[[e]]-maxBij)+edgeMin],Black,Opacity[1]],{e,1,nEdges}];

vStyles=Table[i->Directive[vColors[[i]],Opacity[1]],{i,1,nNodes}];
maxVertexSize = Max[Exp[-EjList]];
vSizes=Table[i->(pFac*Exp[-EjList[[i]]]/maxVertexSize+pMin),{i,1,nNodes}];


If[Length[vCoords]==0,
ogCoords=GraphEmbedding[g];
coords = Table[i->ogCoords[[i]],{i,1,nNodes}];
,
coords = vCoords;
];

DirectedGraph[dirG,
EdgeStyle->eStyles,
ImageSize->imSize,
VertexStyle->vStyles,
VertexSize->vSizes,
VertexCoordinates->coords,
(*VertexLabels->{"Name"},*)
VertexLabelStyle->Directive[FontSize->16,FontFamily->"Arial"]
]
]


DrawFluxGraph[inputs_,inputInds_,signs_,paramBool_,numOuts_,g_,edges_,nEdges_,nNodes_,adjMat_,EjList_,BijList_,FijList_,scFac_,arFac_,arMin_,edgeMin_,pMin_,pFac_,nodeCol_,edgeCol_,vCoords_,BijBool_,repBool_:False,imSize_:400]:=Module[{WijMat,piVec,fluxes,frenesies,dirG,directedEdges,edgeWeights,eColors,vColors,eStyles,vStyles,vSizes,ogCoords,coords,maxFij,maxBij,maxVertexSize},

WijMat=MapInputToWijMat[inputs,inputInds,signs,g,edges,nEdges,nNodes,adjMat,EjList, BijList, FijList,BijBool,repBool];
piVec=GetStationaryVector[WijMat];
fluxes= GetEdgeFluxes[edges,nEdges,piVec,WijMat];
frenesies= GetEdgeFrenesies[edges,nEdges,piVec,WijMat];

{dirG, directedEdges,edgeWeights}= DirectedWeightedGraph[edges,nEdges,fluxes];

eColors = Array[Gray&,nEdges];
vColors =  Array[Gray&,nNodes];

Do[
vColors[[numOuts[[n]]]]=nodeCol[[n]];
,{n,1,Length[nodeCol]}];


maxFij=Max[Abs[fluxes]];
maxBij=Max[Abs[frenesies]];
eStyles =Table[directedEdges[[e]]->Directive[
Arrowheads[arFac*Abs[fluxes[[e]]]/maxFij+arMin],
Thickness[scFac*frenesies[[e]]/maxBij+edgeMin],Gray,Opacity[1]],{e,1,nEdges}];

vStyles=Table[i->Directive[vColors[[i]],Opacity[1]],{i,1,nNodes}];
maxVertexSize = Max[piVec];
vSizes=Table[i->(pFac*piVec[[i]]/maxVertexSize+pMin),{i,1,nNodes}];

If[Length[vCoords]==0,
ogCoords=GraphEmbedding[g];
coords = Table[i->ogCoords[[i]],{i,1,nNodes}];
,
coords = vCoords;
];

DirectedGraph[dirG,
EdgeStyle->eStyles,
ImageSize->imSize,
VertexStyle->vStyles,
VertexSize->vSizes,
VertexCoordinates->coords,
(*VertexLabels->{"Name"},*)
VertexLabelStyle->Directive[FontSize->16,FontFamily->"Arial"]
]
]



(* ::Subsubsection::Closed:: *)
(*Hessian*)


ComputeHessianVec[f_,varVec_,da_:0.01]:=Module[{n,hessian,f0,df,df2,i,j,g,varVecP,varVecM,varVecPP,varVecPM,varVecMP,varVecMM},n=Length[varVec];
f0=f[varVec];
hessian=ConstantArray[0,{Length[f0],n,n}];
varVecP=varVec;
varVecM=varVec;
For[i=1,i<=n,i++,

varVecP[[i]]+=da;
varVecM[[i]]-=da;

varVecPP=varVecP;
varVecPM=varVecP;
varVecMP=varVecM;
varVecMM=varVecM;
For[j=i,j<=n,j++,

varVecPP[[j]]+=da;
varVecMP[[j]]+=da;
varVecPM[[j]]-=da;
varVecMM[[j]]-=da;

g = (f[varVecMM]+f[varVecPP]-f[varVecMP]-f[varVecPM])/(4*da^2);
hessian[[;;,i,j]]=g;
hessian[[;;,j,i]]=g;

varVecPP[[j]]-=da;
varVecMP[[j]]-=da;
varVecPM[[j]]+=da;
varVecMM[[j]]+=da;
];

varVecP[[i]]-=da;
varVecM[[i]]+=da;
];
hessian]

lnPiFuncVec[thetaVec_,edges_,nEdges_,nNodes_,adjMat_,inputs_,inputInds_,signs_]:=Module[
{WijMat},
WijMat =
WijMat[inputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, thetaVec[[1;;nNodes]], thetaVec[[nNodes+1;;nNodes+nEdges]],thetaVec[[nNodes+nEdges+1;;-1]]];
Log[GetStationaryVector[WijMat]]
];

ComputeWeightedHessianVec[inputs_, inputInds_,signs_,g_,edges_,nEdges_,nNodes_,EjList_,BijList_,FijList_,adjMat_,d\[Alpha]_,BijBool_,repBool_:False]:=Module[
{WijMatP,WijMatM,vStatP,vStatM,tempFijList,tempBijList,weightedHessian,nElements,WijMat,pik,thetaVec,hessians},

nElements = nNodes + 2*nEdges;
weightedHessian=ConstantArray[0,{nElements,nElements}];

WijMat =MapInputToWijMat[inputs,inputInds,signs,g,edges,nEdges, nNodes,adjMat, EjList, BijList,FijList,BijBool,repBool];
pik=GetStationaryVector[WijMat];

thetaVec=Flatten[{EjList,BijList,FijList}];

hessians = ComputeHessianVec[Function[varVec,lnPiFuncVec[varVec,edges,nEdges,nNodes,adjMat,inputs,inputInds,signs]],thetaVec,d\[Alpha]];

-pik . hessians

];


(* ::Subsubsection::Closed:: *)
(*Tree enumeration*)


(*Get["https://raw.githubusercontent.com/szhorvat/IGraphM/master/IGInstaller.m"]*)
<<"IGraphM`";

CreateSymblolicWeightMatrix[g_]:=Module[{nNodes,nEdges,adjMat,edges,n1,n2,WijMat,WijSyms},

(*Extract information from the input graph*)nNodes=VertexCount[g];
nEdges=EdgeCount[g];
adjMat=AdjacencyMatrix[g];
edges=EdgeList[g];

(*Initialize the weight matrix*)
WijMat=ConstantArray[0,{nNodes,nNodes}];
WijSyms={};

(*Populate the weight matrix using given formulas*)
Do[n1=edges[[e]][[1]];
n2=edges[[e]][[2]];
WijMat[[n1,n2]]=Symbol["W"<>ToString[n1]<>ToString[n2]];
WijMat[[n2,n1]]=Symbol["W"<>ToString[n2]<>ToString[n1]];
AppendTo[WijSyms,WijMat[[n1,n2]]];
AppendTo[WijSyms,WijMat[[n2,n1]]];
,{e,1,nEdges}];

(*Adjust the diagonal elements of the weight matrix*)
Do[WijMat[[i,i]]=-Total[WijMat[[;;,i]]];,{i,1,nNodes}];

(*Return the resulting weight matrix*)
{WijMat, edges, adjMat,WijSyms}];

CheckFrustration[inequalities_]:=Module[
{frustrated,global},
frustrated=False;
global = False;
If[MemberQ[inequalities[[;;,1]],0],
frustrated=True,
If[Simplify[Total[inequalities[[;;,1]]]-Total[inequalities[[;;,2]]]]==0,
frustrated=True; global=True;]
];
{frustrated,global}
]

CreateSymblolicLists[nNodes_,nEdges_,edges_]:=Module[
{EjListSym,pkListSym,BijListSym,FijListSym,i,j},

EjListSym={};
pkListSym={};
BijListSym={};
FijListSym={};

Do[
AppendTo[EjListSym,Symbol["E"<>ToString[k]]];
AppendTo[pkListSym,Symbol["p"<>ToString[k]]];
,{k,1,nNodes}];


Do[
i=edges[[e]][[1]];
j=edges[[e]][[2]];
AppendTo[BijListSym,Symbol["B"<>ToString[i]<>ToString[j]]];
AppendTo[FijListSym,Symbol["F"<>ToString[i]<>ToString[j]]];

,{e,1,nEdges}];

{EjListSym,pkListSym,BijListSym,FijListSym}
];

CreateSymblolicListsWij[nNodes_,nEdges_,edges_]:=Module[
{WijListSym,WjiListSym,i,j},

WijListSym={};
WjiListSym={};


Do[
i=edges[[e]][[1]];
j=edges[[e]][[2]];
AppendTo[WijListSym,Symbol["W"<>ToString[i]<>ToString[j]]];
AppendTo[WjiListSym,Symbol["W"<>ToString[j]<>ToString[i]]];

,{e,1,nEdges}];

{WijListSym,WjiListSym}
];

GetSpanningTrees[g_, nNodes_]:=Module[
{trees},
trees=Select[TreeGraphQ[Graph@#]&]@Select[VertexCount@#==nNodes&]@Subsets[EdgeList[g],{nNodes-1}];
If[Length[trees]!=IGSpanningTreeCount[g], Print["Bad trees"]];
trees]

OrientTree[tree_,k_]:=EdgeList[IGOrientTree[Graph[tree],k]]

TreeWeight[oTree_,WijMat_]:=Module[
{weight, edge},
weight = 1;
Do[
edge = oTree[[i]];
weight = weight*WijMat[[edge[[1]],edge[[2]]]]
,{i,1,Length[oTree]}];
weight
]

ComputePhik[g_,trees_,WijMat_,k_]:=Module[
{wTot,oTree},
wTot=0;
Do[
oTree = OrientTree[trees[[n]],k];
wTot = wTot +TreeWeight[oTree,WijMat];
,{n,1,Length[trees]}];
Log[wTot]
]

GetPhikList[g_,nNodes_,WijMat_]:=Module[
{trees,PhikList},
trees = GetSpanningTrees[g,nNodes];
PhikList = {};
Do[
AppendTo[PhikList, ComputePhik[g,trees,WijMat,k]]
,{k,1,nNodes}];
PhikList 
]

GetStationaryDistributionTrees[g_,nNodes_,WijMat_]:=Exp[GetPhikList[g,nNodes,WijMat]] /Total[Exp[GetPhikList[g,nNodes,WijMat]]];


AugmentWeightMatrix[WijMat_,edges_,eNums_,vars_,sign_]:=Module[
{WijMatAug, edge, n1, n2, nNodes,eNum},

WijMatAug=WijMat;
nNodes = Length[WijMat[[;;,1]]];

Do[
Do[
eNum=eNums[[s]][[t]];
edge=edges[[eNum]];
n1=edge[[1]];
n2=edge[[2]];


WijMatAug[[n1,n2]]=WijMatAug[[n1,n2]] Exp[sign*vars[[s]]/2];
WijMatAug[[n2,n1]]=WijMatAug[[n2,n1]] Exp[-sign*vars[[s]]/2];
,{t,1,Length[eNums[[s]]]}]
,{s,1,Length[eNums]}
];

Do[
WijMatAug[[i,i]]=0;
WijMatAug[[i,i]]=-Total[WijMatAug[[;;,i]]],
{i,1,nNodes}];

WijMatAug
]

MapParamsToWijs[edges_,nEdges_,EjList_,BijList_,FijList_]:=Module[{evalList,i,j,Ei,Ej,Bij,Fij,WijS,Wij,WjiS,Wji},
evalList = {};
Do[i=edges[[e]][[1]];
j=edges[[e]][[2]];
Ei = EjList[[i]];
Ej=EjList[[j]];
Bij=BijList[[e]];
Fij=FijList[[e]];
WijS=Symbol["W"<>ToString[i]<>ToString[j]];
Wij=Exp[-Bij+Ej+Fij/2];
WjiS=Symbol["W"<>ToString[j]<>ToString[i]];
Wji=Exp[-Bij+Ei-Fij/2];
AppendTo[evalList,WijS->Wij];
AppendTo[evalList,WjiS->Wji];
,{e,1,nEdges}];
evalList
];

DPhikDWijMatrix[g_,nNodes_,nEdges_]:=Module[{mat,PhikList,WijMatSym,WijMatSymbols},
WijMatSym=CreateSymblolicWeightMatrix[g][[1]];
WijMatSymbols=CreateSymblolicWeightMatrix[g][[4]];
mat = ConstantArray[0,{nNodes,2*nEdges}];
PhikList= GetPhikList[g,nNodes,WijMatSym];
Do[
mat[[k,e]]=Simplify[D[PhikList[[k]],WijMatSymbols[[e]]]]
,{k,1,nNodes},{e,1,2*nEdges}];
{mat,WijMatSymbols}
];

GetdPhidFijList[inputs_, inputInds_,edges_,nEdges_,pVec_,dPhidWij_,WijMatSymbols_,EjList_,BijList_,FijList_]:=Module[{evals,Wijs,dPhidWijEval,dPhidFijList,dPhikVec, tempFijList},
tempFijList=FijList;
Do[
tempFijList[[inputInds[[e]]]]+=inputs[[e]];
,{e,1,Length[inputInds]}];

evals=MapParamsToWijs[edges,nEdges,EjList,BijList,tempFijList];
Wijs=Evaluate[WijMatSymbols/.evals];
dPhidWijEval = Evaluate[dPhidWij/.evals];
dPhidFijList = {};

Do[
dPhikVec = 0.5(dPhidWijEval[[;;,2*(e-1)+1]]*Wijs[[2*(e-1)+1]]-dPhidWijEval[[;;,2*(e-1)+2]]*Wijs[[2*(e-1)+2]]);
AppendTo[dPhidFijList , pVec . dPhikVec]
,{e,1,Length[FijList]}];

dPhidFijList
]


Getui\[Alpha][ind_,\[Alpha]_,trees_,edges_,nEdges_,nNodes_]:=Module[
{oTree,ri\[Alpha],si\[Alpha],ti\[Alpha],s,t,it,jt},

oTree = OrientTree[trees[[\[Alpha]]],ind];

ri\[Alpha]=ConstantArray[1,nNodes];
ri\[Alpha][[ind]]=0;

si\[Alpha]=ConstantArray[0,nEdges];
ti\[Alpha]=ConstantArray[0,nEdges];
Do[
it=edges[[e]][[1]];
jt=edges[[e]][[2]];

If[MemberQ[oTree,it\[DirectedEdge]jt],s=-1;t = 1/2;,
If[MemberQ[oTree,jt\[DirectedEdge]it],s=-1;t=-1/2;,
s=0;t=0;]];
si\[Alpha][[e]]=s;
ti\[Alpha][[e]]=t;
,{e,1,nEdges}];

{ri\[Alpha],si\[Alpha],ti\[Alpha]}
]

Getvi\[Alpha][ind_,\[Alpha]_,trees_,edges_,inputInds_, signs_,nEdges_,nNodes_,BijBool_:False]:=Module[
{oTree,vi\[Alpha],v,sign,edge},

oTree = OrientTree[trees[[\[Alpha]]],ind];
vi\[Alpha]=ConstantArray[0,Length[inputInds]];

Do[
v=0;
Do[
edge=edges[[inputInds[[e]][[m]]]];
sign = signs[[m]];

it=edge[[1]];
jt=edge[[2]];
If[BijBool,
If[MemberQ[oTree,it\[DirectedEdge]jt],v-=sign*1;,
If[MemberQ[oTree,jt\[DirectedEdge]it],v-=sign*1;]
];,

If[MemberQ[oTree,it\[DirectedEdge]jt],v+=sign*1/2;,
If[MemberQ[oTree,jt\[DirectedEdge]it],v+=-sign*1/2;]];
];

,{m,1,Length[inputInds[[e]]]}];
vi\[Alpha][[e]]=v;
,{e,1,Length[inputInds]}];

vi\[Alpha]
]

Getui\[Alpha]Array[trees_,edges_,nEdges_,nNodes_]:=Module[
{ui\[Alpha]Array},
ui\[Alpha]Array=ConstantArray[0,{nNodes,Length[trees]}];
Do[
Do[
ui\[Alpha]Array[[k,n]]=Getui\[Alpha][k,n,trees,edges,nEdges,nNodes];
,{n,1,Length[trees]}]
,{k,1,nNodes}];

ui\[Alpha]Array
];

Getvi\[Alpha]Array[trees_,edges_,inputInds_, signs_,nEdges_,nNodes_,BijBool_:False]:=Module[
{vi\[Alpha]Array},
vi\[Alpha]Array=ConstantArray[0,{nNodes,Length[trees]}];
Do[
Do[
vi\[Alpha]Array[[k,n]]=Getvi\[Alpha][k,n,trees,edges,inputInds, signs,nEdges,nNodes,BijBool];
,{n,1,Length[trees]}]
,{k,1,nNodes}];

vi\[Alpha]Array
];


GetPsiVec[ind_,trees_,EjList_,BijList_,FijList_,ui\[Alpha]Array_]:=Module[
{PsiVec,Psi,ri\[Alpha],si\[Alpha],ti\[Alpha]},
PsiVec=ConstantArray[0,Length[trees]];
Do[
{ri\[Alpha],si\[Alpha],ti\[Alpha]}=ui\[Alpha]Array[[ind,n]];
Psi=Exp[ri\[Alpha] . EjList + si\[Alpha] . BijList+ti\[Alpha] . FijList];
PsiVec[[n]]=Psi;
,{n,1,Length[trees]}];

PsiVec
]

GetChiVec[ind_,trees_,inputs_,vi\[Alpha]Array_]:=Module[
{ChiVec,Chi,vi\[Alpha]},
ChiVec=ConstantArray[0,Length[trees]];
Do[
vi\[Alpha]=vi\[Alpha]Array[[ind,n]];
Chi=Exp[vi\[Alpha] . inputs];
ChiVec[[n]]=Chi;
,{n,1,Length[trees]}];
ChiVec
]

GetpiVecTrees[nNodes_,trees_,EjList_,BijList_,FijList_,inputs_,ui\[Alpha]Array_,vi\[Alpha]Array_]:=Module[
{piVec,piUnNormVec,tot},
piVec = ConstantArray[0,nNodes];
piUnNormVec=ConstantArray[0,nNodes];
Do[
piUnNormVec[[k]]=GetPsiVec[k,trees,EjList,BijList,FijList,ui\[Alpha]Array] . GetChiVec[k,trees,inputs,vi\[Alpha]Array];
,{k,1,nNodes}];
tot = Total[piUnNormVec];
Do[
piVec[[k]]=piUnNormVec[[k]]/tot;
,{k,1,nNodes}];
piVec
];

GetLNumk[nNodes_,trees_,EjList_,BijList_,FijList_,inputs_,ui\[Alpha]Array_,vi\[Alpha]Array_,l_]:=Module[
{piVec,piUnNormVec,tot},
piUnNormVec=ConstantArray[0,nNodes];
Do[
piUnNormVec[[k]]=GetPsiVec[k,trees,EjList,BijList,FijList,ui\[Alpha]Array] . GetChiVec[k,trees,l*inputs,vi\[Alpha]Array];
,{k,1,nNodes}];
-1/l Log[piUnNormVec]
];

GetLSE[nNodes_,trees_,EjList_,BijList_,FijList_,inputs_,ui\[Alpha]Array_,vi\[Alpha]Array_,l_]:=Module[
{piVec,piUnNormVec,tot},
piVec = ConstantArray[0,nNodes];
piUnNormVec=ConstantArray[0,nNodes];
Do[
piUnNormVec[[k]]=GetPsiVec[k,trees,EjList,BijList,FijList,ui\[Alpha]Array] . GetChiVec[k,trees,l*inputs,vi\[Alpha]Array];
,{k,1,nNodes}];
tot = Total[piUnNormVec];
-1/l Log[tot]
];



(* ::Subsubsection::Closed:: *)
(*Wij variants*)


UpdateWeightMatrixWij[g_,edges_,nEdges_, nNodes_,adjMat_,WijList_,WjiList_]:=Module[{WijMat,i,j,Wij,Wji},

(*Initialize the weight matrix*)
WijMat=ConstantArray[0,{nNodes,nNodes}];

Do[i=edges[[e]][[1]];
j=edges[[e]][[2]];
Wij=WijList[[e]];
WijMat[[i,j]]=Wij;
Wji=WjiList[[e]];
WijMat[[j,i]]=Wji;
,{e,1,nEdges}];

(*Adjust the diagonal elements of the weight matrix*)
Do[WijMat[[i,i]]=-Total[WijMat[[;;,i]]];,{i,1,nNodes}];

(*Return the resulting weight matrix*)
WijMat];

MapInputToWijMatWij[inputs_,inputInds_,g_,edges_,nEdges_,nNodes_,adjMat_,WijList_,WjiList_]:=Module[{tempWijList,tempWjiList,tempWijMat},
tempWijList=WijList;
tempWjiList=WjiList;
Do[
tempWijList[[inputInds[[e]]]]*=Exp[inputs[[e]]/2];
tempWjiList[[inputInds[[e]]]]*=Exp[-inputs[[e]]/2];
(*tempWijList[[inputInds[[e]]]]*=inputs[[e]];
tempWjiList[[inputInds[[e]]]]/=inputs[[e]];*)
,{e,1,Length[inputInds]}];
UpdateWeightMatrixWij[g,edges,nEdges, nNodes,adjMat,tempWijList,tempWjiList]
];

MapInputOutputWij[inputs_,inputInds_,numOuts_,g_,edges_,nEdges_,nNodes_,adjMat_,WijList_,WjiList_]:=Module[{},
GetOutput[MapInputToWijMatWij[inputs,inputInds,g,edges,nEdges,nNodes,adjMat,WijList,WjiList],numOuts]
];


nudgedStationaryVectorWij[inputs_, inputInds_,numOuts_,nudgeDeltas_,g_,edges_,nEdges_,nNodes_,adjMat_,WijList_,WjiList_]:=Module[{tempWijList,tempWjiList,tempWijMat,nudgedpiVec,ip,jp},
tempWijList=WijList;
tempWjiList=WjiList;


Do[
Do[
ip=edges[[e]][[1]];
jp=edges[[e]][[2]];
If[jp==j,
tempWijList[[e]]+=nudgeDeltas[[j]];
];
If[ip==j,
tempWjiList[[e]]+=nudgeDeltas[[j]];
];
,{e,1,nEdges}];
,{j,numOuts}];

tempWijMat = MapInputToWijMatWij[inputs, inputInds,g,edges,nEdges, nNodes,adjMat,tempWijList,tempWjiList];
nudgedpiVec=GetStationaryVector[tempWijMat];
{nudgedpiVec, GetEdgeFluxes[edges,nEdges,nudgedpiVec,tempWijMat],GetEdgeFrenesies[edges,nEdges,nudgedpiVec,tempWijMat]}
];

ComputepiAndPiprimeWij[inputs_, inputInds_,g_,edges_,nEdges_,nNodes_,WijList_,WjiList_,adjMat_,d\[Alpha]_]:=Module[
{WijMatP,WijMatM,vStatP,vStatM,tempWijList,tempWjiList,dPidWij,dPidWji},

dPidWij=ConstantArray[0,{nNodes,nEdges}];
dPidWji=ConstantArray[0,{nNodes,nEdges}];

(* apply inputs *);
tempWijList=WijList;
tempWjiList=WjiList;
Do[
tempWijList[[inputInds[[e]]]]+=inputs[[e]];
(*tempWjiList[[inputInds[[e]]]]-=inputs[[e]];*)
,{e,1,Length[inputInds]}];

Do[
tempWijList[[e]]+=d\[Alpha];
WijMatP=UpdateWeightMatrixWij[g,edges,nEdges, nNodes,adjMat, tempWijList,tempWjiList];
tempWijList[[e]]-=2*d\[Alpha];

WijMatM =UpdateWeightMatrixWij[g,edges,nEdges, nNodes,adjMat, tempWijList,tempWjiList];
vStatP=GetStationaryVector[WijMatP];
vStatM=GetStationaryVector[WijMatM];
dPidWij[[;;,e]]=(vStatP-vStatM)/(2 d\[Alpha]);

tempWijList[[e]]+=d\[Alpha];
,{e,1,nEdges}];

Do[
tempWjiList[[e]]+=d\[Alpha];
WijMatP=UpdateWeightMatrixWij[g,edges,nEdges, nNodes,adjMat, tempWijList,tempWjiList];
tempWjiList[[e]]-=2*d\[Alpha];

WijMatM =UpdateWeightMatrixWij[g,edges,nEdges, nNodes,adjMat, tempWijList,tempWjiList];
vStatP=GetStationaryVector[WijMatP];
vStatM=GetStationaryVector[WijMatM];
dPidWji[[;;,e]]=(vStatP-vStatM)/(2 d\[Alpha]);

tempWjiList[[e]]+=d\[Alpha];
,{e,1,nEdges}];

{dPidWij,dPidWji}
];


TestPredictionsWij[meanLists_,stdLists_,nTest_,inputList_,inputInds_,numOuts_,g_,edges_,nEdges_,nNodes_,adjMat_,WijList_,WjiList_]:=Module[{output, outputs, iter,newMeans, newStds},
newMeans = {};
newStds = {};

Do[
outputs ={};
Do[
iter=RandomInteger[Length[inputList[[i]]]-1]+1;
output = MapInputOutputWij[inputList[[i]][[iter]],inputInds,numOuts,g,edges,nEdges,nNodes,adjMat,WijList,WjiList][[i]];
AppendTo[outputs,output];
,{n,1,nTest}];

AppendTo[newMeans,Mean[outputs]];
	AppendTo[newStds,StandardDeviation[outputs]];
,{i,1,numOuts}];

{newMeans, newStds}
];



(* ::Subsubsection:: *)
(*Mutual information*)


addGaussians[means_,covariances_,args_]:=Module[{D=Length[means[[1]]],M=Length[means],gaussians,totalGaussian},
(*Generate the list of M Gaussian functions*)
gaussians=Table[
Exp[-1/2 (args-means[[i]]) . Inverse[covariances[[i]]] . (args-means[[i]])]/Sqrt[(2 Pi)^(Length[means[[1]]]) Det[covariances[[i]]]],{i,1,Length[means]}];
(*Define the summed Gaussian function*)
totalGaussian=Total[gaussians]/M;
(*Return the unnormalized summed Gaussian function*)
totalGaussian]

gradI[WijList_,WjiList_,WijListSym_,WjiListSym_,pF_,boundsx_,boundsy_,wp_,ag_,evalsFunc_,WkList_,dWkdWij_,dWkdWji_]:=Module[
{evalsW,WkListEval,ZEval,dWkdWijEval,dWkdWjiEval,dZdWijEval,dZdWjiEval,piEval,dPidWijEval,dPidWjiEval,marginals,Smu,Sf,inf,QijEval,QjiEval,dIdWij,dIdWji},

evalsW=Join[evalsFunc[WijListSym,WijList],evalsFunc[WjiListSym,WjiList]];

WkListEval = WkList/.evalsW;
ZEval=Total[WkListEval];
dWkdWijEval=dWkdWij/.evalsW;
dWkdWjiEval=dWkdWji/.evalsW;
dZdWijEval=Total[dWkdWijEval];
dZdWjiEval=Total[dWkdWjiEval];
piEval = WkListEval / ZEval;
dPidWijEval=Table[(dWkdWijEval[[i]]*ZEval-WkListEval[[i]]*dZdWijEval),{i,1,nNodes}]/ZEval^2;
dPidWjiEval=Table[(dWkdWjiEval[[i]]*ZEval-WkListEval[[i]]*dZdWjiEval),{i,1,nNodes}]/ZEval^2;


marginals = NIntegrate[piEval*pF[Fa],{Fa,boundsx[[1]],boundsx[[2]]},WorkingPrecision->wp,AccuracyGoal->ag,Method->{Automatic,"SymbolicProcessing"->0}];

Smu=-marginals . Log[marginals];
Sf=-piEval . Log[piEval];
inf = Smu-NIntegrate[Sf*pF[Fa],{Fa,boundsx[[1]],boundsx[[2]]},WorkingPrecision->wp,AccuracyGoal->ag,Method->{Automatic,"SymbolicProcessing"->0}];

QijEval=Log[piEval/marginals] . dPidWijEval;
dIdWij=NIntegrate[QijEval*pF[Fa],{Fa,boundsx[[1]],boundsx[[2]]},WorkingPrecision->wp,AccuracyGoal->ag,Method->{Automatic,"SymbolicProcessing"->0}];

QjiEval=Log[piEval/marginals] . dPidWjiEval;
dIdWji=NIntegrate[QjiEval*pF[Fa],{Fa,boundsx[[1]],boundsx[[2]]},WorkingPrecision->wp,AccuracyGoal->ag,Method->{Automatic,"SymbolicProcessing"->0}];

Return[{piEval,marginals,inf,dIdWij,dIdWji}];
]


gradIDiscrete[WijList_,WjiList_,WijListSym_,WjiListSym_,pDat_,evalsFunc_,WkList_,dWkdWij_,dWkdWji_]:=Module[
{evalsW,WkListEval,ZEval,dWkdWijEval,dWkdWjiEval,dZdWijEval,dZdWjiEval,piEval,dPidWijEval,dPidWjiEval,marginals,Smu,Sf,inf,QijEval,QjiEval,dIdWij,dIdWji,piAtFVals,SfAtFVals,QijAtFVals,QjiAtFVals},

evalsW=Join[evalsFunc[WijListSym,WijList],evalsFunc[WjiListSym,WjiList]];

WkListEval = WkList/.evalsW;
ZEval=Total[WkListEval];
dWkdWijEval=dWkdWij/.evalsW;
dWkdWjiEval=dWkdWji/.evalsW;
dZdWijEval=Total[dWkdWijEval];
dZdWjiEval=Total[dWkdWjiEval];
piEval = WkListEval / ZEval;
dPidWijEval=Table[(dWkdWijEval[[i]]*ZEval-WkListEval[[i]]*dZdWijEval),{i,1,nNodes}]/ZEval^2;
dPidWjiEval=Table[(dWkdWjiEval[[i]]*ZEval-WkListEval[[i]]*dZdWjiEval),{i,1,nNodes}]/ZEval^2;
piAtFVals=Transpose[Table[piEval/.{Fa->pDat[[j,1]]},{j,1,Length[pDat]}]];

marginals = Table[Sum[piAtFVals[[i,j]]*pDat[[j,2]],{j,1,Length[pDat]}],{i,1,Length[piEval]}];

Smu=-marginals . Log[marginals];
Sf=-piEval . Log[piEval];
SfAtFVals = Table[Sf/.{Fa->pDat[[j,1]]},{j,1,Length[pDat]}];


inf = Smu-Total[Table[SfAtFVals[[j]]*pDat[[j,2]],{j,1,Length[pDat]}]];

QijEval=Log[piEval/marginals] . dPidWijEval;
QijAtFVals=Transpose[Table[QijEval/.{Fa->pDat[[j,1]]},{j,1,Length[pDat]}]];
dIdWij=Table[Sum[QijAtFVals[[i,j]]*pDat[[j,2]],{j,1,Length[pDat]}],{i,1,Length[QijAtFVals]}];


QjiEval=Log[piEval/marginals] . dPidWjiEval;
QjiAtFVals=Transpose[Table[QjiEval/.{Fa->pDat[[j,1]]},{j,1,Length[pDat]}]];
dIdWji=Table[Sum[QjiAtFVals[[i,j]]*pDat[[j,2]],{j,1,Length[pDat]}],{i,1,Length[QijAtFVals]}];

Return[{piEval,marginals,inf,dIdWij,dIdWji}];
]


BlahutArimoto[pDat_,QMat_,maxIterations_:1000,tolerance_:10^-6]:=Module[{NF,Nn,pIn,pOut,newPIn,mutualInfo,Iold,Inew,iterations,i,j,tmp,cj,infList},
NF=Length[pDat];(*Number of input symbols*)
Nn=Length[QMat];(*Number of output symbols*)

(*Initialize the input distribution (pIn),assume uniform if not provided*)pIn=If[Length[pDat[[2]]]===0,ConstantArray[1/NF,NF],pDat[[;;,2]]];

Iold=0;
iterations=0;
infList = {};

While[iterations<maxIterations,

(*Step 1:Compute output probabilities given input distribution*)
pOut=QMat . pIn;

(*Step 2:Update input distribution*)
cj=Table[Exp[Sum[QMat[[k,j]]Log[QMat[[k,j]]/pOut[[k]]],{k,1,Nn}]],{j,1,NF}];
newPIn=pIn*cj/(pIn . cj);

(*Step 3:Compute mutual information*)mutualInfo=Sum[pIn[[j]]*QMat[[k,j]]*Log[QMat[[k,j]]/pOut[[k]]],{j,1,NF},{k,1,Nn}];

Inew=mutualInfo;
(*Check convergence*)
If[Abs[Inew-Iold]<tolerance,Break[]];
(*Update variables for next iteration*)
pIn=newPIn;
Iold=Inew;
AppendTo[infList, Inew];
iterations++;];
(*Return the optimized input distribution and channel capacity*)
{pIn,Inew,iterations,infList}]



(*Define the module with inputs and outputs*)
optimizationModule[WijListIn_,WjiListIn_,WijListSym_,WjiListSym_,pDat_,evalsFunc_,WkList_,
dWkdWij_,dWkdWji_,maxIterations_:500,tolerance_:10^-6,delta_:0.1]:=Module[{infList={},lambda=10,clipTimes={},clipCount=0,inf,dIdWij,dIdWji,piEval,marginals,cij,cji,n,WijList,WjiList},

WijList = WijListIn;
WjiList = WjiListIn;
Do[

(*Step 1:Calculate gradients and mutual information*)

{piEval,marginals,inf,dIdWij,dIdWji}=gradIDiscrete[WijList,WjiList,WijListSym,WjiListSym,pDat,evalsFunc,WkList,dWkdWij,dWkdWji];

(*Step 2:Append mutual information to list*)
AppendTo[infList,inf];

(*Step 3:Update WijList and WjiList*)
WijList=WijList+delta*dIdWij;
WjiList=WjiList+delta*dIdWji;

(*Step 4:Clip Wij and Wji within given bounds*)
WijList=Clip[WijList,{10^-4,100}];
WjiList=Clip[WjiList,{10^-4,100}];

(*Step 5:Count the number of elements that hit the clipping bounds*)
cij=Count[WjiList,_?(Abs[#-10^-4]<10^-6&)];
cji=Count[WijList,_?(Abs[#-10^-4]<10^-6&)];
If[cij+cji>clipCount,AppendTo[clipTimes,n];clipCount=cij+cji];

(*Step 6:Check for convergence by comparing the last two values of inf*)
If[n>1&&Abs[infList[[-1]]-infList[[-2]]]<tolerance,Break[]];,
{n,1,maxIterations}];(*End of Do loop*)

(*Return results:optimized WijList,WjiList,infList,clipTimes*)
{WijList,WjiList,infList,clipTimes,n,piEval,inf}]


ComputeIInterpO[WijEvalFunc_,pFAtFs_,FRange_,wp_,ag_]:=Module[{PiAtFs,PiAtFIV,PiAtFInterp,PiAtFInterpT,\[Mu]k,dk,dkI,Fa},
PiAtFs=Table[GetStationaryVector[WijEvalFunc[F]],{F,FRange}];
PiAtFIV=Table[Table[{FRange[[FInd]],PiAtFs[[FInd]][[k]]},{FInd,1,Length[FRange]}],{k,1,nNodes}];
PiAtFInterp=Table[Interpolation[PiAtFIV[[k]]],{k,1,nNodes}];
PiAtFInterpT[F_]:=Table[PiAtFInterp[[k]][F],{k,1,nNodes}];
\[Mu]k=Table[NIntegrate[Interpolation[Table[{FRange[[FInd]],pFAtFs[[FInd]]*PiAtFInterp[[k]][FRange[[FInd]]]},{FInd,1,Length[FRange]}]][Fp],{Fp,FRange[[1]],FRange[[-1]]},Method->{Automatic,"SymbolicProcessing"->0},WorkingPrecision->wp,AccuracyGoal->ag],{k,1,nNodes}];
dk[F_]:=PiAtFInterpT[F] . Log[PiAtFInterpT[F]/\[Mu]k];
dkI=Interpolation[Table[{FRange[[FInd]],pFAtFs[[FInd]]*dk[FRange[[FInd]]]},{FInd,1,Length[FRange]}]];
Return[NIntegrate[dkI[F],{F,FRange[[1]],FRange[[-1]]},Method->{Automatic,"SymbolicProcessing"->0},WorkingPrecision->wp,AccuracyGoal->ag]]
]

ComputeIInterp[WijEvalFunc_,pFAtFs_,FRange_,wp_,ag_]:=Module[{PiAtFs,PiAtFIV,PiAtFInterp,PiAtFInterpT,\[Mu]k,dk,dkI,Fa,PiAtFInterpTValues,dkValues,dkInterpolationData},
(*Step 1:Compute the stationary vectors over the range FRange*)
PiAtFs=GetStationaryVector[WijEvalFunc[#]]&/@FRange;

(*Step 2:Construct interpolation points for each node using a flattened table approach*)
PiAtFIV=Table[Transpose[{FRange,PiAtFs[[All,k]]}],{k,1,nNodes}];

(*Step 3:Create interpolating functions for each node*)
PiAtFInterp=Interpolation/@PiAtFIV;

(*Step 4:Define the function to evaluate the interpolated values at a given F*)
PiAtFInterpT[F_]:=Table[PiAtFInterp[[k]][F],{k,1,nNodes}];
\[Mu]k=Table[NIntegrate[Interpolation[Table[{FRange[[FInd]],pFAtFs[[FInd]]*PiAtFInterp[[k]][FRange[[FInd]]]},{FInd,1,Length[FRange]}]][Fp],{Fp,FRange[[1]],FRange[[-1]]},Method->{Automatic,"SymbolicProcessing"->0},WorkingPrecision->wp,AccuracyGoal->ag],{k,1,nNodes}];
PiAtFInterpTValues=Table[PiAtFInterpT[F],{F,FRange}];
dkValues=Table[With[{PiAtF=PiAtFInterpTValues[[FInd]]},PiAtF . Log[PiAtF/\[Mu]k]],{FInd,1,Length[FRange]}];
dkInterpolationData=Transpose[{FRange,pFAtFs*dkValues}];
dkI=Interpolation[dkInterpolationData];
Return[NIntegrate[dkI[F],{F,FRange[[1]],FRange[[-1]]},Method->{Automatic,"SymbolicProcessing"->0},WorkingPrecision->wp,AccuracyGoal->ag]];
]


(*ComputeIGradInterp[WijList_,WjiList_,WijListSym_,WjiListSym_,WijMatSymInput_,evalsFunc_,pFAtFs_,FRange_,d\[Alpha]_,nEdges_,wp_,ag_]:=Module[
{dIdWij,dIdWji,tempWijList,vStatM,tempWjiList,tempBijList,dPidFij,Fa,IP,IM,evalsW,WijEvalFunc},

dIdWij=ConstantArray[0,{nEdges}];
dIdWji=ConstantArray[0,{nEdges}];

tempWijList=WijList;
tempWjiList=WjiList;

Do[
tempWijList[[e]]+=d\[Alpha];
evalsW=Join[evalsFunc[WijListSym,tempWijList],evalsFunc[WjiListSym,tempWjiList]];
WijEvalFunc[F_]:=Evaluate[N[WijMatSymInput[F]]/.evalsW];
IP=ComputeIInterp[WijEvalFunc,pFAtFs,FRange,wp,ag];

tempWijList[[e]]-=2*d\[Alpha];
evalsW=Join[evalsFunc[WijListSym,tempWijList],evalsFunc[WjiListSym,tempWjiList]];
WijEvalFunc[F_]:=Evaluate[N[WijMatSymInput[F]]/.evalsW];
IM=ComputeIInterp[WijEvalFunc,pFAtFs,FRange,wp,ag];

tempWijList[[e]]+=d\[Alpha];
dIdWij[[e]]=(IP-IM)/(2 d\[Alpha]);
,{e,1,nEdges}];


Do[
tempWjiList[[e]]+=d\[Alpha];
evalsW=Join[evalsFunc[WijListSym,tempWijList],evalsFunc[WjiListSym,tempWjiList]];
WijEvalFunc[F_]:=Evaluate[N[WijMatSymInput[F]]/.evalsW];
IP=ComputeIInterp[WijEvalFunc,pFAtFs,FRange,wp,ag];

tempWjiList[[e]]-=2*d\[Alpha];
evalsW=Join[evalsFunc[WijListSym,tempWijList],evalsFunc[WjiListSym,tempWjiList]];
WijEvalFunc[F_]:=Evaluate[N[WijMatSymInput[F]]/.evalsW];
IM=ComputeIInterp[WijEvalFunc,pFAtFs,FRange,wp,ag];

tempWjiList[[e]]+=d\[Alpha];
dIdWji[[e]]=(IP-IM)/(2 d\[Alpha]);
,{e,1,nEdges}];

Return[{dIdWij,dIdWji}]
];*)


ComputePiEvalInterp[WijList_,WijListSym_,WjiList_,WjiListSym_]:=Module[{evalsW,WijEvalFunc,PiAtFs,PiAtFIV,PiAtFInterp,PiAtFInterpT},
evalsW=Join[evalsFunc[WijListSym,WijList],evalsFunc[WjiListSym,WjiList]];
WijEvalFunc[F_]:=Evaluate[N[WijMatSymInput[F]]/.evalsW];

(*Step 1:Compute the stationary vectors over the range FRange*)
PiAtFs=GetStationaryVector[WijEvalFunc[#]]&/@FRange;
(*Step 2:Construct interpolation points for each node using a flattened table approach*)
PiAtFIV=Table[Transpose[{FRange,PiAtFs[[All,k]]}],{k,1,nNodes}];
(*Step 3:Create interpolating functions for each node*)
PiAtFInterp=Interpolation/@PiAtFIV;
(*Step 4:Define the function to evaluate the interpolated values at a given F*)
PiAtFInterpT[F_]:=Table[PiAtFInterp[[k]][F],{k,1,nNodes}];

Return[PiAtFInterpT]
];

ComputeIGradInterp[WijList_,WjiList_,WijListSym_,WjiListSym_,WijMatSymInput_,evalsFunc_,pFAtFs_,FRange_,d\[Alpha]_,nEdges_,wp_,ag_]:=Module[
{dIdWij,dIdWji,tempWijList,vStatM,tempWjiList,tempBijList,dPidFij,Fa,IP,II,evalsW,WijEvalFunc},

dIdWij=ConstantArray[0,{nEdges}];
dIdWji=ConstantArray[0,{nEdges}];

tempWijList=WijList;
tempWjiList=WjiList;

evalsW=Join[evalsFunc[WijListSym,tempWijList],evalsFunc[WjiListSym,tempWjiList]];
WijEvalFunc[F_]:=Evaluate[N[WijMatSymInput[F]]/.evalsW];
II=ComputeIInterp[WijEvalFunc,pFAtFs,FRange,wp,ag];

Do[
tempWijList[[e]]+=d\[Alpha];
evalsW=Join[evalsFunc[WijListSym,tempWijList],evalsFunc[WjiListSym,tempWjiList]];
WijEvalFunc[F_]:=Evaluate[N[WijMatSymInput[F]]/.evalsW];
IP=ComputeIInterp[WijEvalFunc,pFAtFs,FRange,wp,ag];

tempWijList[[e]]-=d\[Alpha];
dIdWij[[e]]=(IP-II)/(d\[Alpha]);
,{e,1,nEdges}];


Do[
tempWjiList[[e]]+=d\[Alpha];
evalsW=Join[evalsFunc[WijListSym,tempWijList],evalsFunc[WjiListSym,tempWjiList]];
WijEvalFunc[F_]:=Evaluate[N[WijMatSymInput[F]]/.evalsW];
IP=ComputeIInterp[WijEvalFunc,pFAtFs,FRange,wp,ag];

tempWjiList[[e]]-=d\[Alpha];
dIdWji[[e]]=(IP-II)/(d\[Alpha]);
,{e,1,nEdges}];

Return[{II,dIdWij,dIdWji}]
];


smoothClip[x_,min_,max_]:=((max-min)/2*Tanh[2*x/(max-min)])+min (max+min)/2


BacktrackingLineSearch[f_,gradfE_,x_,d_,\[Alpha]init_:1.0,\[Rho]_:0.5,c_:1*10^-4,maxIter_:50]:=Module[{\[Alpha]=\[Alpha]init,iter=0,fE},
(*Define the Armijo condition*)
fE=f[x];
While[f[Clip[x+\[Alpha] d,{10^-8,100}]]>fE+c \[Alpha] (gradfE . d)&&iter<maxIter,
\[Alpha]*=\[Rho];
iter++;];
(*Return the optimal step size*)
\[Alpha]]

ConjugateGradientFR[f_,gradf_,x0_,\[Alpha]init_:1.0,\[Rho]_:0.5,c_:1*10^-4,maxIter_:50,tol_:1*10^-6]:=Module[
{x=x0,g,d,\[Alpha],iter=0,\[Beta],gradfE,fList, err},

(*Initial gradient and search direction*)
g=gradf[x];
d=-g;
fList={10^10,f[x]};

(*Iterative process*)
While[Abs[fList[[-1]]-fList[[-2]]]>tol&&iter<maxIter,

(*Step size using Armijo-based line search*)
\[Alpha]=BacktrackingLineSearch[f,g,x,d,\[Alpha]init,\[Rho],c];

(*Update the position*)
err=0*10^-1;
x=x+\[Alpha] d + RandomReal[{-err,err},Length[x]];
x = Clip[x,{10^-8,100}];

(*Compute the new gradient*)
g=gradf[x];

(*Fletcher-Reeves coefficient*)
\[Beta]=Norm[g]^2/Norm[d]^2;

(*Update the search direction*)
d=-g+\[Beta] d;

(*Increment iteration count*)
iter++;
AppendTo[fList,f[x]];
];

(*Return the optimal point and iteration count*)
{x,iter,fList[[2;;-1]]}]


(* ::Subsubsection::Closed:: *)
(*Plotting options*)


SetOptions[ListPlot,
Frame->True,
Axes->False,
FrameTicksStyle->Thickness[.001],
FrameStyle->Directive[Black,Thickness[0.004]],
LabelStyle->{FontFamily->"Arial",Black,FontSize->16}];

SetOptions[Plot,
Frame->True,
Axes->False,
FrameTicksStyle->Thickness[.001],
FrameStyle->Directive[Black,Thickness[0.004]],
LabelStyle->{FontFamily->"Arial",Black,FontSize->16}];

SetOptions[ListLogPlot,
Frame->True,
Axes->False,
FrameTicksStyle->Thickness[.001],
FrameStyle->Directive[Black,Thickness[0.004]],
LabelStyle->{FontFamily->"Arial",Black,FontSize->16}];

SetOptions[ListDensityPlot,
Frame->True,
Axes->False,
FrameTicksStyle->Thickness[.001],
FrameStyle->Directive[Black,Thickness[0.004]],
LabelStyle->{FontFamily->"Arial",Black,FontSize->16}];

SetOptions[DensityPlot,
Frame->True,
Axes->False,
FrameTicksStyle->Thickness[.001],
FrameStyle->Directive[Black,Thickness[0.004]],
LabelStyle->{FontFamily->"Arial",Black,FontSize->16}];

SetOptions[Plot3D,
AxesStyle->Directive[Black,Thickness[0.004]],
LabelStyle->{FontFamily->"Arial",Black,FontSize->16}];

