## Author: Arun Ramesh, University of Houston. https://rpglab.github.io/people/Arun-Venkatesh-Ramesh/
#
## Source webpage: https://rpglab.github.io/resources/FL-ML-R-SCUC_Python/
#
## If you use any codes/data here for your work, please cite the following paper: 
#       Arun Venkatesh Ramesh and Xingpeng Li, “Feasibility Layer Aided Machine Learning Approach for Day-Ahead Operations”, 
#       IEEE Transactions on Power Systems, Apr. 2023.

## SCUC consider N-1 (Only Transmission Constraints) Original Formulation

set BUS;    # set of buses
set BRANCH; # set of branches
set GEND;   # Gen Data
set LOAD;   # Load Percent data of peak load

#@@@@@@@@@@@@@@@
#### PARAMETERS:
# Bus Data
param bus_num		{BUS}; # Bus Number
param bus_Pd		{BUS}; # Real Power Demand 

# GENData
param genD_bus		{GEND}; # GEN location
param genD_minUP	{GEND}; # Min UP Time
param genD_minDN	{GEND}; # Min Down Time
param genD_status	{GEND}; # Initial UC Variable (1 for on)
param genD_Pmax		{GEND}; # Max gen production
param genD_Pmin     {GEND}; # Min gen production when committed
param genC_Startup 	{GEND}; # startup cost
param genC_Cost		{GEND}; # Linear Cost Term
param genC_NLoad	{GEND}; # No Load Cost
param SPRamp		{GEND}; # 10 Min Spin Ramp
param NSRamp		{GEND}; # 10 Min Non Spin Ramp
param HRamp			{GEND}; # Hourly Ramp
param StartRamp		{GEND}; # Startup/Shutdown Ramp
param gen_Style		{GEND}; # 1 denotes fast start-up Gen, 0 denotes slow start-up Gen


# Branch Data
param branch_fbus	{BRANCH}; # from bus for line
param branch_tbus	{BRANCH}; # to bus for line
param branch_b		{BRANCH}; # line susceptance
param branch_rateA	{BRANCH}; # long term thermal rating
param branch_rateC	{BRANCH}; # emergency thermal rating
param branch_radial	{BRANCH}; # whether you will monitor the line

# Load Data
param load_pcnt		{LOAD}; # the percentage of annual peak

# Additional Parameters that are not loaded through sets:
param Bus_Pd{n in BUS, t in LOAD};  # Creates the hourly load per bus
param MBase; let MBase:=100; # the MVA Base
#@@@@@@@@@@@@@@@

param BigM; let BigM:=100000;

#param Ugt_init {GEND,LOAD};
#param Ugt_init_best {GEND,LOAD};
#@@@@@@@@@@@@@@@
#### VARIABLES:
var obj_M;
var bus_angle {n in BUS, t in LOAD};        # Variable for Bus Angles
var line_flow {j in BRANCH, t in LOAD};     # Variable for all line flows
var gen_supply {g in GEND, t in LOAD};      # Variable for GEN Supply
var reserve{g in GEND, t in LOAD} >= 0;
var genslackInc {t in LOAD} >=0;
var genslackDec {t in LOAD} >=0;
#var loadslackInc {t in LOAD} >=0;
#var loadslackDec {t in LOAD} >=0;
# Generation Unit Commitment Variables:
var Ugt{g in GEND, t in LOAD} binary; # unit commitment var
var Vgt{g in GEND, t in LOAD} binary; # startup var (binary var modeled as continuous since it will have binary solution)

var Ugt_mfPlus{g in GEND, t in LOAD} binary;
var Ugt_mfMinus{g in GEND, t in LOAD} binary;
var Vgt_mf{g in GEND, t in LOAD} binary;

var Ugt_mfPlus2{t in LOAD} binary;
var Ugt_mfMinus2{t in LOAD} binary;
var Vgt_mf2{t in LOAD} binary;

var Ugt_mf3{t in LOAD} binary;
var Vgt_mf3{t in LOAD} binary;
var Z{t in LOAD} binary; 
#########

param lodf {BRANCH,BRANCH};

#@@@@@@@@@@@@@@@
#### OBJECTIVE:
# Objective is to Minimize Cost
minimize M_COST: sum{g in GEND, t in LOAD}(gen_supply[g,t]*genC_Cost[g]+Ugt[g,t]*genC_NLoad[g]+Vgt[g,t]*genC_Startup[g]) ;
#+ sum{t in LOAD}(8000*(genslackInc[t]+genslackDec[t]));

minimize Obj1: sum{g in GEND, t in LOAD} (Ugt_mfPlus[g,t] + Ugt_mfMinus[g,t]);

minimize Obj2: sum{t in LOAD} (Ugt_mfPlus2[t] + Ugt_mfMinus2[t]);

minimize Obj3: sum{t in LOAD} (genFix[allprdsample,genIter,t]*(Z[t]));
#### CONSTRAINTS:

#### Base case modeling of generation:
subject to PGen1{g in GEND, t in LOAD}: # Gen min constraint for steady-state
	genD_Pmin[g]*Ugt[g,t] <= gen_supply[g,t];

subject to unitReserve2{g in GEND, t in LOAD}:
	gen_supply[g,t] + reserve[g,t] <= genD_Pmax[g]*Ugt[g,t];

subject to unitReserve1{g in GEND, t in LOAD}: 
	reserve[g,t] <= SPRamp[g]*Ugt[g,t];

subject to systemReserve{g in GEND, t in LOAD}:
	sum{s in GEND}(reserve[s,t]) >= gen_supply[g,t] + reserve[g,t];

###	Ramp up and Ramp down constraints
subject to HR_RampUP{g in GEND, t in LOAD: t>=2}:
	gen_supply[g,t]-gen_supply[g,t-1] <= HRamp[g]*Ugt[g,t-1] + StartRamp[g]*Vgt[g,t];

subject to HR_RampDN{g in GEND, t in LOAD: t>=2}:
	gen_supply[g,t-1]-gen_supply[g,t] <= HRamp[g]*Ugt[g,t] + StartRamp[g]*(Vgt[g,t]-Ugt[g,t]+Ugt[g,t-1]);
	
subj to HR_RampUP2{g in GEND}:
	gen_supply[g,1]-gen_supply[g,nT] <= HRamp[g]*Ugt[g,nT] + StartRamp[g]*Vgt[g,1];

subj to HR_RampDN2{g in GEND}:
	gen_supply[g,nT]-gen_supply[g,1] <= HRamp[g]*Ugt[g,1] + StartRamp[g]*(Vgt[g,1]-Ugt[g,1]+Ugt[g,nT]);
	
### Min up time constraint:
subj to FacetUP{g in GEND, t in LOAD: t>=genD_minUP[g] }:
	sum{m in LOAD: t-genD_minUP[g]+1<=m<=t}Vgt[g,m] <= Ugt[g,t];

subj to FacetUP2{g in GEND, t in LOAD:  t<=genD_minUP[g]-1 }:
	sum{m in LOAD: nT+t-genD_minUP[g]+1<=m<=nT}Vgt[g,m] + sum{n in LOAD: 1<=n<=t}Vgt[g,n] <= Ugt[g,t] ;

### Min down time constraint:
subj to FacetDN{g in GEND, t in LOAD: t<=nT-genD_minDN[g]}:
	sum{m in LOAD: t+1<=m<=t+genD_minDN[g]}Vgt[g,m] <= 1-Ugt[g,t];
	
subj to FacetDN2{g in GEND, t in LOAD: t>=nT-genD_minDN[g]+1 }:
	sum{m in LOAD: 1<=m<=t+genD_minDN[g]-nT}Vgt[g,m] + sum{n in LOAD: t+1<=n<=nT}Vgt[g,n] <= 1-Ugt[g,t];

###
subject to SUSD{g in GEND, t in LOAD: t>=2}:
	Vgt[g,t] >= Ugt[g,t] - Ugt[g,t-1];

subject to SUSD2{g in GEND}: #SUSD constraint for t=1
	Vgt[g,1] >= Ugt[g,1] - Ugt[g,nT];
	
subject to slack{t in LOAD}: bus_angle[1,t] = 0;

### Base case modeling of power flow:
subject to Line_FlowEq1{j in BRANCH, t in LOAD}:	#Line Flow Constraint for steady-state:
	branch_b[j]*(bus_angle[branch_tbus[j],t]-bus_angle[branch_fbus[j],t])-(line_flow[j,t]/100) = 0;

subject to Thermal2{j in BRANCH, t in LOAD}:		# Thermal Constraint, steady-state
	#S[j,t]*
	branch_rateA[j] >= line_flow[j,t]; # based on Rate A
	#1000 >= line_flow[j,t]; # based on Rate A

subject to Thermal1{j in BRANCH, t in LOAD}:		# Thermal Constraint 2, steady-state
	#S[j,t]*
	(-branch_rateA[j]) <= line_flow[j,t]; #based on Rate A
	#-1000 <= line_flow[j,t]; #based on Rate A

subject to PowerBal{k in BUS, t in LOAD}: # Node Balance Constraint, steady-state
	sum{j in BRANCH: branch_tbus[j] ==k}line_flow[j,t] #flows into bus
	- sum{j in BRANCH: branch_fbus[j]==k}line_flow[j,t]# flows out of bus
	+ sum{g in GEND: genD_bus[g]==k}gen_supply[g,t] #+ genslackInc[t] - genslackDec[t] 
	- Bus_Pd[k,t] = 0; # supply and load at bus

#Model 1 constraints

### Min up time constraint:
subj to tUP_PP{g in GEND, t in LOAD: t>=genD_minUP[g] }:
	sum{m in LOAD: t-genD_minUP[g]+1<=m<=t}Vgt_mf[g,m] <= (Ugt_mfPlus[g,t] - Ugt_mfMinus[g,t] + Ugt_Predict_m[g,t]);

subj to tUP2_PP{g in GEND, t in LOAD:  t<=genD_minUP[g]-1 }:
	sum{m in LOAD: nT+t-genD_minUP[g]+1<=m<=nT}Vgt_mf[g,m] + sum{n in LOAD: 1<=n<=t}Vgt_mf[g,n] <= (Ugt_mfPlus[g,t] - Ugt_mfMinus[g,t] + Ugt_Predict_m[g,t]) ;
		
### Min down time constraint:
subj to tDN_PP{g in GEND, t in LOAD: t<=nT-genD_minDN[g]}:
	sum{m in LOAD: t+1<=m<=t+genD_minDN[g]}Vgt_mf[g,m] <= 1 - (Ugt_mfPlus[g,t] - Ugt_mfMinus[g,t] + Ugt_Predict_m[g,t]);
	
subj to tDN2_PP{g in GEND, t in LOAD: t>=nT-genD_minDN[g]+1 }:
	sum{m in LOAD: 1<=m<=t+genD_minDN[g]-nT}Vgt_mf[g,m] + sum{n in LOAD: t+1<=n<=nT}Vgt_mf[g,n] <= 1 - (Ugt_mfPlus[g,t] - Ugt_mfMinus[g,t] + Ugt_Predict_m[g,t]);

###
subject to SUSD_PP{g in GEND, t in LOAD: t>=2}:
	Vgt_mf[g,t] >= (Ugt_mfPlus[g,t] - Ugt_mfMinus[g,t]+ Ugt_Predict_m[g,t]) - (Ugt_mfPlus[g,t-1] - Ugt_mfMinus[g,t-1] + Ugt_Predict_m[g,t-1]);

subject to SUSD2_PP{g in GEND}: #SUSD constraint for t=1
	Vgt_mf[g,1] >= (Ugt_mfPlus[g,1] - Ugt_mfMinus[g,1] + Ugt_Predict_m[g,1]) - (Ugt_mfPlus[g,nT] - Ugt_mfMinus[g,nT] + Ugt_Predict_m[g,nT]);

subject to Pred_PP{g in GEND, t in LOAD}: 
	Ugt_mfPlus[g,t] + Ugt_mfMinus[g,t] <= 1;
	
subject to MeetDmd {t in LOAD}:
	sum{g in GEND} ((Ugt_mfPlus[g,t] - Ugt_mfMinus[g,t] + Ugt_Predict_m[g,t])*genD_Pmax[g]) >= sum{n in BUS} Bus_Pd[n,t];
	
subject to MeetMinDmd {t in LOAD}:
	sum{g in GEND} ((Ugt_mfPlus[g,t] - Ugt_mfMinus[g,t] + Ugt_Predict_m[g,t])*genD_Pmin[g]) <= sum{n in BUS} Bus_Pd[n,t];
	

#Model 2 constraints

### Min up time constraint:
subj to tUP_PP2{t in LOAD: t>=genD_minUP[genIter] }:
	sum{n in LOAD: t-genD_minUP[genIter]+1<=n<=t}Vgt_mf2[n] <= (Ugt_mfPlus2[t] - Ugt_mfMinus2[t] + Ugt_Predict_m[genIter,t]);

subj to tUP2_PP2{t in LOAD:  t<=genD_minUP[genIter]-1 }:
	sum{n in LOAD: nT+t-genD_minUP[genIter]+1<=n<=nT}Vgt_mf2[n] + sum{n in LOAD: 1<=n<=t}Vgt_mf2[n] <= (Ugt_mfPlus2[t] - Ugt_mfMinus2[t] + Ugt_Predict_m[genIter,t]) ;
		
### Min down time constraint:
subj to tDN_PP2{t in LOAD: t<=nT-genD_minDN[genIter]}:
	sum{n in LOAD: t+1<=n<=t+genD_minDN[genIter]}Vgt_mf2[n] <= 1 - (Ugt_mfPlus2[t] - Ugt_mfMinus2[t] + Ugt_Predict_m[genIter,t]);
	
subj to tDN2_PP2{t in LOAD: t>=nT-genD_minDN[genIter]+1 }:
	sum{n in LOAD: 1<=n<=t+genD_minDN[genIter]-nT}Vgt_mf2[n] + sum{n in LOAD: t+1<=n<=nT}Vgt_mf2[n] <= 1 - (Ugt_mfPlus2[t] - Ugt_mfMinus2[t] + Ugt_Predict_m[genIter,t]);

###
subject to SUSD_PP2{t in LOAD: t>=2}:
	Vgt_mf2[t] >= (Ugt_mfPlus2[t] - Ugt_mfMinus2[t]+ Ugt_Predict_m[genIter,t]) - (Ugt_mfPlus2[t-1] - Ugt_mfMinus2[t-1] + Ugt_Predict_m[genIter,t-1]);

subject to SUSD2_PP2: #SUSD constraint for t=1
	Vgt_mf2[1] >= (Ugt_mfPlus2[1] - Ugt_mfMinus2[1] + Ugt_Predict_m[genIter,1]) - (Ugt_mfPlus2[nT] - Ugt_mfMinus2[nT] + Ugt_Predict_m[genIter,nT]);

subject to Pred_PP2{t in LOAD}: 
	Ugt_mfPlus2[t] + Ugt_mfMinus2[t] <= 1;
	
#Model 3 constraints
### Min up time constraint:
subj to tUP_PP3{t in LOAD: t>=genD_minUP[genIter] }:
	sum{n in LOAD: t-genD_minUP[genIter]+1<=n<=t}Vgt_mf3[n] <= Ugt_mf3[t];

subj to tUP2_PP3{t in LOAD:  t<=genD_minUP[genIter]-1 }:
	sum{n in LOAD: nT+t-genD_minUP[genIter]+1<=n<=nT}Vgt_mf3[n] + sum{n in LOAD: 1<=n<=t}Vgt_mf3[n] <= Ugt_mf3[t] ;
		
### Min down time constraint:
subj to tDN_PP3{t in LOAD: t<=nT-genD_minDN[genIter]}:
	sum{n in LOAD: t+1<=n<=t+genD_minDN[genIter]}Vgt_mf3[n] <= 1 - Ugt_mf3[t];
	
subj to tDN2_PP3{t in LOAD: t>=nT-genD_minDN[genIter]+1 }:
	sum{n in LOAD: 1<=n<=t+genD_minDN[genIter]-nT}Vgt_mf3[n] + sum{n in LOAD: t+1<=n<=nT}Vgt_mf3[n] <= 1 - Ugt_mf3[t];

###
subject to SUSD_PP3{t in LOAD: t>=2}:
	Vgt_mf3[t] >= Ugt_mf3[t] - Ugt_mf3[t-1];

subject to SUSD2_PP3: #SUSD constraint for t=1
	Vgt_mf3[1] >= Ugt_mf3[1] - Ugt_mf3[nT];
	
subject to absolute1{t in LOAD}:
	Z[t] >= (Ugt_mf3[t] - Ugt_Predict_m[genIter,t]);
	
subject to absolute2{t in LOAD}:
	Z[t] >= (Ugt_Predict_m[genIter,t] - Ugt_mf3[t]);

 
