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

param M; let M:=100000;

param nT;

#param Ugt_init {GEND,LOAD};
#param Ugt_init_best {GEND,LOAD};
#@@@@@@@@@@@@@@@
#### VARIABLES:
var obj_M;
var bus_angle {n in BUS, t in LOAD};        # Variable for Bus Angles
var line_flow {j in BRANCH, t in LOAD};     # Variable for all line flows
var gen_supply {g in GEND, t in LOAD};      # Variable for GEN Supply
var reserve{g in GEND, t in LOAD} >= 0;

# Generation Unit Commitment Variables:
var Ugt{g in GEND, t in LOAD} binary; # unit commitment var
var Vgt{g in GEND, t in LOAD} binary; #>= 0, <=1; # startup var (binary var modeled as continuous since it will have binary solution)

#########

param lodf {BRANCH,BRANCH};

#@@@@@@@@@@@@@@@
#### OBJECTIVE:
# Objective is to Minimize Cost
minimize M_COST: sum{g in GEND, t in LOAD}(gen_supply[g,t]*genC_Cost[g]+Ugt[g,t]*genC_NLoad[g]+Vgt[g,t]*genC_Startup[g]);

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
	+ sum{g in GEND: genD_bus[g]==k}gen_supply[g,t] - Bus_Pd[k,t]=0; # supply and load at bus