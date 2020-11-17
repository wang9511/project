
const

  NODE_NUM : 2;
  DATA_NUM : 2;

type

  NODE : 1..NODE_NUM;
  DATA : 1..DATA_NUM;

  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum{I,S,E};

  CACHE : record
    State : CACHE_STATE;
    Data : DATA;
  end;

  MSG_CMD : enum{Empty,ReqS,ReqE,Inv,InvAck,GntS,GntE};

  MSG : record
    Cmd : MSG_CMD;
    Data : DATA;
  end;
  new_type_0 : array [ NODE ] of CACHE;
  new_type_1 : array [ NODE ] of MSG;
  new_type_2 : array [ NODE ] of MSG;
  new_type_3 : array [ NODE ] of MSG;
  new_type_4 : array [ NODE ] of boolean;
  new_type_5 : array [ NODE ] of boolean;

var

  Cache : new_type_0;
  Chan1 : new_type_1;
  Chan2 : new_type_2;
  Chan3 : new_type_3;
  InvSet : new_type_4;
  ShrSet : new_type_5;
  ExGntd : boolean;
  CurCmd : MSG_CMD;
  CurPtr : ABS_NODE;
  MemData : DATA;
  AuxData : DATA;

ruleset  i : NODE do
rule "RecvGntE1"
  Chan2[i].Cmd = GntE
==>
begin
  Cache[i].State := E;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvGntS2"
  Chan2[i].Cmd = GntS
==>
begin
  Cache[i].State := S;
  Cache[i].Data := Chan2[i].Data;
  Chan2[i].Cmd := Empty;
  undefine Chan2[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntE3"
  CurCmd = ReqE &
  CurPtr = i &
  Chan2[i].Cmd = Empty &
  ExGntd = false &
  forall j : NODE do
    ShrSet[j] = false
  end
==>
begin
  Chan2[i].Cmd := GntE;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  ExGntd := true;
  CurCmd := Empty;
  undefine CurPtr;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendGntS4"
  CurCmd = ReqS &
  CurPtr = i &
  Chan2[i].Cmd = Empty &
  ExGntd = false
==>
begin
  Chan2[i].Cmd := GntS;
  Chan2[i].Data := MemData;
  ShrSet[i] := true;
  CurCmd := Empty;
  undefine CurPtr;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck5"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd = true
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
  ExGntd := false;
  MemData := Chan3[i].Data;
  undefine Chan3[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvInvAck6"
  Chan3[i].Cmd = InvAck &
  CurCmd != Empty &
  ExGntd != true
==>
begin
  Chan3[i].Cmd := Empty;
  ShrSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck7"
  Chan2[i].Cmd = Inv &
  Chan3[i].Cmd = Empty &
  Cache[i].State = E
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  Chan3[i].Data := Cache[i].Data;
  Cache[i].State := I;
  undefine Cache[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInvAck8"
  Chan2[i].Cmd = Inv &
  Chan3[i].Cmd = Empty &
  Cache[i].State != E
==>
begin
  Chan2[i].Cmd := Empty;
  Chan3[i].Cmd := InvAck;
  Cache[i].State := I;
  undefine Cache[i].Data;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv9"
  Chan2[i].Cmd = Empty &
  InvSet[i] = true &
  CurCmd = ReqE
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendInv10"
  Chan2[i].Cmd = Empty &
  InvSet[i] = true &
  CurCmd = ReqS &
  ExGntd = true
==>
begin
  Chan2[i].Cmd := Inv;
  InvSet[i] := false;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqE11"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqE
==>
begin
  CurCmd := ReqE;
  CurPtr := i;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;
endruleset;

ruleset  i : NODE do
rule "RecvReqS12"
  CurCmd = Empty &
  Chan1[i].Cmd = ReqS
==>
begin
  CurCmd := ReqS;
  CurPtr := i;
  Chan1[i].Cmd := Empty;
  for j : NODE do
    InvSet[j] := ShrSet[j];
  endfor;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE13"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqE14"
  Chan1[i].Cmd = Empty &
  Cache[i].State = S
==>
begin
  Chan1[i].Cmd := ReqE;
endrule;
endruleset;

ruleset  i : NODE do
rule "SendReqS15"
  Chan1[i].Cmd = Empty &
  Cache[i].State = I
==>
begin
  Chan1[i].Cmd := ReqS;
endrule;
endruleset;

ruleset  d : DATA; i : NODE do
rule "Store16"
  Cache[i].State = E
==>
begin
  Cache[i].Data := d;
  AuxData := d;
endrule;
endruleset;

ruleset  d : DATA do
startstate
  for i : NODE do
    Chan1[i].Cmd := Empty;
    Chan2[i].Cmd := Empty;
    Chan3[i].Cmd := Empty;
    Cache[i].State := I;
    InvSet[i] := false;
    ShrSet[i] := false;
  end;
  ExGntd := false;
  CurCmd := Empty;
  MemData := d;
  AuxData := d;
endstartstate;
endruleset;

invariant "CntrlProp"
  forall i : NODE do
    forall j : NODE do
      (i != j ->
      ((Cache[i].State = E ->
      Cache[j].State = I) &
      (Cache[i].State = S ->
      (Cache[j].State = I |
      Cache[j].State = S))))
    end
  end;

invariant "DataProp"
  ((ExGntd = false ->
  MemData = AuxData) &
  forall i : NODE do
    (Cache[i].State != I ->
    Cache[i].Data = AuxData)
  end);



-- No abstract rule for rule RecvGntE1



-- No abstract rule for rule RecvGntS2


rule "n_ABS_SendGntE3_NODE_1"

	CurCmd = ReqE &
	CurPtr = Other &
	ExGntd = false
	& forall NODE_2 : NODE do
			ShrSet[NODE_2] = false
	end
==>
begin
	ExGntd := true ;
	CurCmd := Empty;
endrule;
rule "n_ABS_SendGntS4_NODE_1"

	CurCmd = ReqS &
	CurPtr = Other &
	ExGntd = false
==>
begin
	CurCmd := Empty;
endrule;
rule "n_ABS_RecvInvAck5_NODE_1"

	CurCmd != Empty &
	ExGntd = true
 	& 
	forall NODE_2 : NODE do
		Chan3[NODE_2].Cmd = Empty &
		Chan3[NODE_2].Cmd != InvAck &
		Chan2[NODE_2].Cmd != Inv &
		Cache[NODE_2].State != E &
		Cache[NODE_2].State = I &
		Chan2[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE &
		ShrSet[NODE_2] = false &
		InvSet[NODE_2] = false
	end
==>
begin
	ExGntd := false ;
	MemData := AuxData;
endrule;

-- No abstract rule for rule RecvInvAck6



-- No abstract rule for rule SendInvAck7



-- No abstract rule for rule SendInvAck8



-- No abstract rule for rule SendInv9



-- No abstract rule for rule SendInv10


rule "n_ABS_RecvReqE11_NODE_1"

	CurCmd = Empty
==>
begin
	CurCmd := ReqE ;
	CurPtr := Other;
	for NODE_2 : NODE do
		InvSet[NODE_2] := ShrSet[NODE_2] ;
		;
	endfor;
endrule;
rule "n_ABS_RecvReqS12_NODE_1"

	CurCmd = Empty
==>
begin
	CurCmd := ReqS ;
	CurPtr := Other;
	for NODE_2 : NODE do
		InvSet[NODE_2] := ShrSet[NODE_2] ;
		;
	endfor;
endrule;

-- No abstract rule for rule SendReqE13



-- No abstract rule for rule SendReqE14



-- No abstract rule for rule SendReqS15



ruleset DATA_1 : DATA do
rule "n_ABS_Store16_NODE_1"

	forall NODE_2 : NODE do
		Chan3[NODE_2].Cmd = Empty &
		Chan3[NODE_2].Cmd != InvAck &
		Chan2[NODE_2].Cmd != Inv &
		Cache[NODE_2].State != E &
		Cache[NODE_2].State = I &
		Cache[NODE_2].State != S &
		Chan2[NODE_2].Cmd != GntS &
		Chan2[NODE_2].Cmd = Empty &
		Chan2[NODE_2].Cmd != GntE &
		ExGntd = true &
		ShrSet[NODE_2] = false &
		InvSet[NODE_2] = false
	end
==>
begin
	AuxData := DATA_1;
endrule;
endruleset;



ruleset i : NODE do
Invariant "rule_1"
	(Chan2[i].Cmd = Inv -> CurCmd != Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_2"
	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_3"
		(i != j) ->	(Cache[i].State = E -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_4"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_5"
	(Chan2[i].Cmd = GntS -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_6"
		(i != j) ->	(Cache[i].State = E -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_7"
		(i != j) ->	(Chan2[i].Cmd = GntE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_8"
	(Chan2[i].Cmd = GntE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_9"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_10"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_11"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_12"
		(i != j) ->	(CurCmd = ReqS & InvSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_13"
		(i != j) ->	(Chan2[i].Cmd = GntE -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_14"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_15"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_16"
		(i != j) ->	(Cache[i].State = E -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_17"
		(i != j) ->	(Cache[i].State = S -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_18"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_19"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_20"
		(i != j) ->	(Cache[i].State = E -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_21"
	(ExGntd = true & InvSet[i] = true -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_22"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_23"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_24"
	(Cache[i].State = S -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_25"
		(i != j) ->	(Chan3[i].Cmd = InvAck -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_26"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_27"
		(i != j) ->	(Chan3[i].Cmd = InvAck -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_28"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_29"
		(i != j) ->	(CurCmd = ReqS & InvSet[i] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_30"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_31"
		(i != j) ->	(Cache[i].State = E -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_32"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_33"
		(i != j) ->	(InvSet[i] = true -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_34"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_35"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_36"
	(Cache[i].State = E -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_37"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_38"
		(i != j) ->	(Chan2[i].Cmd = Inv -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_39"
		(i != j) ->	(CurCmd = ReqS & InvSet[i] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_40"
		(i != j) ->	(Cache[i].State = E -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_41"
		(i != j) ->	(Cache[i].State = E -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_42"
		(i != j) ->	(Cache[i].State = S -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_43"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_44"
	(Chan2[i].Cmd = GntS -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_45"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_46"
		(i != j) ->	(Cache[i].State = E -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_47"
		(i != j) ->	(InvSet[i] = true -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_48"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_49"
		(i != j) ->	(Chan2[i].Cmd = Inv -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_50"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_51"
		(i != j) ->	(Cache[i].State = E -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_52"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_53"
		(i != j) ->	(Cache[i].State = E -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_54"
	(Cache[i].State = S -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_55"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_56"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_57"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_58"
	(Chan2[i].Cmd = GntE -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_59"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_60"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_61"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_62"
		(i != j) ->	(Cache[i].State = E -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_63"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan2[j].Cmd != Inv);
endruleset;
