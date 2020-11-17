
const

  NODE_NUM : 2;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

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



ruleset i : NODE do
Invariant "rule_1196"
	(Chan2[i].Data = AuxData & InvSet[i] = false -> CurCmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1374"
		(i != j) ->	(MemData != AuxData & Cache[j].Data = AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_681"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_94"
	(ShrSet[j] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_228"
		(i != j) ->	(Cache[j].State = E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_367"
		(i != j) ->	(ShrSet[j] = true & Chan3[i].Cmd = InvAck -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_592"
	(Chan2[i].Cmd != Empty & Cache[i].State = I -> Chan2[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_223"
		(i != j) ->	(Chan2[i].Cmd = Inv -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_688"
	(MemData != AuxData & Cache[j].State != E -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_345"
		(i != j) ->	(ShrSet[j] = true & ExGntd = true -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_5"
	(Chan3[j].Data = AuxData -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1554"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_376"
	(Chan2[i].Cmd = GntS & InvSet[i] = false -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_623"
		(i != j) ->	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1097"
	(CurCmd != ReqE & ExGntd = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_363"
	(Chan3[i].Cmd != Empty & ExGntd = false -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1416"
		(i != j) ->	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1457"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_634"
		(i != j) ->	(CurCmd = ReqS & Cache[i].State != I -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_303"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1002"
		(i != j) ->	(CurCmd = ReqS & ShrSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_508"
		(i != j) ->	(InvSet[j] = true & InvSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_268"
	(CurCmd = Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1182"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Data = AuxData -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1103"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1135"
		(i != j) ->	(CurCmd = ReqS & Chan2[j].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_312"
	(Chan2[j].Cmd = Inv -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1220"
		(i != j) ->	(MemData != AuxData & Chan3[j].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_415"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1487"
		(i != j) ->	(Chan2[i].Data = AuxData & Cache[j].State != I -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_673"
		(i != j) ->	(MemData != AuxData & Chan3[j].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_342"
	(Cache[j].State != I & InvSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1445"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1030"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan3[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1336"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_285"
	(Cache[j].Data = AuxData -> ShrSet[j] = true);
endruleset;


ruleset i : NODE do
Invariant "rule_16"
	(Chan2[i].Cmd = Inv -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_1085"
	(Cache[i].State = I & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_900"
	(CurCmd != ReqS & CurCmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1482"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_660"
		(i != j) ->	(MemData != AuxData & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_29"
		(i != j) ->	(InvSet[i] = true -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1197"
		(i != j) ->	(ExGntd = true & Cache[j].State != I -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1125"
		(i != j) ->	(CurCmd != ReqE & Cache[i].State = S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_319"
	(CurCmd = Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_458"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Data = AuxData -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_509"
		(i != j) ->	(ExGntd = true & Cache[j].Data = AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_776"
		(i != j) ->	(Chan3[j].Cmd = InvAck & InvSet[i] = true -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_870"
		(i != j) ->	(Cache[j].State != I & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_147"
	(Cache[i].Data = AuxData -> Cache[i].State != I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_498"
		(i != j) ->	(ShrSet[i] = false & ExGntd = true -> ShrSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1288"
		(i != j) ->	(Cache[j].State = S & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_817"
		(i != j) ->	(Chan2[j].Cmd != Empty & InvSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_855"
		(i != j) ->	(Chan2[j].Cmd != Empty & Cache[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_639"
		(i != j) ->	(Chan2[j].Cmd != Empty & MemData != AuxData -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1565"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_284"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_1402"
	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> Chan3[j].Data = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_73"
	(Chan2[i].Data = AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_646"
	(Chan2[j].Cmd = GntS & CurCmd != Empty -> InvSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_456"
		(i != j) ->	(CurCmd = ReqS & InvSet[i] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_219"
	(Cache[j].State = S -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1271"
		(i != j) ->	(CurCmd != ReqE & Cache[i].Data = AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_314"
		(i != j) ->	(Chan2[i].Data = AuxData -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_265"
	(Cache[j].State = E -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_1263"
	(Cache[j].State != S & Cache[j].Data = AuxData -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_849"
		(i != j) ->	(InvSet[i] = true & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_287"
	(Chan3[i].Cmd = InvAck -> CurCmd != Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_198"
	(Chan3[i].Data = AuxData -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_477"
		(i != j) ->	(ExGntd = true & Cache[i].Data = AuxData -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_142"
		(i != j) ->	(Chan2[j].Cmd = Inv -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_1070"
	(CurCmd = ReqE & Chan2[i].Data = AuxData -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_347"
		(i != j) ->	(ShrSet[j] = true & ExGntd = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1367"
		(i != j) ->	(Chan2[i].Cmd = GntS & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_956"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1160"
		(i != j) ->	(Cache[j].State != I & Cache[j].State != S -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1082"
	(InvSet[j] = true & Cache[j].State != E -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_53"
	(Cache[j].State = S -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_895"
		(i != j) ->	(Chan2[i].Cmd = GntS & CurCmd = ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_215"
	(Chan3[i].Cmd = InvAck -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_1536"
	(Chan2[j].Cmd = Inv & Cache[j].State != E -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1130"
		(i != j) ->	(Cache[j].State != I & Chan3[i].Cmd = InvAck -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_495"
	(CurCmd = ReqS & Cache[i].State = S -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1254"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_295"
	(MemData != AuxData -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_87"
		(i != j) ->	(InvSet[j] = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1129"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan2[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1240"
		(i != j) ->	(Chan3[i].Cmd = InvAck & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1447"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan3[i].Cmd = InvAck -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_798"
		(i != j) ->	(Chan2[i].Cmd != Empty & MemData != AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_507"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[j].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_524"
	(CurCmd != Empty & InvSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1075"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].State != I -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_300"
	(Chan2[i].Cmd = Inv -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_928"
		(i != j) ->	(Cache[j].State != S & Cache[j].Data = AuxData -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1575"
	(Chan2[j].Cmd != Inv & Chan2[j].Cmd != Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_121"
		(i != j) ->	(Cache[i].State = E -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_166"
	(Cache[i].Data = AuxData -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_662"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_289"
	(Cache[i].State = E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_715"
		(i != j) ->	(ShrSet[i] = true & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_362"
		(i != j) ->	(ExGntd = true & Chan2[i].Data = AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_1327"
	(Chan2[i].Cmd != Empty & MemData != AuxData -> Cache[i].State != I);
endruleset;


ruleset i : NODE do
Invariant "rule_108"
	(Cache[i].State = S -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_411"
	(Chan2[j].Cmd != Empty & MemData != AuxData -> CurCmd != Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_105"
	(Chan2[i].Cmd = GntE -> Chan2[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1035"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Data = AuxData -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_288"
		(i != j) ->	(Cache[i].State = E -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1410"
		(i != j) ->	(Cache[i].State != I & MemData != AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1505"
		(i != j) ->	(CurCmd = ReqS & Cache[i].State = S -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_1095"
	(CurCmd != ReqE & Cache[j].State != E -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_856"
		(i != j) ->	(Cache[j].State != S & InvSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_719"
		(i != j) ->	(InvSet[j] = false & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_939"
		(i != j) ->	(ShrSet[j] = true & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_659"
		(i != j) ->	(Chan2[j].Cmd != Empty & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_825"
		(i != j) ->	(Chan2[j].Cmd = GntS & CurCmd != ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1116"
		(i != j) ->	(Chan2[j].Cmd = GntS & CurCmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_141"
	(InvSet[j] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1531"
		(i != j) ->	(Chan2[i].Data = AuxData & CurCmd != ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_562"
		(i != j) ->	(Chan2[i].Cmd = GntS & Cache[j].State != S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_424"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1495"
		(i != j) ->	(ShrSet[j] = true & CurCmd != ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1010"
		(i != j) ->	(Cache[i].State != I & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_323"
		(i != j) ->	(Cache[i].State = E -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_744"
	(MemData != AuxData & Chan3[j].Cmd != Empty -> Chan3[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_393"
		(i != j) ->	(Cache[i].State != S & Cache[i].State != I -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_833"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1003"
		(i != j) ->	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1235"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd != Empty -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_519"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[i].State != S -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_550"
		(i != j) ->	(Chan2[i].Cmd != Empty & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1561"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[j].State != S -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_1281"
	(InvSet[i] = true & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1556"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_897"
		(i != j) ->	(ExGntd = true & Chan2[i].Data = AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1176"
	(Chan2[i].Cmd != Empty & MemData != AuxData -> Cache[i].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1310"
		(i != j) ->	(Chan2[i].Cmd != Empty & ExGntd = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1119"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1060"
		(i != j) ->	(Chan2[j].Cmd = GntS & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset i : NODE do
Invariant "rule_529"
	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_133"
	(Chan3[i].Cmd = InvAck -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1392"
		(i != j) ->	(Cache[j].State != I & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1120"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[i].State != S -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1158"
		(i != j) ->	(Cache[j].State != I & Cache[j].State != S -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_959"
	(Chan2[j].Cmd = GntS & InvSet[j] = false -> CurCmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_617"
	(ExGntd = true & InvSet[i] = true -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_523"
		(i != j) ->	(ShrSet[j] = true & Chan2[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1494"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[j].Cmd != Empty -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_390"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_539"
		(i != j) ->	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_997"
	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_25"
	(Chan3[j].Cmd != Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_125"
	(Chan2[i].Data = AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_736"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_802"
	(Chan2[i].Data = AuxData & Cache[i].State != I -> InvSet[i] = true);
endruleset;


ruleset i : NODE do
Invariant "rule_1143"
	(Cache[i].State != I & InvSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_989"
		(i != j) ->	(Cache[j].State != I & CurCmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_728"
		(i != j) ->	(Chan3[j].Cmd = InvAck & MemData != AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1537"
		(i != j) ->	(MemData != AuxData & Chan3[j].Cmd != Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_44"
		(i != j) ->	(Chan3[j].Data = AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_39"
		(i != j) ->	(Chan3[j].Cmd = InvAck -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_1261"
	(Chan2[i].Cmd != Empty & Chan2[i].Cmd != Inv -> Chan2[i].Data = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_1065"
	(CurCmd = ReqS & InvSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1448"
		(i != j) ->	(ExGntd = true & Chan2[i].Cmd = Inv -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_173"
	(Chan3[j].Cmd != Empty -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1282"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[j].Data = AuxData -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_55"
		(i != j) ->	(Cache[i].State = E -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1239"
		(i != j) ->	(Chan3[j].Cmd = InvAck & InvSet[i] = true -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_1427"
	(InvSet[j] = true & CurCmd = Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_464"
		(i != j) ->	(Chan3[i].Cmd = InvAck & MemData != AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_72"
	(Chan2[i].Cmd = GntS -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_403"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_722"
	(CurCmd = ReqS & Cache[i].State = S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_651"
	(CurCmd = Empty & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_863"
		(i != j) ->	(InvSet[j] = true & InvSet[i] = true -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_612"
		(i != j) ->	(InvSet[j] = true & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_654"
		(i != j) ->	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_1165"
	(Cache[j].State != I & Cache[j].State != E -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_272"
		(i != j) ->	(Cache[j].State = E -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1493"
		(i != j) ->	(CurCmd != ReqE & Cache[j].State = S -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_232"
	(Cache[i].State = E -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_170"
		(i != j) ->	(Chan3[i].Data = AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_910"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_827"
		(i != j) ->	(Chan2[j].Cmd != Empty & InvSet[i] = true -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1352"
	(Chan2[i].Data = AuxData & Cache[i].State != I -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1569"
		(i != j) ->	(Chan2[j].Cmd = GntS & CurCmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_547"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_1421"
	(Cache[i].Data = AuxData & Cache[i].State != S -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_1272"
	(InvSet[j] = false & Chan2[j].Cmd = GntE -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_299"
	(Chan2[i].Cmd = GntE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_483"
	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1440"
		(i != j) ->	(Cache[j].State != I & Cache[j].State != S -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_395"
	(ExGntd = true & CurCmd = Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1025"
	(Cache[i].Data = AuxData & Cache[i].State != S -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_621"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[j].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_632"
		(i != j) ->	(Cache[i].State != I & MemData != AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_216"
		(i != j) ->	(Cache[j].State = E -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_478"
		(i != j) ->	(ShrSet[j] = true & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_297"
	(Cache[j].State = S -> Cache[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_912"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_558"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_235"
	(Chan3[j].Cmd = InvAck -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1305"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1020"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd = InvAck -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_27"
	(Cache[i].Data = AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_1292"
	(Chan3[i].Cmd = InvAck & MemData != AuxData -> Chan3[i].Data = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_43"
	(Chan3[j].Data = AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1510"
		(i != j) ->	(ExGntd = true & Chan2[j].Cmd != Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_737"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[i].State != S -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_794"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[i].State != S -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_212"
	(Chan2[i].Cmd = GntE -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_961"
		(i != j) ->	(Chan2[i].Cmd != Empty & InvSet[j] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1047"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1224"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1503"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_720"
		(i != j) ->	(CurCmd = ReqS & Cache[j].Data = AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_563"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].State = S -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_696"
		(i != j) ->	(Chan2[i].Cmd != Empty & ExGntd = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_647"
		(i != j) ->	(ExGntd = true & Chan2[i].Cmd = Inv -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_730"
		(i != j) ->	(ExGntd = true & Cache[j].State != I -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_261"
	(ShrSet[j] = false -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1361"
		(i != j) ->	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_184"
	(ShrSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_998"
		(i != j) ->	(ShrSet[j] = true & ShrSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_741"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_229"
		(i != j) ->	(Chan3[j].Data = AuxData -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_599"
		(i != j) ->	(Cache[j].State != I & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_613"
	(Chan2[i].Cmd = GntS & InvSet[i] = false -> CurCmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1371"
		(i != j) ->	(Chan2[i].Cmd = GntS & InvSet[i] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_1170"
	(Chan2[j].Cmd = GntE & InvSet[j] = true -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_537"
		(i != j) ->	(Chan2[j].Cmd = GntS & Chan2[i].Cmd = Inv -> InvSet[j] = true);
endruleset;


ruleset i : NODE do
Invariant "rule_1032"
	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_14"
	(Chan3[j].Cmd = InvAck -> ShrSet[j] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_1521"
	(CurCmd != ReqE & Cache[j].State = S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_511"
		(i != j) ->	(Cache[j].State != I & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_916"
	(Chan2[i].Cmd != Empty & MemData != AuxData -> Cache[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_357"
		(i != j) ->	(Chan3[i].Cmd != Empty & ExGntd = true -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_986"
		(i != j) ->	(ExGntd = true & Chan2[j].Cmd != Empty -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_683"
		(i != j) ->	(InvSet[j] = true & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_441"
		(i != j) ->	(ExGntd = true & InvSet[j] = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_548"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Chan3[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_560"
		(i != j) ->	(Chan2[i].Cmd != Empty & InvSet[j] = true -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1276"
		(i != j) ->	(InvSet[j] = true & Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1432"
	(Chan3[i].Cmd != Empty & ExGntd = false -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_485"
		(i != j) ->	(ExGntd = true & InvSet[j] = true -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_786"
		(i != j) ->	(CurCmd != ReqE & Cache[j].Data = AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_175"
	(Chan3[i].Cmd != Empty -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_666"
	(InvSet[j] = false & Chan2[j].Cmd = GntE -> CurCmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_210"
		(i != j) ->	(Chan3[i].Data = AuxData -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_814"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1018"
		(i != j) ->	(CurCmd != ReqE & Cache[j].State = S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_48"
	(Chan2[j].Cmd = GntE -> ShrSet[j] = true);
endruleset;


ruleset i : NODE do
Invariant "rule_197"
	(ShrSet[i] = false -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_789"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_156"
		(i != j) ->	(Chan3[i].Data = AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_266"
	(Cache[j].State != I -> Cache[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1456"
		(i != j) ->	(CurCmd != ReqE & Cache[i].Data = AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1091"
		(i != j) ->	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1227"
		(i != j) ->	(CurCmd != ReqE & InvSet[j] = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1071"
	(Cache[i].State != E & CurCmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_811"
		(i != j) ->	(ExGntd = true & Chan2[i].Cmd = Inv -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_455"
	(InvSet[j] = false & CurCmd != Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_885"
	(CurCmd = ReqS & InvSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_1223"
	(Cache[i].State != S & Cache[i].State != I -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_447"
		(i != j) ->	(Chan2[j].Cmd = Inv & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_255"
	(Chan3[j].Data = AuxData -> Chan3[j].Cmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_658"
		(i != j) ->	(Cache[j].State != S & Cache[j].Data = AuxData -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_400"
		(i != j) ->	(ShrSet[i] = true & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1023"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].State = S -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_624"
	(Chan2[i].Data = AuxData & Cache[i].State = S -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1558"
		(i != j) ->	(CurCmd != ReqE & Chan2[j].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1106"
	(Chan2[i].Cmd = GntS & InvSet[i] = false -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_919"
	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> Cache[i].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1394"
		(i != j) ->	(ShrSet[i] = true & Cache[j].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_315"
	(Chan3[j].Data = AuxData -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_824"
	(Cache[j].State != S & ExGntd = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_602"
		(i != j) ->	(ShrSet[j] = true & MemData != AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1474"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_541"
		(i != j) ->	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1275"
		(i != j) ->	(Chan2[i].Cmd = GntS & Chan3[j].Cmd = InvAck -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_1039"
	(Chan2[j].Cmd = Inv & ExGntd = true -> Cache[j].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1354"
		(i != j) ->	(CurCmd = ReqS & Cache[j].State = S -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_475"
		(i != j) ->	(ShrSet[j] = true & InvSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_656"
	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> ExGntd = true);
endruleset;


ruleset i : NODE do
Invariant "rule_174"
	(ExGntd = true -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_732"
		(i != j) ->	(Chan2[j].Cmd = Inv & ShrSet[i] = true -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1164"
	(Chan2[i].Data = AuxData & InvSet[i] = false -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1189"
		(i != j) ->	(Cache[j].State != I & Cache[i].State != I -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_322"
		(i != j) ->	(Chan3[i].Cmd != Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_42"
	(Chan3[j].Cmd = InvAck -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1435"
	(Chan2[j].Cmd != Empty & MemData != AuxData -> Cache[j].State != I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1099"
		(i != j) ->	(Chan3[i].Cmd = InvAck & MemData != AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_525"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_503"
	(Chan2[i].Data = AuxData & InvSet[i] = false -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_1446"
	(Chan2[i].Cmd != Empty & Cache[i].State = I -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_1000"
	(CurCmd = Empty & Cache[j].State = E -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1451"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1050"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan3[j].Cmd = InvAck -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_749"
	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1287"
		(i != j) ->	(Chan3[j].Cmd != Empty & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_313"
	(Cache[j].Data = AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1450"
		(i != j) ->	(Chan2[j].Cmd = GntS & CurCmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_729"
		(i != j) ->	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_158"
		(i != j) ->	(Cache[j].State != I -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_801"
	(Cache[j].State = S & InvSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_67"
	(Chan2[j].Cmd = Inv -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_591"
	(CurCmd = ReqS & InvSet[i] = false -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_927"
		(i != j) ->	(ShrSet[i] = false & MemData != AuxData -> ShrSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1178"
		(i != j) ->	(Chan2[j].Cmd = GntS & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_795"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_420"
	(CurCmd = ReqS & InvSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_1169"
	(CurCmd != Empty & Chan2[j].Cmd = GntE -> InvSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_398"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_103"
	(Chan3[i].Data = AuxData -> Chan3[i].Cmd = InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_167"
		(i != j) ->	(Chan3[j].Cmd != Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_346"
		(i != j) ->	(ExGntd = true & Chan2[j].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_803"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_838"
		(i != j) ->	(Chan3[i].Cmd = InvAck & InvSet[j] = true -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_1540"
	(Chan2[j].Cmd = Inv & Cache[j].State != E -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_747"
		(i != j) ->	(Cache[i].Data = AuxData & MemData != AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1063"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_358"
	(InvSet[i] = true & CurCmd = Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_559"
		(i != j) ->	(ShrSet[j] = true & MemData != AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_333"
	(Cache[i].State = E -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_280"
	(Cache[i].State = S -> Cache[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_452"
		(i != j) ->	(InvSet[j] = true & MemData != AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_47"
	(Chan3[j].Cmd = InvAck -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1214"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1042"
		(i != j) ->	(Cache[i].State != I & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_994"
		(i != j) ->	(MemData != AuxData & Cache[j].Data = AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_318"
		(i != j) ->	(Chan3[j].Data = AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1479"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_466"
		(i != j) ->	(InvSet[j] = true & MemData != AuxData -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_368"
		(i != j) ->	(Chan2[i].Cmd != Empty & MemData != AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_352"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_422"
	(Chan2[i].Cmd = GntS & Cache[i].State = S -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_152"
		(i != j) ->	(Chan2[j].Cmd = GntS -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1207"
		(i != j) ->	(CurCmd != ReqE & ShrSet[i] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_26"
	(Chan3[j].Data = AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1518"
		(i != j) ->	(MemData != AuxData & Chan2[i].Cmd = Inv -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1497"
		(i != j) ->	(ExGntd = true & Cache[j].Data = AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_1330"
	(Chan2[i].Cmd != Empty & InvSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_1113"
	(CurCmd != ReqS & CurCmd != ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_899"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[j].State != S -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_81"
	(Chan2[j].Cmd != Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_23"
	(Chan3[i].Cmd != Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_343"
		(i != j) ->	(Cache[j].State != I & InvSet[i] = true -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1262"
	(Chan2[j].Cmd = GntS & Cache[j].Data = AuxData -> InvSet[j] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_35"
	(Cache[j].State = E -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_163"
	(Chan3[i].Cmd != Empty -> Chan2[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_50"
	(Cache[j].State = S -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_680"
		(i != j) ->	(Chan3[i].Cmd != Empty & InvSet[j] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1541"
		(i != j) ->	(Cache[i].State != S & Cache[i].State != I -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1005"
		(i != j) ->	(MemData != AuxData & Cache[j].Data = AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1256"
		(i != j) ->	(CurCmd = ReqS & Cache[j].Data = AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_853"
		(i != j) ->	(Chan2[j].Cmd != Empty & MemData != AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_938"
		(i != j) ->	(Cache[j].State != I & MemData != AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_709"
	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> Chan3[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1246"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Chan2[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_669"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_573"
	(ExGntd = false & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_66"
		(i != j) ->	(Chan3[j].Data = AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_714"
		(i != j) ->	(MemData != AuxData & Cache[j].Data = AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_712"
		(i != j) ->	(ShrSet[j] = true & Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_848"
		(i != j) ->	(MemData != AuxData & Chan3[j].Cmd != Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_740"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_104"
	(Cache[i].State = E -> Cache[i].Data = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_324"
	(Chan3[i].Data = AuxData -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_777"
		(i != j) ->	(Chan2[j].Cmd = Inv & InvSet[i] = true -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_629"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan3[i].Cmd = InvAck -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_1215"
	(InvSet[j] = true & CurCmd = Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_908"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1177"
		(i != j) ->	(Cache[i].State != I & Chan3[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1366"
		(i != j) ->	(InvSet[i] = true & MemData != AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_760"
		(i != j) ->	(Cache[j].State != I & Cache[i].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1209"
		(i != j) ->	(ShrSet[i] = true & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_530"
		(i != j) ->	(ShrSet[j] = true & Chan2[i].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_85"
	(Cache[j].State != I -> ShrSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1154"
		(i != j) ->	(Cache[j].State != S & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_329"
	(CurCmd = Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_610"
		(i != j) ->	(ExGntd = true & Cache[i].Data = AuxData -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1004"
	(CurCmd = ReqS & Cache[j].State != E -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1443"
		(i != j) ->	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_371"
		(i != j) ->	(ExGntd = true & InvSet[j] = true -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_615"
		(i != j) ->	(MemData != AuxData & Chan2[i].Cmd = Inv -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_263"
		(i != j) ->	(Chan2[i].Data = AuxData -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1341"
		(i != j) ->	(ShrSet[j] = true & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1475"
		(i != j) ->	(Cache[i].State != S & Chan2[i].Cmd = Inv -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_140"
	(ShrSet[i] = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_576"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd != Empty -> Cache[j].State = S);
endruleset;


ruleset i : NODE do
Invariant "rule_1203"
	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_419"
		(i != j) ->	(ShrSet[j] = true & Chan3[i].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1192"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_202"
	(Cache[j].State != I -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_9"
	(Chan2[j].Cmd = GntS -> ShrSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1496"
		(i != j) ->	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_695"
		(i != j) ->	(InvSet[j] = true & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_107"
	(Chan3[j].Cmd = InvAck -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_957"
	(Chan2[j].Cmd = GntS & Cache[j].State = S -> InvSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1014"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1321"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1413"
		(i != j) ->	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1296"
		(i != j) ->	(Cache[i].State != S & Chan2[i].Cmd = Inv -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_138"
	(Chan3[j].Cmd != Empty -> CurCmd != Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_177"
	(Chan3[j].Data = AuxData -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_837"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[j].Data = AuxData -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_528"
	(Cache[i].State != E & Cache[i].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_792"
	(CurCmd != ReqE & ExGntd = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_122"
	(Chan3[j].Data = AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1481"
		(i != j) ->	(Chan3[i].Cmd = InvAck & MemData != AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1578"
		(i != j) ->	(Cache[i].State = S & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1516"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1048"
		(i != j) ->	(Chan2[i].Data = AuxData & InvSet[i] = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1426"
		(i != j) ->	(InvSet[i] = true & MemData != AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1551"
		(i != j) ->	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1442"
		(i != j) ->	(Cache[j].State != I & Cache[j].State != S -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_975"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1335"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan3[j].Cmd != Empty -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_389"
		(i != j) ->	(ShrSet[j] = true & ExGntd = true -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1430"
		(i != j) ->	(Cache[j].State != I & CurCmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_866"
	(Cache[i].State = I & InvSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_836"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_76"
	(Cache[j].State = S -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1104"
		(i != j) ->	(CurCmd = ReqS & Cache[j].Data = AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_738"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Data = AuxData -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_311"
	(Chan2[i].Cmd = GntS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_321"
		(i != j) ->	(Chan3[i].Data = AuxData -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_951"
		(i != j) ->	(ExGntd = true & Chan2[i].Data = AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_1490"
	(Cache[i].State = I & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_162"
	(Chan3[i].Cmd != Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_109"
	(Chan2[i].Cmd = GntS -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_292"
		(i != j) ->	(Cache[i].State = E -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_702"
		(i != j) ->	(Chan2[j].Cmd = Inv & MemData != AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1056"
		(i != j) ->	(ShrSet[i] = true & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1238"
		(i != j) ->	(CurCmd = ReqS & InvSet[j] = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_821"
		(i != j) ->	(ExGntd = true & Cache[j].State != I -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_204"
	(Chan2[i].Cmd = Inv -> Cache[i].State != I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_764"
		(i != j) ->	(Chan2[j].Cmd = Inv & ExGntd = true -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_766"
		(i != j) ->	(Chan2[j].Cmd = Inv & ShrSet[i] = true -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_950"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_690"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd = InvAck -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_553"
		(i != j) ->	(CurCmd = ReqS & InvSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1485"
		(i != j) ->	(InvSet[i] = true & MemData != AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1218"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].Data = AuxData -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1141"
		(i != j) ->	(Chan3[j].Cmd = InvAck & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1332"
		(i != j) ->	(Cache[i].State != S & Cache[i].State != I -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1073"
		(i != j) ->	(Cache[i].Data = AuxData & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_1109"
	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> Chan3[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1567"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].State != I -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_862"
	(Cache[i].State = I & InvSet[i] = true -> Chan2[i].Cmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_440"
		(i != j) ->	(Chan2[i].Data = AuxData & Cache[j].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_196"
		(i != j) ->	(Chan2[j].Cmd = GntE -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_682"
		(i != j) ->	(Chan3[j].Cmd = InvAck & ShrSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1186"
		(i != j) ->	(ExGntd = true & ShrSet[i] = true -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_756"
	(Chan2[i].Cmd = Empty & Cache[i].State = I -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1221"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[j].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_18"
	(InvSet[j] = true -> ShrSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_717"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_755"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan2[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_150"
	(Chan3[j].Cmd = InvAck -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_110"
	(MemData != AuxData -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_161"
	(Cache[i].State != I -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1244"
		(i != j) ->	(Cache[i].State != S & Cache[i].State != I -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_304"
		(i != j) ->	(Cache[i].State = E -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1124"
		(i != j) ->	(Chan2[j].Cmd != Empty & Cache[i].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1478"
		(i != j) ->	(Cache[j].State != I & CurCmd != ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1283"
		(i != j) ->	(Chan2[j].Cmd != Empty & MemData != AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_139"
		(i != j) ->	(Cache[j].State = E -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_948"
		(i != j) ->	(InvSet[i] = true & Chan3[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_759"
		(i != j) ->	(ShrSet[i] = true & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1111"
		(i != j) ->	(Chan2[j].Cmd = Inv & InvSet[i] = true -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_743"
		(i != j) ->	(Chan2[j].Cmd = Inv & ExGntd = true -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_74"
		(i != j) ->	(Cache[j].State = S -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1008"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[i].State != S -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_911"
		(i != j) ->	(Chan2[j].Cmd = GntS & Chan3[i].Cmd = InvAck -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1126"
		(i != j) ->	(Chan2[i].Cmd != Empty & MemData != AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1582"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_516"
	(InvSet[i] = true & Cache[i].State = E -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1260"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan3[j].Cmd = InvAck -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_392"
		(i != j) ->	(Cache[j].State != S & ShrSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_454"
		(i != j) ->	(ShrSet[j] = true & CurCmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_930"
		(i != j) ->	(ExGntd = true & Chan2[i].Data = AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1138"
		(i != j) ->	(Cache[i].State != S & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_609"
		(i != j) ->	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_751"
		(i != j) ->	(Chan2[j].Cmd = Inv & ExGntd = true -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1546"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_545"
	(CurCmd = ReqE & InvSet[j] = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_607"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan2[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_762"
	(Cache[i].State = S & InvSet[i] = false -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_472"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Data = AuxData -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1253"
		(i != j) ->	(Cache[j].State != I & Chan3[i].Cmd = InvAck -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_1433"
	(Chan2[j].Cmd = Inv & ExGntd = false -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1458"
		(i != j) ->	(Cache[j].State != S & Cache[j].Data = AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_1364"
	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1391"
		(i != j) ->	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1462"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_251"
	(Chan2[j].Cmd = GntS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_981"
		(i != j) ->	(MemData != AuxData & Chan3[j].Cmd != Empty -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1088"
		(i != j) ->	(Chan3[j].Cmd = InvAck & ExGntd = true -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_830"
	(Chan2[i].Data = AuxData & InvSet[i] = false -> CurCmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_684"
		(i != j) ->	(Cache[j].State != I & Chan3[i].Cmd = InvAck -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_52"
	(CurCmd = Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_377"
	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1346"
		(i != j) ->	(Chan2[i].Data = AuxData & CurCmd != ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_935"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_1572"
	(Chan2[j].Cmd = GntS & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1185"
		(i != j) ->	(Chan2[i].Cmd = GntS & InvSet[i] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_864"
		(i != j) ->	(CurCmd = ReqS & Cache[i].Data = AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1270"
	(InvSet[i] = true & MemData != AuxData -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_889"
		(i != j) ->	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_113"
	(Chan3[j].Cmd != Empty -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_260"
	(ExGntd = false -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_839"
	(ExGntd = false & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1267"
		(i != j) ->	(Cache[j].State != S & Cache[j].Data = AuxData -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_847"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_858"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].State != S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_396"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_209"
	(ExGntd = false -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_1434"
	(Cache[i].State != E & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1066"
		(i != j) ->	(CurCmd != ReqE & Cache[j].Data = AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_1211"
	(CurCmd = ReqS & Cache[j].State = S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1526"
		(i != j) ->	(Chan2[i].Cmd != Empty & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_399"
	(InvSet[j] = true & MemData != AuxData -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_846"
		(i != j) ->	(Cache[i].Data = AuxData & MemData != AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_995"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].Data = AuxData -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_3"
	(ShrSet[j] = false -> Cache[j].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_1118"
	(Chan2[i].Data = AuxData & Cache[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_586"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_115"
	(Chan3[j].Cmd != Empty -> ShrSet[j] = true);
endruleset;


ruleset i : NODE do
Invariant "rule_878"
	(Cache[i].State = S & InvSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1439"
		(i != j) ->	(Cache[i].State != I & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1393"
	(Chan2[j].Cmd = Inv & Cache[j].State != E -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1405"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[j].State != S -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_34"
	(InvSet[i] = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1559"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1404"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[j].State != S -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_926"
		(i != j) ->	(ShrSet[j] = true & MemData != AuxData -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1384"
		(i != j) ->	(Cache[j].State != S & Cache[i].Data = AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_330"
	(Cache[i].State = S -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_1022"
	(CurCmd != ReqS & CurCmd != ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1195"
		(i != j) ->	(Cache[j].State = S & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1212"
		(i != j) ->	(Cache[i].Data = AuxData & Chan3[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_59"
	(Chan3[j].Data = AuxData -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1512"
		(i != j) ->	(Cache[j].State != I & CurCmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_518"
		(i != j) ->	(Chan3[i].Cmd != Empty & ExGntd = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_381"
		(i != j) ->	(ExGntd = true & Chan2[i].Data = AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_892"
	(Chan3[j].Cmd = InvAck & MemData != AuxData -> Chan3[j].Data = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_1325"
	(Chan2[i].Data = AuxData & Cache[i].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_582"
		(i != j) ->	(Cache[i].State = S & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_667"
	(Chan2[j].Cmd = GntE & CurCmd = Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_708"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd != Empty -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_671"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_893"
	(CurCmd = ReqS & ExGntd = false -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1068"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1460"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[j].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_571"
		(i != j) ->	(CurCmd = ReqS & ShrSet[i] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_335"
	(Chan3[i].Data = AuxData -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1431"
		(i != j) ->	(Chan3[i].Cmd = InvAck & MemData != AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_992"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd = InvAck -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_767"
		(i != j) ->	(Chan2[j].Cmd = GntS & Chan3[i].Cmd = InvAck -> InvSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1096"
		(i != j) ->	(Chan3[i].Cmd != Empty & MemData != AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_694"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = GntS -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_378"
		(i != j) ->	(ShrSet[j] = true & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_522"
		(i != j) ->	(ShrSet[j] = true & ExGntd = true -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_97"
	(Chan3[i].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_698"
		(i != j) ->	(Chan3[j].Cmd = InvAck & MemData != AuxData -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1377"
	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> ExGntd = true);
endruleset;


ruleset i : NODE do
Invariant "rule_823"
	(CurCmd = ReqS & ExGntd = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_934"
		(i != j) ->	(Chan2[j].Cmd = Inv & InvSet[i] = true -> Cache[j].State = S);
endruleset;


ruleset i : NODE do
Invariant "rule_190"
	(Chan3[i].Data = AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_145"
	(Chan2[j].Cmd = Inv -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1102"
		(i != j) ->	(Cache[j].State != I & Cache[j].State != S -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_1370"
	(Chan2[i].Cmd = GntS & CurCmd != Empty -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1585"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan2[j].Cmd = GntS -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_227"
	(Chan3[i].Cmd != Empty -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1089"
		(i != j) ->	(ExGntd = true & InvSet[j] = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_707"
		(i != j) ->	(ExGntd = true & InvSet[j] = true -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_211"
	(Chan2[j].Cmd = GntE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_448"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan3[i].Cmd = InvAck -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_355"
	(CurCmd = ReqS & ExGntd = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1454"
	(Chan2[i].Data = AuxData & Cache[i].Data = AuxData -> InvSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_183"
	(Chan2[j].Cmd = GntE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1339"
		(i != j) ->	(Chan3[i].Cmd != Empty & MemData != AuxData -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_982"
	(Chan3[i].Cmd != Empty & MemData != AuxData -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1013"
		(i != j) ->	(ExGntd = true & Cache[i].Data = AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1506"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd = InvAck -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1232"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_1480"
	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1555"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Data = AuxData -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_179"
		(i != j) ->	(Cache[i].State != I -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_117"
		(i != j) ->	(Cache[j].State = E -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1583"
		(i != j) ->	(CurCmd != ReqE & Cache[i].State != I -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_77"
		(i != j) ->	(Cache[j].Data = AuxData -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_691"
		(i != j) ->	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1286"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Chan2[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_915"
	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_648"
		(i != j) ->	(Cache[i].State != I & Chan3[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1517"
	(CurCmd != ReqS & CurCmd != ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_807"
	(Cache[j].Data = AuxData & Cache[j].State != E -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_725"
		(i != j) ->	(Chan3[i].Cmd = InvAck & InvSet[j] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_296"
	(Cache[i].State = E -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_857"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_566"
		(i != j) ->	(MemData != AuxData & Chan3[j].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_154"
	(Chan2[i].Cmd = GntS -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_248"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_382"
	(Cache[i].Data = AuxData & InvSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1083"
		(i != j) ->	(ShrSet[j] = true & Chan3[i].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_111"
	(Chan3[j].Cmd != Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_112"
		(i != j) ->	(InvSet[i] = true -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_446"
		(i != j) ->	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_28"
		(i != j) ->	(ShrSet[i] = true -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1453"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[i].State != S -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1580"
		(i != j) ->	(Chan2[i].Cmd != Empty & Cache[j].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1488"
		(i != j) ->	(CurCmd != ReqE & Cache[i].Data = AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_896"
	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1533"
		(i != j) ->	(Chan3[j].Cmd = InvAck & InvSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_401"
		(i != j) ->	(ShrSet[i] = false & ShrSet[j] = false -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_351"
		(i != j) ->	(CurCmd != ReqE & InvSet[i] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_649"
		(i != j) ->	(InvSet[j] = true & ShrSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_64"
	(ExGntd = true -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_570"
	(InvSet[i] = true & MemData != AuxData -> Cache[i].Data = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_444"
	(InvSet[j] = true & Chan2[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_546"
	(InvSet[i] = true & MemData != AuxData -> Cache[i].State != I);
endruleset;


ruleset j : NODE do
Invariant "rule_286"
	(Chan3[j].Cmd != Empty -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_902"
		(i != j) ->	(Chan3[j].Cmd = InvAck & ShrSet[i] = true -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_128"
		(i != j) ->	(Cache[j].State = E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1024"
		(i != j) ->	(InvSet[i] = true & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_332"
		(i != j) ->	(Chan2[j].Cmd = GntE -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_1289"
	(MemData != AuxData & Cache[j].State != E -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1469"
	(Chan2[i].Cmd != Empty & Cache[i].State = E -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_54"
	(Chan2[i].Data = AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_130"
	(Chan2[i].Cmd = Inv -> Cache[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_942"
		(i != j) ->	(InvSet[j] = true & Cache[i].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_126"
	(Cache[i].State = E -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1046"
		(i != j) ->	(Cache[j].State != I & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_281"
		(i != j) ->	(Chan3[i].Data = AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_595"
		(i != j) ->	(Chan2[j].Cmd = GntS & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_429"
	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1356"
		(i != j) ->	(Chan3[i].Cmd != Empty & MemData != AuxData -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_575"
	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> Cache[j].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1131"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Cache[j].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1302"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_1205"
	(CurCmd = Empty & Cache[j].State = E -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_82"
		(i != j) ->	(Chan3[i].Data = AuxData -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_692"
		(i != j) ->	(ExGntd = true & ShrSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_309"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_976"
		(i != j) ->	(CurCmd = ReqS & InvSet[i] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_336"
	(Chan3[i].Cmd != Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_822"
		(i != j) ->	(Chan2[i].Data = AuxData & Cache[j].State = S -> Chan2[i].Cmd = GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_95"
	(ShrSet[j] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1425"
		(i != j) ->	(Cache[j].State != I & MemData != AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_490"
		(i != j) ->	(ShrSet[j] = true & Cache[i].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_579"
		(i != j) ->	(InvSet[j] = true & Cache[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1248"
	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_971"
		(i != j) ->	(Cache[j].State != I & Chan3[i].Cmd = InvAck -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_502"
		(i != j) ->	(Chan2[j].Cmd != Empty & ShrSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1144"
		(i != j) ->	(Chan2[j].Cmd = Inv & MemData != AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_1219"
	(Chan3[j].Cmd = InvAck & ExGntd = true -> Chan3[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_672"
		(i != j) ->	(Chan2[i].Cmd != Empty & ExGntd = true -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1064"
		(i != j) ->	(Chan2[j].Cmd != Empty & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_923"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_488"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Cache[j].Data = AuxData -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1139"
		(i != j) ->	(CurCmd != ReqE & InvSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_298"
	(Cache[j].State != I -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1461"
		(i != j) ->	(Chan2[j].Cmd = Inv & MemData != AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1093"
		(i != j) ->	(CurCmd = ReqS & Chan2[j].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_1044"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_224"
	(Chan3[i].Data = AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1052"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan2[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1345"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1117"
		(i != j) ->	(MemData != AuxData & Chan3[j].Cmd != Empty -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_33"
		(i != j) ->	(Chan3[i].Cmd = InvAck -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_192"
		(i != j) ->	(Chan2[j].Cmd = GntE -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_704"
		(i != j) ->	(Chan2[j].Cmd = GntS & CurCmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_237"
		(i != j) ->	(Cache[i].State != I -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_538"
		(i != j) ->	(Chan3[i].Cmd != Empty & InvSet[j] = true -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_787"
		(i != j) ->	(Chan2[i].Data = AuxData & InvSet[j] = true -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_302"
		(i != j) ->	(Chan2[j].Cmd = GntE -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_1105"
	(Chan2[i].Cmd != Empty & InvSet[i] = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_890"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1123"
		(i != j) ->	(Chan3[j].Cmd = InvAck & InvSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_810"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_214"
	(Cache[j].State = E -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_852"
		(i != j) ->	(CurCmd != ReqE & Cache[j].Data = AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_467"
		(i != j) ->	(Chan2[j].Cmd != Empty & Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1473"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[i].State != S -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_93"
	(Chan2[i].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_294"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1360"
		(i != j) ->	(Cache[j].State = S & Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_703"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1553"
		(i != j) ->	(ExGntd = true & Cache[i].State != I -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_542"
		(i != j) ->	(MemData != AuxData & Cache[j].Data = AuxData -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1467"
		(i != j) ->	(Cache[j].State != I & Cache[j].State != S -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_120"
	(Cache[j].State != I -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_408"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1249"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_283"
	(Chan3[i].Cmd = InvAck -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_1171"
	(Chan3[j].Cmd = InvAck & ExGntd = false -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_155"
	(Chan3[j].Data = AuxData -> ExGntd = true);
endruleset;


ruleset i : NODE do
Invariant "rule_500"
	(Chan2[i].Data = AuxData & Cache[i].Data = AuxData -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_484"
	(Chan2[i].Cmd = Empty & InvSet[i] = true -> Cache[i].State != I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1180"
		(i != j) ->	(Cache[j].State != S & Cache[i].State = S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_1098"
	(InvSet[j] = true & MemData != AuxData -> Cache[j].State != I);
endruleset;


ruleset j : NODE do
Invariant "rule_275"
	(Chan3[j].Data = AuxData -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_625"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[j].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_20"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_534"
	(InvSet[j] = true & MemData != AuxData -> Cache[j].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1471"
		(i != j) ->	(Cache[i].State != I & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1449"
		(i != j) ->	(ExGntd = true & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_875"
		(i != j) ->	(Chan2[i].Data = AuxData & InvSet[j] = true -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_60"
	(InvSet[i] = true -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_118"
		(i != j) ->	(Cache[i].Data = AuxData -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1067"
		(i != j) ->	(Chan2[i].Cmd != Empty & Cache[j].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_83"
	(Cache[i].State = I -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_341"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].State != I -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_208"
	(Chan2[i].Cmd = Inv -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_181"
	(Chan2[i].Cmd = GntE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_1184"
	(InvSet[j] = true & Cache[j].State = E -> CurCmd != Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1136"
	(CurCmd != ReqE & ExGntd = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_873"
		(i != j) ->	(ShrSet[j] = true & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_844"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[j].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1542"
		(i != j) ->	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1243"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_337"
	(Chan3[i].Cmd = InvAck -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_865"
		(i != j) ->	(Cache[j].State != I & Cache[i].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1252"
		(i != j) ->	(CurCmd != ReqE & Chan2[j].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_434"
		(i != j) ->	(Chan2[j].Cmd = GntS & InvSet[j] = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_1415"
	(Chan2[i].Data = AuxData & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_879"
		(i != j) ->	(Chan2[j].Cmd != Empty & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_752"
	(Chan2[j].Cmd = Inv & Cache[j].State != S -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_835"
		(i != j) ->	(Chan3[j].Cmd = InvAck & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1101"
		(i != j) ->	(ShrSet[j] = false & MemData != AuxData -> ShrSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_123"
	(Cache[j].State = S -> ShrSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1397"
		(i != j) ->	(Chan2[i].Cmd != Empty & CurCmd != ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_577"
		(i != j) ->	(Chan2[i].Data = AuxData & InvSet[i] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_405"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1513"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[j].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1525"
		(i != j) ->	(Chan3[j].Cmd != Empty & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_359"
		(i != j) ->	(Chan2[i].Cmd = Inv & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_531"
		(i != j) ->	(ExGntd = true & ShrSet[i] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_129"
		(i != j) ->	(ShrSet[j] = true -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1062"
		(i != j) ->	(Cache[j].State != I & CurCmd != ReqE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1452"
		(i != j) ->	(CurCmd = ReqS & Cache[i].Data = AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1489"
		(i != j) ->	(Chan3[j].Cmd = InvAck & InvSet[i] = true -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_435"
	(Chan2[j].Cmd != Empty & MemData != AuxData -> Cache[j].State = E);
endruleset;


ruleset i : NODE do
Invariant "rule_191"
	(Chan2[i].Cmd = GntE -> ShrSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_1092"
	(Chan2[j].Cmd = Inv & MemData != AuxData -> Cache[j].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1027"
		(i != j) ->	(Chan2[i].Cmd = GntS & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_439"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1509"
	(Chan2[j].Cmd = GntS & InvSet[j] = false -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_968"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_872"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].Data = AuxData -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_274"
		(i != j) ->	(Chan2[j].Cmd = GntE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_278"
		(i != j) ->	(Chan2[j].Cmd = GntE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_417"
		(i != j) ->	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_521"
		(i != j) ->	(CurCmd = ReqS & ShrSet[i] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_71"
	(CurCmd = Empty -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1137"
		(i != j) ->	(Chan3[i].Cmd = InvAck & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_941"
		(i != j) ->	(CurCmd != ReqE & InvSet[j] = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_513"
		(i != j) ->	(Chan2[i].Cmd != Empty & ExGntd = true -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_246"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1204"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan2[j].Cmd = GntS -> InvSet[j] = true);
endruleset;


ruleset i : NODE do
Invariant "rule_244"
	(Cache[i].State != I -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1359"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1057"
		(i != j) ->	(Chan3[i].Cmd != Empty & MemData != AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_806"
		(i != j) ->	(ExGntd = true & Chan2[j].Cmd != Empty -> ShrSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_884"
	(Cache[j].State != I & Cache[j].State != E -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1319"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Cache[j].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_768"
		(i != j) ->	(InvSet[i] = true & Chan3[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1009"
		(i != j) ->	(Cache[j].State != I & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_213"
	(ShrSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1576"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[j].State != S -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1530"
		(i != j) ->	(Chan2[i].Data = AuxData & CurCmd = ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_996"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Chan2[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_813"
	(CurCmd != ReqS & CurCmd != ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_366"
		(i != j) ->	(ShrSet[i] = true & Chan3[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_58"
	(Chan2[i].Cmd = GntE -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_182"
	(Cache[i].State != I -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1081"
		(i != j) ->	(Chan2[j].Cmd = Inv & ExGntd = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_290"
	(Cache[j].Data = AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_987"
		(i != j) ->	(ExGntd = true & Cache[j].State != I -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1245"
		(i != j) ->	(Cache[i].State = S & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1337"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan2[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_462"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan3[j].Cmd = InvAck -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_993"
	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1147"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = GntS -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1151"
		(i != j) ->	(InvSet[j] = true & MemData != AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1293"
	(InvSet[j] = false & Chan2[j].Cmd = GntE -> CurCmd != ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1121"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1269"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_217"
	(Cache[j].State = E -> ShrSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_365"
		(i != j) ->	(InvSet[i] = true & MemData != AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_921"
		(i != j) ->	(Chan2[i].Cmd != Empty & ExGntd = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_564"
	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1037"
		(i != j) ->	(ExGntd = true & Cache[j].Data = AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1213"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_375"
		(i != j) ->	(Chan2[j].Cmd = Inv & ShrSet[i] = true -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_701"
		(i != j) ->	(Chan2[i].Cmd != Empty & Cache[j].State != I -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_199"
	(ShrSet[i] = false -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_1054"
	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_953"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].State = S -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_958"
	(Cache[j].Data = AuxData & Cache[j].State != E -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1349"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1090"
		(i != j) ->	(InvSet[i] = true & Cache[j].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1250"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan3[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_148"
	(Cache[i].State != I -> Cache[i].Data = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_242"
	(Chan3[i].Cmd = InvAck -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_270"
	(Chan3[i].Data = AuxData -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1381"
		(i != j) ->	(ExGntd = true & Cache[i].State != I -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1076"
		(i != j) ->	(Cache[i].State != S & Cache[i].State != I -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_106"
	(Cache[i].State = S -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_24"
	(Chan3[i].Cmd != Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1348"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1400"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].State = S -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1278"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_164"
		(i != j) ->	(Chan3[j].Data = AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_638"
		(i != j) ->	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1127"
		(i != j) ->	(ExGntd = true & Cache[i].Data = AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1399"
		(i != j) ->	(MemData != AuxData & Chan2[i].Cmd = Inv -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1401"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[j].State != S -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_877"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd = InvAck -> ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_936"
	(Chan2[i].Cmd != Empty & InvSet[i] = true -> Chan2[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_793"
		(i != j) ->	(ExGntd = true & InvSet[j] = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_652"
		(i != j) ->	(Cache[j].State != I & InvSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_449"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_679"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].State != I -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_905"
		(i != j) ->	(ShrSet[i] = true & MemData != AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_800"
		(i != j) ->	(ExGntd = true & Cache[j].State != I -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1086"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1547"
		(i != j) ->	(Chan2[j].Cmd = Inv & MemData != AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1259"
		(i != j) ->	(ShrSet[j] = true & Chan3[i].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1353"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_307"
		(i != j) ->	(Chan2[j].Cmd = GntE -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_22"
	(ExGntd = false -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_1428"
	(MemData != AuxData & Cache[j].State != E -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_665"
	(Cache[i].State = S & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_783"
	(Chan2[i].Data = AuxData & InvSet[i] = false -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1157"
		(i != j) ->	(Chan3[i].Cmd != Empty & InvSet[j] = true -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_8"
	(Chan2[i].Cmd = Inv -> ShrSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_1190"
	(InvSet[j] = true & CurCmd = Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1584"
		(i != j) ->	(Chan2[i].Cmd != Empty & MemData != AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_1476"
	(CurCmd != ReqE & Cache[i].State = S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1159"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1222"
		(i != j) ->	(MemData != AuxData & Chan2[i].Cmd = Inv -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_812"
		(i != j) ->	(ExGntd = true & ShrSet[i] = true -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1015"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_775"
		(i != j) ->	(CurCmd = ReqS & Cache[i].State = S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_551"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1502"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_978"
	(Chan3[i].Cmd = InvAck & ExGntd = false -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_1079"
	(Chan2[j].Cmd = GntS & InvSet[j] = false -> CurCmd != ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_774"
	(Chan2[j].Cmd = Empty & InvSet[j] = true -> Cache[j].Data = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_1134"
	(Cache[i].State = S & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1029"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd != Empty -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1507"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].State != I -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_176"
	(InvSet[i] = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1388"
		(i != j) ->	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_11"
		(i != j) ->	(Chan2[i].Cmd = GntE -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_983"
		(i != j) ->	(ShrSet[j] = true & Chan3[i].Cmd = InvAck -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_1"
	(Chan3[i].Cmd = InvAck -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1266"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_661"
	(Cache[j].State = I & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_402"
		(i != j) ->	(Chan3[j].Cmd = InvAck & MemData != AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_326"
		(i != j) ->	(Chan2[j].Cmd = GntS -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_887"
		(i != j) ->	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1523"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_269"
	(Chan3[i].Cmd != Empty -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_670"
		(i != j) ->	(CurCmd != ReqE & InvSet[i] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_504"
		(i != j) ->	(ShrSet[j] = true & MemData != AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_603"
	(Chan3[j].Cmd = InvAck & ExGntd = false -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_38"
		(i != j) ->	(Chan3[i].Data = AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1529"
		(i != j) ->	(Chan2[i].Cmd = GntS & CurCmd != ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1368"
	(InvSet[j] = false & Cache[j].Data = AuxData -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1514"
		(i != j) ->	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_119"
	(Cache[i].Data = AuxData -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_881"
		(i != j) ->	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_186"
	(Cache[j].State = S -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_771"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_308"
	(Chan2[i].Data = AuxData -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1100"
		(i != j) ->	(ShrSet[i] = true & MemData != AuxData -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_46"
		(i != j) ->	(Cache[i].State = E -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_790"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1258"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_410"
		(i != j) ->	(ExGntd = true & Chan2[i].Cmd = Inv -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_360"
	(InvSet[j] = false & CurCmd != Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_909"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan2[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_784"
		(i != j) ->	(InvSet[j] = true & MemData != AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1216"
		(i != j) ->	(Cache[i].State != S & Chan3[j].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_903"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_944"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[i].State != S -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1028"
		(i != j) ->	(ShrSet[j] = true & Chan3[i].Cmd = InvAck -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_100"
	(Chan2[j].Cmd = GntE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_753"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_655"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_325"
		(i != j) ->	(Cache[i].State = E -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1417"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_706"
		(i != j) ->	(Chan2[j].Cmd != Empty & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_778"
		(i != j) ->	(ShrSet[j] = true & Cache[i].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_397"
	(Chan2[i].Data = AuxData & CurCmd = ReqS -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1344"
		(i != j) ->	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1581"
		(i != j) ->	(Cache[i].State != I & Cache[j].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_861"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Cache[j].State = S -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_799"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].Data = AuxData -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_438"
		(i != j) ->	(Cache[j].State != S & Cache[i].State != I -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1053"
	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_427"
		(i != j) ->	(Chan3[i].Cmd != Empty & ExGntd = true -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_124"
	(ShrSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_4"
	(Chan3[j].Data = AuxData -> ShrSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1122"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_739"
		(i != j) ->	(Cache[j].State = S & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_51"
		(i != j) ->	(Cache[j].State != I -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1486"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_432"
		(i != j) ->	(ExGntd = true & ShrSet[j] = false -> ShrSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_153"
	(ShrSet[j] = false -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_279"
	(MemData != AuxData -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_788"
		(i != j) ->	(Chan3[i].Cmd = InvAck & InvSet[j] = true -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_137"
		(i != j) ->	(ShrSet[i] = true -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1210"
		(i != j) ->	(ExGntd = true & Chan2[j].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_533"
		(i != j) ->	(Chan3[i].Cmd != Empty & ExGntd = true -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_15"
	(Chan2[j].Cmd = Inv -> Cache[j].State != I);
endruleset;


ruleset i : NODE do
Invariant "rule_1233"
	(Chan3[i].Cmd = InvAck & ExGntd = false -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_80"
	(Cache[j].Data = AuxData -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1436"
		(i != j) ->	(ShrSet[j] = true & Chan2[i].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1277"
		(i != j) ->	(CurCmd = ReqS & Cache[i].State != I -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1108"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_453"
		(i != j) ->	(ExGntd = true & Cache[j].Data = AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_433"
		(i != j) ->	(ExGntd = true & ShrSet[i] = true -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1172"
		(i != j) ->	(Chan2[i].Cmd = GntS & CurCmd != ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1463"
		(i != j) ->	(Chan2[j].Cmd = Inv & ExGntd = true -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_641"
		(i != j) ->	(Chan2[i].Cmd != Empty & CurCmd = ReqS -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1225"
		(i != j) ->	(Chan2[i].Data = AuxData & CurCmd = ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1153"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Data = AuxData -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_842"
		(i != j) ->	(Chan2[j].Cmd != Empty & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1264"
	(MemData != AuxData & Cache[j].Data = AuxData -> Cache[j].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1299"
		(i != j) ->	(Chan2[j].Cmd = GntS & Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_716"
		(i != j) ->	(Cache[i].State != I & Cache[j].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_932"
		(i != j) ->	(Cache[i].Data = AuxData & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1423"
		(i != j) ->	(ExGntd = true & Chan2[i].Cmd = Inv -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_841"
	(Cache[j].State = S & InvSet[j] = false -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1314"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Cache[j].State != S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1034"
		(i != j) ->	(InvSet[i] = true & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_136"
		(i != j) ->	(Chan2[i].Cmd = GntE -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1279"
	(Cache[j].State != I & Cache[j].State != S -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_611"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1357"
		(i != j) ->	(Cache[j].State != S & Cache[j].Data = AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_590"
		(i != j) ->	(Chan2[i].Data = AuxData & Cache[j].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1145"
	(Cache[i].State != E & Cache[i].State != I -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_386"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan3[j].Cmd = InvAck -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_425"
	(Cache[i].State != S & Chan2[i].Cmd = Inv -> ExGntd = true);
endruleset;


ruleset j : NODE do
Invariant "rule_520"
	(CurCmd = ReqS & Cache[j].State = S -> InvSet[j] = true);
endruleset;


ruleset i : NODE do
Invariant "rule_1532"
	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_225"
		(i != j) ->	(Cache[j].State = E -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1500"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].State = S -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_620"
		(i != j) ->	(Chan2[j].Cmd = Inv & ExGntd = true -> ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_240"
	(Chan3[i].Data = AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_980"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan3[j].Cmd != Empty -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1418"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan3[j].Cmd = InvAck -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_626"
	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1538"
		(i != j) ->	(Chan2[j].Cmd != Empty & Cache[i].State != I -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1241"
		(i != j) ->	(ExGntd = true & Cache[i].State != I -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_149"
	(Chan2[i].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1080"
		(i != j) ->	(Chan3[j].Cmd != Empty & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1378"
		(i != j) ->	(Chan2[i].Data = AuxData & CurCmd != ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_901"
	(Cache[i].State = I & InvSet[i] = true -> Chan2[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_831"
		(i != j) ->	(CurCmd != ReqE & Chan2[j].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_685"
	(Cache[i].State != S & ExGntd = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1466"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1429"
		(i != j) ->	(Cache[j].State != I & ShrSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1499"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_388"
		(i != j) ->	(CurCmd != ReqE & Cache[i].State != I -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1519"
		(i != j) ->	(InvSet[i] = true & Cache[j].Data = AuxData -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_236"
	(MemData != AuxData -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_99"
		(i != j) ->	(Cache[j].State = E -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_143"
	(Chan2[j].Cmd != Empty -> ShrSet[j] = true);
endruleset;


ruleset i : NODE do
Invariant "rule_245"
	(ExGntd = false -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_796"
	(ExGntd = true & InvSet[j] = true -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_819"
		(i != j) ->	(InvSet[j] = true & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1206"
		(i != j) ->	(Chan2[i].Cmd != Empty & ExGntd = true -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_763"
	(CurCmd = Empty & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1188"
	(Cache[i].State != E & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1229"
		(i != j) ->	(Cache[i].State != S & Chan2[i].Cmd = Inv -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_91"
		(i != j) ->	(Chan2[j].Cmd != Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_1550"
	(Chan2[j].Cmd = Inv & Cache[j].State != E -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_1539"
	(Chan2[i].Data = AuxData & CurCmd != Empty -> InvSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_949"
	(Chan2[j].Cmd != Empty & CurCmd = Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1163"
		(i != j) ->	(CurCmd != ReqE & Cache[i].State != I -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1146"
		(i != j) ->	(InvSet[j] = true & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_169"
		(i != j) ->	(Cache[i].State = E -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1006"
		(i != j) ->	(InvSet[j] = true & Cache[i].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_339"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_380"
		(i != j) ->	(Chan3[i].Cmd != Empty & MemData != AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1132"
		(i != j) ->	(Chan3[i].Cmd = InvAck & InvSet[j] = true -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_578"
		(i != j) ->	(ExGntd = true & Cache[j].Data = AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1323"
		(i != j) ->	(Chan2[i].Cmd != Empty & CurCmd = ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_633"
	(Cache[i].State != E & Cache[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1226"
		(i != j) ->	(Cache[i].Data = AuxData & MemData != AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_583"
		(i != j) ->	(ShrSet[j] = true & Cache[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1543"
	(Chan2[j].Cmd != Empty & Cache[j].State != E -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_70"
	(Chan3[i].Cmd = InvAck -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_536"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd != Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_63"
		(i != j) ->	(InvSet[j] = true -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_459"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_340"
	(Chan2[i].Cmd != Empty & Chan2[i].Cmd != Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_40"
	(Cache[i].State = S -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1155"
	(CurCmd = Empty & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_316"
	(ShrSet[i] = false -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_1304"
	(CurCmd = ReqE & Chan2[j].Cmd = GntS -> InvSet[j] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_249"
	(Chan2[j].Cmd = Inv -> ShrSet[j] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_426"
	(Chan2[j].Cmd != Empty & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_57"
	(ShrSet[i] = false -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_493"
		(i != j) ->	(ExGntd = true & Chan2[i].Data = AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1406"
		(i != j) ->	(Cache[i].State != S & Cache[i].State != I -> Cache[j].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_487"
	(Chan2[j].Cmd = Inv & ExGntd = false -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_344"
		(i != j) ->	(Chan2[j].Cmd != Empty & MemData != AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_584"
		(i != j) ->	(MemData != AuxData & Chan2[i].Cmd = Inv -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1084"
		(i != j) ->	(InvSet[j] = true & Cache[i].State != I -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1573"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_832"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_770"
		(i != j) ->	(Chan2[i].Cmd != Empty & ExGntd = true -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_30"
	(ShrSet[i] = false -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1012"
		(i != j) ->	(Chan2[j].Cmd = Inv & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_277"
	(Chan2[j].Cmd = GntS -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_779"
	(CurCmd = ReqE & InvSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1468"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Cache[j].State = S -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1001"
		(i != j) ->	(Cache[i].State != S & Cache[i].State != I -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_348"
		(i != j) ->	(CurCmd != ReqE & Cache[j].State = S -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1347"
		(i != j) ->	(Chan2[j].Cmd = Inv & InvSet[i] = true -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_305"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan2[j].Cmd != GntS);
endruleset;
Invariant "rule_194"
	(ExGntd = false -> MemData = AuxData);


ruleset i : NODE ; j : NODE do
Invariant "rule_840"
		(i != j) ->	(Chan3[i].Cmd != Empty & ExGntd = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_876"
		(i != j) ->	(Chan3[i].Cmd != Empty & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_200"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_233"
	(Chan3[j].Cmd = InvAck -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_963"
		(i != j) ->	(InvSet[j] = true & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1295"
		(i != j) ->	(Cache[i].State != I & MemData != AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1167"
		(i != j) ->	(Cache[j].State != I & MemData != AuxData -> ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_645"
	(Chan2[i].Data = AuxData & ExGntd = false -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1112"
		(i != j) ->	(ExGntd = true & Cache[i].Data = AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_891"
		(i != j) ->	(ShrSet[i] = true & Cache[j].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_601"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_630"
		(i != j) ->	(Chan2[j].Cmd = Inv & ExGntd = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_937"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1284"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_663"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Chan3[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_450"
		(i != j) ->	(Chan2[j].Cmd = Inv & ShrSet[i] = true -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1562"
		(i != j) ->	(Cache[i].State != S & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1128"
		(i != j) ->	(Cache[i].State != S & Cache[j].Data = AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_79"
	(ShrSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_780"
		(i != j) ->	(Cache[i].State != I & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_765"
		(i != j) ->	(ExGntd = true & Chan3[i].Cmd = InvAck -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_593"
		(i != j) ->	(Cache[j].State != I & MemData != AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_596"
		(i != j) ->	(Cache[i].Data = AuxData & Chan3[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1198"
		(i != j) ->	(Chan2[i].Cmd != Empty & CurCmd = ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1574"
		(i != j) ->	(MemData != AuxData & Chan2[i].Cmd = Inv -> Cache[j].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_1544"
	(Chan2[i].Cmd != Empty & MemData != AuxData -> CurCmd != Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_241"
	(Chan2[i].Cmd = GntE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_972"
		(i != j) ->	(ShrSet[j] = true & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_960"
		(i != j) ->	(Chan3[j].Cmd = InvAck & MemData != AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1228"
		(i != j) ->	(Chan3[i].Cmd != Empty & ExGntd = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_815"
	(Chan2[j].Cmd != Empty & Cache[j].State = E -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_860"
	(Cache[i].State != E & MemData != AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_369"
		(i != j) ->	(ShrSet[j] = true & Chan2[i].Data = AuxData -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1398"
		(i != j) ->	(CurCmd != ReqE & Cache[i].State = S -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_282"
	(Chan3[i].Data = AuxData -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_65"
	(ExGntd = true -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1058"
		(i != j) ->	(InvSet[j] = true & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE do
Invariant "rule_1444"
	(Chan2[i].Cmd = GntS & InvSet[i] = false -> CurCmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_12"
	(Chan3[i].Cmd != Empty -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_407"
	(CurCmd = ReqS & InvSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_291"
	(Chan2[i].Cmd = GntS -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_486"
	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_543"
	(Chan2[i].Cmd = GntS & Cache[i].State != I -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1549"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = GntS -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_718"
		(i != j) ->	(ShrSet[j] = true & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_991"
	(Cache[i].Data = AuxData & MemData != AuxData -> Cache[i].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_404"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1333"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan3[j].Cmd = InvAck -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_101"
		(i != j) ->	(Cache[j].State = E -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_1577"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_1294"
	(Chan2[i].Cmd = GntS & InvSet[i] = false -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_1251"
	(ExGntd = true & Chan2[i].Data = AuxData -> Cache[i].State = I);
endruleset;


ruleset j : NODE do
Invariant "rule_317"
	(Chan2[j].Cmd = GntS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1017"
		(i != j) ->	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1571"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].State != I -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_974"
		(i != j) ->	(Cache[i].Data = AuxData & MemData != AuxData -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_676"
		(i != j) ->	(Cache[j].State = S & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1464"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd = InvAck -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1161"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan3[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_301"
	(MemData != AuxData -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1522"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_643"
		(i != j) ->	(Cache[i].Data = AuxData & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1564"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[j].State != S -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_699"
	(ExGntd = true & Chan2[i].Cmd = Inv -> Cache[i].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1587"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_206"
	(ShrSet[j] = false -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_1535"
	(Chan2[i].Data = AuxData & Cache[i].State = S -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1552"
		(i != j) ->	(Chan2[i].Cmd = GntS & CurCmd != ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_705"
		(i != j) ->	(Cache[j].State != I & Cache[j].State != S -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_1408"
	(Cache[i].State != E & Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_276"
		(i != j) ->	(Chan3[i].Data = AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_608"
		(i != j) ->	(Cache[j].State != I & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_761"
	(MemData != AuxData & Chan2[i].Cmd = Inv -> Cache[i].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_556"
		(i != j) ->	(Chan2[i].Cmd != Empty & Cache[j].State != I -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1166"
		(i != j) ->	(ExGntd = true & Cache[j].State != I -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_353"
		(i != j) ->	(ExGntd = true & Cache[j].Data = AuxData -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1193"
		(i != j) ->	(CurCmd = ReqS & Cache[i].State != I -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1110"
		(i != j) ->	(Cache[i].State != I & MemData != AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1528"
		(i != j) ->	(Chan2[i].Cmd = GntS & Chan3[j].Cmd != Empty -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_264"
	(Chan2[j].Cmd = GntS -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1114"
		(i != j) ->	(ShrSet[j] = true & CurCmd = ReqS -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_1365"
	(Cache[j].State != I & Cache[j].State != S -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1515"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].State != I -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_37"
	(Chan3[i].Data = AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1380"
		(i != j) ->	(Chan2[i].Cmd = GntS & InvSet[i] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1247"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_134"
		(i != j) ->	(Cache[j].State = E -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_731"
	(Chan2[i].Cmd != Empty & Chan2[i].Cmd != Inv -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_180"
		(i != j) ->	(Cache[j].State = S -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_1326"
	(CurCmd != ReqE & ExGntd = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_92"
		(i != j) ->	(Chan3[j].Data = AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_159"
		(i != j) ->	(Cache[j].State = E -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_677"
	(ExGntd = false & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1376"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_635"
	(Chan2[i].Cmd != GntE & Chan2[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_327"
		(i != j) ->	(Cache[i].State = S -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1343"
		(i != j) ->	(ExGntd = true & Cache[i].State != I -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_370"
		(i != j) ->	(ShrSet[i] = false & ShrSet[j] = false -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_373"
		(i != j) ->	(Chan2[i].Cmd != Empty & CurCmd != ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1217"
	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> Chan3[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_416"
		(i != j) ->	(Chan2[i].Cmd != Empty & MemData != AuxData -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_588"
		(i != j) ->	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> ShrSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_132"
	(Cache[i].State != I -> ShrSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_114"
	(Chan2[j].Cmd != Empty -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1040"
		(i != j) ->	(ShrSet[j] = true & Cache[i].State != I -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_116"
		(i != j) ->	(Chan2[i].Cmd = GntE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_78"
		(i != j) ->	(Chan3[i].Data = AuxData -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_904"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Cache[j].Data = AuxData -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_917"
		(i != j) ->	(ShrSet[j] = true & CurCmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_98"
	(Chan2[i].Cmd != Empty -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_845"
		(i != j) ->	(Chan2[i].Cmd != Empty & Chan3[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1382"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_144"
	(Chan2[j].Cmd = GntE -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_746"
		(i != j) ->	(ShrSet[j] = true & Chan3[i].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_979"
		(i != j) ->	(Chan2[i].Cmd = GntS & CurCmd = ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_394"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_205"
	(Chan2[i].Data = AuxData -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_929"
		(i != j) ->	(Chan3[j].Cmd != Empty & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_293"
		(i != j) ->	(Chan2[i].Cmd = Inv -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1320"
		(i != j) ->	(Cache[j].State != I & Cache[j].State != S -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_572"
		(i != j) ->	(Chan2[j].Cmd = GntS & InvSet[j] = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1051"
		(i != j) ->	(Cache[i].Data = AuxData & Cache[i].State != S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_1307"
	(Cache[j].State != S & Cache[j].State != E -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_733"
		(i != j) ->	(CurCmd != ReqE & InvSet[j] = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1548"
		(i != j) ->	(Chan2[j].Cmd != Empty & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1504"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_754"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan3[i].Cmd = InvAck -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_257"
		(i != j) ->	(Chan3[j].Data = AuxData -> Cache[i].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_189"
	(Chan3[j].Data = AuxData -> Chan3[j].Cmd = InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1162"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd != Empty -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1049"
		(i != j) ->	(ExGntd = true & Chan2[j].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_451"
		(i != j) ->	(Cache[i].State != S & Chan2[i].Cmd = Inv -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_946"
		(i != j) ->	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_468"
	(InvSet[j] = true & Cache[j].State = E -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_600"
		(i != j) ->	(ExGntd = true & Cache[i].State != I -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1329"
	(Chan2[i].Cmd != Empty & CurCmd = Empty -> Chan2[i].Data = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_924"
	(Chan2[j].Cmd = Inv & Cache[j].State = S -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_406"
	(ExGntd = true & CurCmd = Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1501"
		(i != j) ->	(MemData != AuxData & Cache[j].Data = AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_414"
		(i != j) ->	(ExGntd = true & Chan2[j].Cmd != Empty -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_782"
		(i != j) ->	(ExGntd = true & Cache[i].State != I -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_809"
		(i != j) ->	(Chan3[i].Cmd = InvAck & InvSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1508"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = Inv -> Cache[j].State = S);
endruleset;


ruleset i : NODE do
Invariant "rule_598"
	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> Cache[i].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1350"
		(i != j) ->	(Chan2[i].Cmd != Empty & CurCmd != ReqE -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1437"
		(i != j) ->	(Chan2[j].Cmd != Empty & MemData != AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1414"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd = ReqS -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1579"
		(i != j) ->	(Cache[j].State != I & CurCmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_965"
	(Chan2[j].Cmd = Inv & ExGntd = false -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_320"
	(Chan2[i].Cmd = GntE -> Cache[i].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_310"
	(Chan2[j].Cmd = GntE -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_356"
		(i != j) ->	(CurCmd = ReqS & Cache[j].State = S -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1303"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[i].Cmd != GntS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_2"
	(Chan3[i].Cmd = InvAck -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_526"
	(Chan2[j].Cmd = GntS & InvSet[j] = false -> Cache[j].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_193"
	(MemData != AuxData -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_622"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan3[j].Cmd = InvAck -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_514"
		(i != j) ->	(Cache[j].State != I & Chan2[i].Cmd = Inv -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1409"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd = InvAck -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1274"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].Data = AuxData -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_619"
		(i != j) ->	(Chan2[i].Cmd = GntS & Chan3[j].Cmd != Empty -> InvSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_1545"
	(CurCmd = ReqS & Chan2[j].Cmd = GntE -> InvSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1351"
		(i != j) ->	(Cache[j].State != S & Cache[j].Data = AuxData -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_880"
		(i != j) ->	(Cache[i].State != S & Cache[i].State != I -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_165"
		(i != j) ->	(Chan2[j].Cmd = GntE -> InvSet[i] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1201"
	(Chan2[j].Cmd != Empty & CurCmd = Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_171"
		(i != j) ->	(Cache[i].Data = AuxData -> Chan2[j].Cmd != GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_234"
	(Chan2[j].Cmd = GntE -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_606"
		(i != j) ->	(ExGntd = true & InvSet[j] = true -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_471"
		(i != j) ->	(ShrSet[j] = true & ExGntd = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_306"
		(i != j) ->	(Chan3[j].Data = AuxData -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_254"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Cache[j].State != E);
endruleset;


ruleset j : NODE do
Invariant "rule_6"
	(Chan3[j].Cmd = InvAck -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_32"
		(i != j) ->	(Chan2[j].Cmd = GntE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1313"
		(i != j) ->	(Cache[j].State != I & Cache[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1055"
		(i != j) ->	(ExGntd = true & Cache[i].Data = AuxData -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_805"
		(i != j) ->	(ShrSet[j] = true & ExGntd = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_693"
		(i != j) ->	(InvSet[j] = true & MemData != AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_61"
	(Cache[j].State = E -> Cache[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_781"
		(i != j) ->	(Chan2[i].Cmd = GntS & Chan3[j].Cmd = InvAck -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_379"
		(i != j) ->	(ShrSet[j] = true & ShrSet[i] = true -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1534"
		(i != j) ->	(Chan3[j].Cmd != Empty & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset j : NODE do
Invariant "rule_222"
	(Chan3[j].Cmd != Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_218"
	(ShrSet[i] = false -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1375"
		(i != j) ->	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1355"
		(i != j) ->	(Chan2[j].Cmd = GntS & Chan2[i].Data = AuxData -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_62"
		(i != j) ->	(Chan3[j].Data = AuxData -> Cache[i].State != S);
endruleset;


ruleset i : NODE do
Invariant "rule_1291"
	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1317"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].Data = AuxData -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1498"
		(i != j) ->	(Chan2[j].Cmd != Empty & Cache[i].State != I -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_17"
	(ShrSet[j] = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_914"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_431"
		(i != j) ->	(Chan3[j].Cmd = InvAck & ShrSet[i] = true -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1200"
		(i != j) ->	(CurCmd = ReqS & InvSet[j] = true -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1234"
		(i != j) ->	(Cache[i].State != S & Chan2[i].Cmd = Inv -> Cache[j].State != S);
endruleset;


ruleset j : NODE do
Invariant "rule_331"
	(Chan2[j].Cmd = Inv -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_7"
	(Chan3[j].Cmd != Empty -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1007"
		(i != j) ->	(Chan2[i].Data = AuxData & Cache[j].State != S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_84"
	(InvSet[j] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1036"
		(i != j) ->	(Chan2[i].Cmd != Empty & Cache[j].State != S -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_489"
	(InvSet[j] = true & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_160"
		(i != j) ->	(Cache[i].State = E -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_374"
	(InvSet[i] = true & CurCmd = Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_735"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Data = AuxData -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1331"
	(ExGntd = false & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_869"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_391"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_207"
		(i != j) ->	(Cache[j].Data = AuxData -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_898"
		(i != j) ->	(Cache[j].State != S & Cache[j].Data = AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_820"
		(i != j) ->	(Chan3[j].Cmd = InvAck & MemData != AuxData -> Cache[i].State = I);
endruleset;


ruleset i : NODE do
Invariant "rule_256"
	(ShrSet[i] = false -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_226"
		(i != j) ->	(Chan2[j].Cmd = GntE -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_1115"
	(Chan2[i].Cmd != Empty & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_587"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].State = S -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1563"
		(i != j) ->	(Chan2[i].Cmd != Empty & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_544"
	(Chan2[j].Cmd = GntS & CurCmd = ReqS -> InvSet[j] = true);
endruleset;


ruleset i : NODE do
Invariant "rule_252"
	(Cache[i].State = S -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_243"
	(Cache[j].State = E -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1491"
		(i != j) ->	(Chan2[i].Cmd = GntS & Chan3[j].Cmd = InvAck -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_804"
	(InvSet[j] = true & CurCmd = Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_955"
		(i != j) ->	(Chan2[j].Cmd = Inv & InvSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1363"
		(i != j) ->	(Cache[i].State != S & Cache[i].State != I -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1311"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_445"
		(i != j) ->	(ExGntd = true & ShrSet[i] = true -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1477"
		(i != j) ->	(MemData != AuxData & Cache[j].Data = AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1324"
		(i != j) ->	(CurCmd = ReqS & Chan2[j].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1298"
		(i != j) ->	(Chan2[j].Cmd = GntS & CurCmd != ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1156"
	(CurCmd = ReqS & ExGntd = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1570"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_494"
		(i != j) ->	(InvSet[i] = true & MemData != AuxData -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_461"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].Data = AuxData -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_631"
	(ExGntd = true & Cache[i].Data = AuxData -> Cache[i].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1107"
		(i != j) ->	(Chan2[i].Data = AuxData & InvSet[i] = false -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1043"
	(CurCmd != ReqS & CurCmd != ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_1191"
	(Cache[i].State != E & CurCmd != ReqE -> Chan2[i].Cmd != Inv);
endruleset;
Invariant "rule_262"
	(MemData != AuxData -> ExGntd = true);


ruleset i : NODE ; j : NODE do
Invariant "rule_364"
		(i != j) ->	(ShrSet[i] = true & MemData != AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_850"
		(i != j) ->	(Chan3[j].Cmd = InvAck & ShrSet[i] = true -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1236"
		(i != j) ->	(CurCmd = ReqS & Cache[i].Data = AuxData -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_178"
		(i != j) ->	(Chan2[j].Cmd = GntE -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_931"
		(i != j) ->	(ExGntd = true & ShrSet[i] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_854"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1520"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan3[j].Cmd = InvAck -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1566"
		(i != j) ->	(ShrSet[i] = true & MemData != AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_557"
		(i != j) ->	(Chan3[i].Cmd != Empty & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_31"
	(Chan3[i].Cmd = InvAck -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_657"
		(i != j) ->	(CurCmd = ReqS & InvSet[j] = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_259"
	(Cache[j].State = I -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1387"
		(i != j) ->	(Cache[i].Data = AuxData & MemData != AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1087"
	(CurCmd = Empty & MemData != AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1016"
	(ExGntd = false & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE do
Invariant "rule_636"
	(CurCmd = ReqS & ExGntd = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_220"
	(Chan3[j].Cmd != Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1407"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Cmd = GntS -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_567"
	(InvSet[i] = true & MemData != AuxData -> Cache[i].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_492"
		(i != j) ->	(Chan2[j].Cmd = GntS & Chan2[i].Cmd = Inv -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_1385"
	(Chan2[i].Cmd = Empty & InvSet[i] = true -> Cache[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_940"
		(i != j) ->	(Chan3[i].Cmd != Empty & InvSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_834"
		(i != j) ->	(Cache[j].State != I & Cache[i].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1484"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_481"
	(CurCmd != ReqE & ExGntd = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_383"
		(i != j) ->	(InvSet[j] = true & Chan2[i].Cmd = Inv -> ExGntd = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1373"
	(Chan2[i].Cmd = GntS & Cache[i].Data = AuxData -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_721"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Cache[i].State != I -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_69"
		(i != j) ->	(Chan2[j].Cmd = Inv -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1078"
		(i != j) ->	(Cache[j].State != S & Cache[j].Data = AuxData -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_569"
		(i != j) ->	(Cache[i].Data = AuxData & Chan3[j].Cmd != Empty -> Cache[i].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_1438"
	(InvSet[j] = true & Chan2[j].Cmd != Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1403"
		(i != j) ->	(Chan2[j].Cmd != Empty & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE do
Invariant "rule_21"
	(InvSet[i] = true -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_689"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan2[i].Data = AuxData -> InvSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_886"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan3[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_843"
		(i != j) ->	(CurCmd = ReqS & Chan3[j].Cmd != Empty -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_465"
		(i != j) ->	(ExGntd = true & Chan2[i].Cmd = Inv -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_675"
		(i != j) ->	(CurCmd != ReqE & Cache[i].State = S -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset j : NODE do
Invariant "rule_964"
	(Cache[j].State = I & InvSet[j] = true -> Chan2[j].Cmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1179"
		(i != j) ->	(Chan3[i].Cmd != Empty & ExGntd = true -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_650"
	(CurCmd = ReqE & Chan2[j].Cmd = GntE -> InvSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_585"
		(i != j) ->	(Chan2[j].Cmd != Empty & ShrSet[i] = true -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_482"
	(Cache[j].State = I & InvSet[j] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_990"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> Chan2[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_532"
		(i != j) ->	(ExGntd = true & Chan2[i].Data = AuxData -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_36"
	(CurCmd = Empty -> Chan2[j].Cmd != Inv);
endruleset;


ruleset j : NODE do
Invariant "rule_967"
	(Chan2[j].Cmd = GntS & InvSet[j] = false -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1237"
		(i != j) ->	(InvSet[i] = false & Chan3[j].Cmd != Empty -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_727"
		(i != j) ->	(Chan3[i].Cmd != Empty & InvSet[j] = true -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_385"
	(Cache[j].State = I & Chan2[j].Cmd = Empty -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_888"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[j].State != S -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_421"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_1231"
	(Chan2[j].Cmd != Empty & MemData != AuxData -> Cache[j].Data = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_1369"
	(Chan2[i].Cmd != Empty & CurCmd = Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_195"
		(i != j) ->	(Chan3[j].Data = AuxData -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_473"
		(i != j) ->	(ExGntd = true & Cache[j].Data = AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_131"
	(Cache[i].Data = AuxData -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_1395"
	(Cache[i].State != E & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1309"
		(i != j) ->	(Chan3[j].Cmd = InvAck & CurCmd != ReqE -> Cache[i].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_172"
		(i != j) ->	(Chan3[j].Data = AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1524"
		(i != j) ->	(Cache[j].State != S & Cache[j].Data = AuxData -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1255"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1061"
	(Chan2[j].Cmd = Empty & InvSet[j] = true -> Cache[j].State != I);
endruleset;


ruleset i : NODE do
Invariant "rule_250"
	(Chan2[i].Cmd != Empty -> ShrSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_271"
	(Chan3[j].Cmd = InvAck -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_230"
		(i != j) ->	(Chan3[i].Cmd = InvAck -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_913"
		(i != j) ->	(Cache[j].State != I & ShrSet[i] = true -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_642"
		(i != j) ->	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_871"
		(i != j) ->	(Chan2[i].Cmd = GntS & CurCmd = ReqS -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_457"
		(i != j) ->	(InvSet[j] = true & ShrSet[i] = true -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_201"
		(i != j) ->	(ShrSet[j] = true -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1202"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_350"
	(Cache[i].State != E & Cache[i].Data = AuxData -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1173"
		(i != j) ->	(ShrSet[j] = true & CurCmd != ReqE -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_88"
	(Chan2[i].Cmd = Inv -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1306"
		(i != j) ->	(CurCmd = ReqS & Cache[j].State = S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_442"
		(i != j) ->	(Cache[j].State != I & MemData != AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_999"
		(i != j) ->	(ExGntd = true & InvSet[i] = true -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_640"
	(Chan2[i].Cmd != Empty & Cache[i].State != E -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1069"
		(i != j) ->	(ExGntd = true & Cache[j].State != I -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_361"
	(CurCmd != ReqE & ExGntd = false -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_221"
	(Chan3[i].Data = AuxData -> ExGntd = true);
endruleset;


ruleset j : NODE do
Invariant "rule_338"
	(ExGntd = true & Cache[j].State != E -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_724"
		(i != j) ->	(Chan3[i].Cmd != Empty & Chan2[j].Cmd = GntS -> CurCmd != ReqS);
endruleset;


ruleset i : NODE do
Invariant "rule_580"
	(Chan3[i].Cmd != Empty & ExGntd = true -> Chan3[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_628"
		(i != j) ->	(ShrSet[j] = true & Chan3[i].Cmd = InvAck -> CurCmd = ReqE);
endruleset;


ruleset i : NODE do
Invariant "rule_90"
	(Chan2[i].Cmd = GntS -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_19"
	(ShrSet[i] = false -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_772"
		(i != j) ->	(Cache[i].Data = AuxData & MemData != AuxData -> Chan2[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_1312"
	(Chan2[j].Cmd != Empty & Cache[j].State = E -> CurCmd != Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_816"
	(ExGntd = true & Chan3[j].Cmd != Empty -> Chan3[j].Data = AuxData);
endruleset;


ruleset i : NODE do
Invariant "rule_1465"
	(Cache[i].State != S & Cache[i].State != I -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1322"
		(i != j) ->	(CurCmd != ReqE & Chan3[j].Cmd != Empty -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1316"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd = InvAck -> Chan3[i].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_496"
	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> Cache[j].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_334"
		(i != j) ->	(Chan2[j].Cmd != Empty -> Cache[i].State != E);
endruleset;


ruleset i : NODE do
Invariant "rule_68"
	(Chan3[i].Data = AuxData -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_41"
		(i != j) ->	(Cache[i].State = S -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE do
Invariant "rule_517"
	(ExGntd = true & Chan2[i].Data = AuxData -> Chan2[i].Cmd = GntE);
endruleset;


ruleset j : NODE do
Invariant "rule_96"
	(Chan2[j].Cmd = Inv -> Cache[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_555"
		(i != j) ->	(Chan3[i].Cmd = InvAck & MemData != AuxData -> ShrSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1208"
	(Chan2[j].Cmd = GntS & Cache[j].State != I -> InvSet[j] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_723"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd = InvAck -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1290"
		(i != j) ->	(CurCmd = ReqS & Cache[i].State = S -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1199"
		(i != j) ->	(Chan2[i].Data = AuxData & Cache[j].Data = AuxData -> Chan2[i].Cmd = GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1183"
		(i != j) ->	(ShrSet[j] = true & CurCmd = ReqS -> Chan3[i].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_945"
		(i != j) ->	(CurCmd != ReqE & ShrSet[i] = true -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_157"
	(Chan2[i].Cmd = GntE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1285"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd != ReqE -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_474"
	(ExGntd = false & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_247"
	(Cache[j].State = E -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_203"
	(Chan2[i].Cmd = GntS -> Chan2[i].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_868"
		(i != j) ->	(Cache[i].State != I & MemData != AuxData -> ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_188"
		(i != j) ->	(Cache[i].State = E -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1527"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].State = S -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_13"
	(Chan2[j].Cmd = GntS -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_253"
		(i != j) ->	(Chan3[j].Cmd != Empty -> Chan2[i].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_185"
		(i != j) ->	(Chan3[i].Data = AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1411"
	(ExGntd = true & Cache[i].State != E -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_387"
	(Cache[i].State != E & InvSet[i] = true -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_1383"
	(Cache[j].State = I & Chan2[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_1586"
	(Chan2[j].Cmd != Inv & Chan2[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1441"
		(i != j) ->	(Chan2[j].Cmd = Inv & MemData != AuxData -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_985"
		(i != j) ->	(Chan2[j].Cmd = GntS & Chan3[i].Cmd = InvAck -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_231"
		(i != j) ->	(Chan3[i].Data = AuxData -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_697"
		(i != j) ->	(InvSet[i] = true & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset j : NODE do
Invariant "rule_1340"
	(Cache[j].State = I & MemData != AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_510"
		(i != j) ->	(CurCmd != ReqE & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1045"
		(i != j) ->	(ExGntd = true & Chan3[j].Cmd = InvAck -> Chan3[i].Cmd != InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_943"
		(i != j) ->	(Chan2[j].Cmd = Inv & Chan3[i].Cmd = InvAck -> CurCmd = ReqE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_791"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_75"
	(Chan3[j].Data = AuxData -> InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1041"
		(i != j) ->	(ExGntd = true & Cache[i].Data = AuxData -> Chan2[j].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_1150"
	(CurCmd = ReqS & ExGntd = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1297"
		(i != j) ->	(ExGntd = true & Cache[i].State != I -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_501"
		(i != j) ->	(Chan3[j].Cmd = InvAck & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_758"
		(i != j) ->	(Chan2[j].Cmd = Inv & InvSet[i] = false -> Chan2[i].Cmd != GntS);
endruleset;


ruleset j : NODE do
Invariant "rule_594"
	(InvSet[j] = true & MemData != AuxData -> Cache[j].Data = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_933"
		(i != j) ->	(CurCmd != ReqE & ShrSet[i] = true -> Chan3[j].Cmd = Empty);
endruleset;


ruleset j : NODE do
Invariant "rule_102"
	(Chan3[j].Cmd = InvAck -> CurCmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1420"
		(i != j) ->	(Chan2[i].Data = AuxData & CurCmd = ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_127"
	(Chan3[i].Data = AuxData -> Chan3[i].Cmd != Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_349"
		(i != j) ->	(Chan3[i].Cmd != Empty & CurCmd = ReqS -> Chan2[j].Cmd = Empty);
endruleset;


ruleset i : NODE do
Invariant "rule_49"
	(Cache[i].State = S -> ShrSet[i] = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1301"
		(i != j) ->	(Chan3[i].Cmd = InvAck & CurCmd = ReqS -> Chan3[j].Cmd = Empty);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1152"
		(i != j) ->	(Chan2[j].Cmd = GntS & InvSet[j] = false -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_430"
		(i != j) ->	(Cache[i].State != S & Chan2[i].Cmd = Inv -> ShrSet[j] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_711"
	(ExGntd = false & Chan2[i].Cmd = Inv -> CurCmd != ReqS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1492"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd != ReqE -> Chan2[i].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_499"
		(i != j) ->	(ShrSet[j] = true & ExGntd = true -> ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_423"
		(i != j) ->	(ShrSet[j] = true & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_535"
		(i != j) ->	(ShrSet[j] = true & InvSet[i] = true -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_970"
	(Cache[j].State != S & Cache[j].Data = AuxData -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_151"
		(i != j) ->	(Chan2[i].Cmd != Empty -> Chan2[j].Cmd != GntE);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1021"
		(i != j) ->	(Chan2[j].Cmd = Inv & Cache[i].State != I -> Cache[j].State = S);
endruleset;


ruleset i : NODE do
Invariant "rule_1194"
	(Chan3[i].Cmd != Empty & CurCmd != ReqE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1300"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan3[j].Cmd != Empty -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_187"
	(ExGntd = true -> Cache[j].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_829"
		(i != j) ->	(InvSet[i] = true & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1455"
		(i != j) ->	(Chan2[j].Cmd != Empty & MemData != AuxData -> InvSet[i] = false);
endruleset;


ruleset i : NODE do
Invariant "rule_1334"
	(CurCmd = ReqE & Chan2[i].Cmd = GntS -> InvSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_267"
	(Cache[j].Data = AuxData -> Cache[j].State != I);
endruleset;


ruleset i : NODE do
Invariant "rule_1379"
	(Chan2[i].Cmd = GntS & Cache[i].Data = AuxData -> Cache[i].State = S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_966"
		(i != j) ->	(Chan2[j].Cmd = Inv & ShrSet[i] = true -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1557"
		(i != j) ->	(Cache[i].State != S & Chan2[i].Cmd = Inv -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1328"
		(i != j) ->	(Chan3[i].Cmd = InvAck & Chan2[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset j : NODE do
Invariant "rule_168"
	(InvSet[j] = true -> Chan3[j].Cmd != InvAck);
endruleset;


ruleset i : NODE do
Invariant "rule_1308"
	(Chan2[i].Cmd = GntS & CurCmd = ReqS -> InvSet[i] = true);
endruleset;


ruleset j : NODE do
Invariant "rule_1242"
	(CurCmd = ReqE & InvSet[j] = false -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE do
Invariant "rule_89"
	(Cache[i].State = E -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1511"
		(i != j) ->	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> Chan2[j].Cmd != GntS);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_258"
		(i != j) ->	(Chan3[j].Cmd = InvAck -> Cache[i].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_969"
		(i != j) ->	(Chan2[j].Cmd = Inv & CurCmd = ReqS -> Cache[i].State != S);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1280"
		(i != j) ->	(Chan3[i].Cmd != Empty & Cache[j].State != I -> MemData = AuxData);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_984"
		(i != j) ->	(Chan2[i].Data = AuxData & Chan2[j].Cmd != Empty -> ExGntd = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_616"
		(i != j) ->	(ShrSet[i] = true & MemData != AuxData -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_894"
		(i != j) ->	(Chan2[i].Data = AuxData & Cache[j].Data = AuxData -> Cache[j].State = S);
endruleset;


ruleset j : NODE do
Invariant "rule_56"
	(Chan2[j].Cmd = GntE -> ExGntd = true);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1396"
		(i != j) ->	(CurCmd = ReqS & Chan2[i].Cmd = Inv -> Cache[j].State = I);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_773"
		(i != j) ->	(ShrSet[i] = true & Chan3[j].Cmd != Empty -> MemData = AuxData);
endruleset;


ruleset j : NODE do
Invariant "rule_1459"
	(Chan2[j].Cmd = Inv & Cache[j].State = S -> CurCmd = ReqE);
endruleset;


ruleset j : NODE do
Invariant "rule_977"
	(ExGntd = true & Cache[j].Data = AuxData -> Cache[j].State = E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_10"
		(i != j) ->	(Chan2[i].Cmd = GntS -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_328"
		(i != j) ->	(Chan3[i].Cmd != Empty -> Cache[j].State != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_384"
		(i != j) ->	(ShrSet[j] = true & MemData != AuxData -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_1560"
		(i != j) ->	(Cache[j].State != I & Cache[j].State != S -> Chan2[i].Cmd != Inv);
endruleset;


ruleset i : NODE do
Invariant "rule_238"
	(Chan2[i].Data = AuxData -> Chan2[i].Cmd != Empty);
endruleset;
