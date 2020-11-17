
const

  NODE_NUM : 3;
  DATA_NUM : 2;

type

  NODE : scalarset(NODE_NUM);
  DATA : scalarset(DATA_NUM);

  ABS_NODE : union {NODE, enum{Other}};

  CACHE_STATE : enum {CACHE_I, CACHE_S, CACHE_E};

  NODE_CMD : enum {NODE_None, NODE_Get, NODE_GetX};

  NODE_STATE : record
    ProcCmd : NODE_CMD;
    InvMarked : boolean;
    CacheState : CACHE_STATE;
    CacheData : DATA;
  end;

  DIR_STATE : record
    Pending : boolean;
    Local : boolean;
    Dirty : boolean;
    HeadVld : boolean;
    HeadPtr : ABS_NODE;
    ShrVld : boolean;
    ShrSet : array [NODE] of boolean;
    InvSet : array [NODE] of boolean;
  end;

  UNI_CMD : enum {UNI_None, UNI_Get, UNI_GetX, UNI_Put, UNI_PutX, UNI_Nak};

  UNI_MSG : record
    Cmd : UNI_CMD;
    Proc : ABS_NODE;
    Data : DATA;
  end;

  INV_CMD : enum {INV_None, INV_Inv, INV_InvAck};

  INV_MSG : record
    Cmd : INV_CMD;
  end;

  RP_CMD : enum {RP_None, RP_Replace};

  RP_MSG : record
    Cmd : RP_CMD;
  end;

  WB_CMD : enum {WB_None, WB_Wb};

  WB_MSG : record
    Cmd : WB_CMD;
    Proc : ABS_NODE;
    Data : DATA;
  end;

  SHWB_CMD : enum {SHWB_None, SHWB_ShWb, SHWB_FAck};

  SHWB_MSG : record
    Cmd : SHWB_CMD;
    Proc : ABS_NODE;
    Data : DATA;
  end;

  NAKC_CMD : enum {NAKC_None, NAKC_Nakc};

  NAKC_MSG : record
    Cmd : NAKC_CMD;
  end;

  STATE : record
  -- Program variables:
    Proc : array [NODE] of NODE_STATE;
    Dir : DIR_STATE;
    MemData : DATA;
    UniMsg : array [NODE] of UNI_MSG;
    InvMsg : array [NODE] of INV_MSG;
    RpMsg : array [NODE] of RP_MSG;
    WbMsg : WB_MSG;
    ShWbMsg : SHWB_MSG;
    NakcMsg : NAKC_MSG;
  -- Auxiliary variables:
    CurrData : DATA;
    PrevData : DATA;
    LastWrVld : boolean;
    LastWrPtr : ABS_NODE;
    PendReqSrc : ABS_NODE;
    PendReqCmd : UNI_CMD;
    Collecting : boolean;
    FwdCmd : UNI_CMD;
    FwdSrc : ABS_NODE;
    LastInvAck : ABS_NODE;
    LastOtherInvAck : ABS_NODE;
  end;

var

  Home : NODE;
  Sta : STATE;

ruleset  src : NODE do
rule "NI_Replace1"
  Sta.RpMsg[src].Cmd = RP_Replace &
  Sta.Dir.ShrVld = true
==>
begin
  Sta.RpMsg[src].Cmd := RP_None;
  Sta.Dir.ShrSet[src] := false;
  Sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Replace2"
  Sta.RpMsg[src].Cmd = RP_Replace &
  Sta.Dir.ShrVld = false
==>
begin
  Sta.RpMsg[src].Cmd := RP_None;
endrule;
endruleset;

rule "NI_ShWb3"
  Sta.ShWbMsg.Cmd = SHWB_ShWb
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.ShrVld := true;
  for p : NODE do
    Sta.Dir.InvSet[p] := (p = Sta.ShWbMsg.Proc |
    Sta.Dir.ShrSet[p] = true);
    Sta.Dir.ShrSet[p] := (p = Sta.ShWbMsg.Proc |
    Sta.Dir.ShrSet[p] = true);
  endfor;
  Sta.MemData := Sta.ShWbMsg.Data;
  undefine Sta.ShWbMsg.Proc;
  undefine Sta.ShWbMsg.Data;
endrule;

rule "NI_FAck4"
  Sta.ShWbMsg.Cmd = SHWB_FAck &
  Sta.Dir.Dirty = true
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  Sta.Dir.HeadPtr := Sta.ShWbMsg.Proc;
  undefine Sta.ShWbMsg.Proc;
  undefine Sta.ShWbMsg.Data;
endrule;

rule "NI_FAck5"
  Sta.ShWbMsg.Cmd = SHWB_FAck &
  Sta.Dir.Dirty = false
==>
begin
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.Dir.Pending := false;
  undefine Sta.ShWbMsg.Proc;
  undefine Sta.ShWbMsg.Data;
endrule;

rule "NI_Wb6"
  Sta.WbMsg.Cmd = WB_Wb
==>
begin
  Sta.WbMsg.Cmd := WB_None;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.MemData := Sta.WbMsg.Data;
  undefine Sta.WbMsg.Proc;
  undefine Sta.WbMsg.Data;
  undefine Sta.Dir.HeadPtr;
endrule;

ruleset  src : NODE do
rule "NI_InvAck_no_exists7"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  Sta.Dir.InvSet[Home] = false &
  forall p : NODE do
    p = src |
    Sta.Dir.InvSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Dir.Dirty = false
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Collecting := false;
  Sta.LastInvAck := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_InvAck_no_exists8"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  Sta.Dir.InvSet[Home] = false &
  forall p : NODE do
    p = src | Sta.Dir.InvSet[p] = false
  end &
  Sta.Dir.Local = false
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
  Sta.Dir.Pending := false;
  Sta.Collecting := false;
  Sta.LastInvAck := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_InvAck_no_exists9"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  Sta.Dir.InvSet[Home] = false &
  forall p : NODE do
    p = src |
    Sta.Dir.InvSet[p] = false
  end &
  Sta.Dir.Dirty = true
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.Dir.InvSet[src] := false;
  Sta.Dir.Pending := false;
  Sta.Collecting := false;
  Sta.LastInvAck := src;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_InvAck_exists10"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  dst != src &
  Sta.Dir.InvSet[dst] = true
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.LastInvAck := src;
  for p : NODE do
    if (p != src & Sta.Dir.InvSet[p] = true) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  Sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_InvAck_exists_Home11"
  Sta.InvMsg[src].Cmd = INV_InvAck &
  Sta.Dir.Pending = true &
  Sta.Dir.InvSet[src] = true &
  Sta.Dir.InvSet[Home] = true
==>
begin
  Sta.InvMsg[src].Cmd := INV_None;
  Sta.LastInvAck := src;
  for p : NODE do
    if ((p != src & Sta.Dir.InvSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  Sta.Dir.InvSet[src] := false;
endrule;
endruleset;

ruleset  dst : NODE do
rule "NI_Inv12"
  dst != Home &
  Sta.InvMsg[dst].Cmd = INV_Inv &
  Sta.Proc[dst].ProcCmd = NODE_Get
==>
begin
  Sta.InvMsg[dst].Cmd := INV_InvAck;
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.Proc[dst].InvMarked := true;
  undefine Sta.Proc[dst].CacheData;
endrule;
endruleset;

ruleset  dst : NODE do
rule "NI_Inv13"
  dst != Home &
  Sta.InvMsg[dst].Cmd = INV_Inv &
  Sta.Proc[dst].ProcCmd != NODE_Get
==>
begin
  Sta.InvMsg[dst].Cmd := INV_InvAck;
  Sta.Proc[dst].CacheState := CACHE_I;
  undefine Sta.Proc[dst].CacheData;
endrule;
endruleset;

ruleset  dst : NODE do
rule "NI_Remote_PutX14"
  dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_PutX &
  Sta.Proc[dst].ProcCmd = NODE_GetX
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].InvMarked := false;
  Sta.Proc[dst].CacheState := CACHE_E;
  Sta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
  undefine Sta.UniMsg[dst].Proc;
  undefine Sta.UniMsg[dst].Data;
endrule;
endruleset;

rule "NI_Local_PutXAcksDone15"
  Sta.UniMsg[Home].Cmd = UNI_PutX
==>
begin
  Sta.UniMsg[Home].Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := true;
  Sta.Dir.HeadVld := false;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
  Sta.Proc[Home].CacheData := Sta.UniMsg[Home].Data;
  undefine Sta.UniMsg[Home].Proc;
  undefine Sta.UniMsg[Home].Data;
  undefine Sta.Dir.HeadPtr;
endrule;

ruleset  dst : NODE do
rule "NI_Remote_Put16"
  dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_Put &
  Sta.Proc[dst].InvMarked = true
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].InvMarked := false;
  Sta.Proc[dst].CacheState := CACHE_I;
  undefine Sta.Proc[dst].CacheData;
  undefine Sta.UniMsg[dst].Proc;
  undefine Sta.UniMsg[dst].Data;
endrule;
endruleset;

ruleset  dst : NODE do
rule "NI_Remote_Put17"
  dst != Home &
  Sta.UniMsg[dst].Cmd = UNI_Put &
  Sta.Proc[dst].InvMarked = false
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].CacheState := CACHE_S;
  Sta.Proc[dst].CacheData := Sta.UniMsg[dst].Data;
  undefine Sta.UniMsg[dst].Proc;
  undefine Sta.UniMsg[dst].Data;
endrule;
endruleset;

rule "NI_Local_Put18"
  Sta.UniMsg[Home].Cmd = UNI_Put &
  Sta.Proc[Home].InvMarked = true
==>
begin
  Sta.UniMsg[Home].Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.Local := true;
  Sta.MemData := Sta.UniMsg[Home].Data;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  undefine Sta.UniMsg[Home].Proc;
  undefine Sta.UniMsg[Home].Data;
endrule;

rule "NI_Local_Put19"
  Sta.UniMsg[Home].Cmd = UNI_Put &
  Sta.Proc[Home].InvMarked = false
==>
begin
  Sta.UniMsg[Home].Cmd := UNI_None;
  Sta.Dir.Pending := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.Local := true;
  Sta.MemData := Sta.UniMsg[Home].Data;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].CacheState := CACHE_S;
  Sta.Proc[Home].CacheData := Sta.UniMsg[Home].Data;
  undefine Sta.UniMsg[Home].Proc;
  undefine Sta.UniMsg[Home].Data;
endrule;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_GetX_PutX20"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E &
  src != Home
==>
begin
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := dst;
  Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  Sta.ShWbMsg.Cmd := SHWB_FAck;
  Sta.ShWbMsg.Proc := src;
  undefine Sta.ShWbMsg.Data;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
  undefine Sta.Proc[dst].CacheData;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_GetX_PutX21"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E &
  src = Home
==>
begin
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := dst;
  Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
  undefine Sta.Proc[dst].CacheData;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_GetX_Nak22"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := dst;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX23"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = true
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX24"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = true
==>
begin
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX25"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX26"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX27"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Proc[Home].ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX28"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX29"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX30"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX31"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Proc[Home].ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX32"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX33"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX34"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX35"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX36"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadPtr = src &
  forall p : NODE do
    p != src ->
    Sta.Dir.ShrSet[p] = false
  end &
  Sta.Dir.Local = false
==>
begin
  Sta.Dir.Dirty := true;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.Dir.ShrVld := false;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
  endfor;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX37"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home & p != src) & ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) | (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p))
    then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX38"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX39"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX40"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX41"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX42"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX43"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX44"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd = NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Proc[Home].InvMarked := true;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX45"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX46"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX47"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX48"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX49"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX50"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX51"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX52"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = true &
  Sta.Proc[Home].ProcCmd != NODE_Get &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX53"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX54"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX55"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX56"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX57"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX58"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX59"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_PutX60"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true &
  exists p : NODE do
    !(p != src -> Sta.Dir.ShrSet[p] = false)
  end &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.Dir.Pending := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if (p != Home &
    p != src) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
  endfor;
  Sta.Dir.ShrVld := false;
  Sta.Dir.HeadVld := true;
  Sta.UniMsg[src].Cmd := UNI_PutX;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
  Sta.Dir.Local := false;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  for p : NODE do
    if ((p != src &
    Sta.Dir.ShrSet[p] = true)) then
      Sta.LastOtherInvAck := p;
    endif;
  endfor;
  for p : NODE do
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.HeadPtr := src;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_GetX61"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_GetX;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.FwdCmd := UNI_GetX;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_GetX62"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_GetX;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_Nak63"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Pending = true
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_Nak64"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_GetX_Nak65"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_GetX &
  Sta.UniMsg[src].Proc = Home &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_Get_Put66"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E &
  src != Home
==>
begin
  Sta.Proc[dst].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := dst;
  Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  Sta.ShWbMsg.Cmd := SHWB_ShWb;
  Sta.ShWbMsg.Proc := src;
  Sta.ShWbMsg.Data := Sta.Proc[dst].CacheData;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_Get_Put67"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState = CACHE_E &
  src = Home
==>
begin
  Sta.Proc[dst].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := dst;
  Sta.UniMsg[src].Data := Sta.Proc[dst].CacheData;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
endrule;
endruleset;

ruleset  dst : NODE; src : NODE do
rule "NI_Remote_Get_Nak68"
  src != dst &
  dst != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = dst &
  Sta.Proc[dst].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := dst;
  Sta.NakcMsg.Cmd := NAKC_Nakc;
  Sta.FwdCmd := UNI_None;
  Sta.FwdSrc := src;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put69"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = true
==>
begin
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.MemData := Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put70"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = true
==>
begin
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.MemData := Sta.Proc[Home].CacheData;
  Sta.Proc[Home].CacheState := CACHE_S;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.Proc[Home].CacheData;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put71"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.ShrVld := true;
  Sta.Dir.ShrSet[src] := true;
  for p : NODE do
    Sta.Dir.InvSet[p] := (p = src |
    Sta.Dir.ShrSet[p] = true);
  endfor;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put72"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.ShrVld := true;
  Sta.Dir.ShrSet[src] := true;
  for p : NODE do
    Sta.Dir.InvSet[p] := (p = src |
    Sta.Dir.ShrSet[p] = true);
  endfor;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put73"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false
==>
begin
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Put74"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false
==>
begin
  Sta.Dir.HeadVld := true;
  Sta.Dir.HeadPtr := src;
  Sta.UniMsg[src].Cmd := UNI_Put;
  Sta.UniMsg[src].Proc := Home;
  Sta.UniMsg[src].Data := Sta.MemData;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Get75"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_Get;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.FwdCmd := UNI_Get;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_Get;
  Sta.Collecting := false;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Get76"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr != src &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Dir.Pending := true;
  Sta.UniMsg[src].Cmd := UNI_Get;
  Sta.UniMsg[src].Proc := Sta.Dir.HeadPtr;
  Sta.PendReqSrc := src;
  Sta.PendReqCmd := UNI_Get;
  Sta.Collecting := false;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Nak77"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Pending = true
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Nak78"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = true &
  Sta.Proc[Home].CacheState != CACHE_E
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

ruleset  src : NODE do
rule "NI_Local_Get_Nak79"
  src != Home &
  Sta.UniMsg[src].Cmd = UNI_Get &
  Sta.UniMsg[src].Proc = Home &
  Sta.RpMsg[src].Cmd != RP_Replace &
  Sta.Dir.Dirty = true &
  Sta.Dir.Local = false &
  Sta.Dir.HeadPtr = src
==>
begin
  Sta.UniMsg[src].Cmd := UNI_Nak;
  Sta.UniMsg[src].Proc := Home;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

rule "NI_Nak_Clear80"
  Sta.NakcMsg.Cmd = NAKC_Nakc
==>
begin
  Sta.NakcMsg.Cmd := NAKC_None;
  Sta.Dir.Pending := false;
endrule;

ruleset  dst : NODE do
rule "NI_Nak81"
  Sta.UniMsg[dst].Cmd = UNI_Nak
==>
begin
  Sta.UniMsg[dst].Cmd := UNI_None;
  Sta.Proc[dst].ProcCmd := NODE_None;
  Sta.Proc[dst].InvMarked := false;
  undefine Sta.UniMsg[dst].Proc;
  undefine Sta.UniMsg[dst].Data;
endrule;
endruleset;

rule "PI_Local_Replace82"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S
==>
begin
  Sta.Dir.Local := false;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
endrule;

ruleset  src : NODE do
rule "PI_Remote_Replace83"
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_S
==>
begin
  Sta.Proc[src].CacheState := CACHE_I;
  Sta.RpMsg[src].Cmd := RP_Replace;
  undefine Sta.Proc[src].CacheData;
endrule;
endruleset;

rule "PI_Local_PutX84"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Pending = true
==>
begin
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Dirty := false;
  Sta.MemData := Sta.Proc[Home].CacheData;
  undefine Sta.Proc[Home].CacheData;
endrule;

rule "PI_Local_PutX85"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_E &
  Sta.Dir.Pending = false
==>
begin
  Sta.Proc[Home].CacheState := CACHE_I;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.MemData := Sta.Proc[Home].CacheData;
  undefine Sta.Proc[Home].CacheData;
endrule;

ruleset  dst : NODE do
rule "PI_Remote_PutX86"
  dst != Home &
  Sta.Proc[dst].ProcCmd = NODE_None &
  Sta.Proc[dst].CacheState = CACHE_E
==>
begin
  Sta.Proc[dst].CacheState := CACHE_I;
  Sta.WbMsg.Cmd := WB_Wb;
  Sta.WbMsg.Proc := dst;
  Sta.WbMsg.Data := Sta.Proc[dst].CacheData;
  undefine Sta.Proc[dst].CacheData;
endrule;
endruleset;

rule "PI_Local_GetX_PutX87"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if ((p != Home &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.Pending := true;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  undefine Sta.Dir.HeadPtr;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
  Sta.Proc[Home].CacheData := Sta.MemData;
endrule;

rule "PI_Local_GetX_PutX88"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = true
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  for p : NODE do
    if ((p != Home &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[p] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = p)))) then
      Sta.Dir.InvSet[p] := true;
      Sta.InvMsg[p].Cmd := INV_Inv;
    else
      Sta.Dir.InvSet[p] := false;
      Sta.InvMsg[p].Cmd := INV_None;
    endif;
    Sta.Dir.ShrSet[p] := false;
  endfor;
  Sta.Dir.Pending := true;
  Sta.Collecting := true;
  Sta.PrevData := Sta.CurrData;
  Sta.LastOtherInvAck := Sta.Dir.HeadPtr;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  undefine Sta.Dir.HeadPtr;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
  Sta.Proc[Home].CacheData := Sta.MemData;
endrule;

rule "PI_Local_GetX_PutX89"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
  Sta.Proc[Home].CacheData := Sta.MemData;
endrule;

rule "PI_Local_GetX_PutX90"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Dir.HeadVld = false
==>
begin
  Sta.Dir.Local := true;
  Sta.Dir.Dirty := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_E;
  Sta.Proc[Home].CacheData := Sta.MemData;
endrule;

rule "PI_Local_GetX_GetX91"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_GetX;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.FwdCmd := UNI_GetX;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
  undefine Sta.UniMsg[Home].Data;
endrule;

rule "PI_Local_GetX_GetX92"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_GetX;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.FwdCmd := UNI_GetX;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
  undefine Sta.UniMsg[Home].Data;
endrule;

rule "PI_Local_GetX_GetX93"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_GetX;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
  undefine Sta.UniMsg[Home].Data;
endrule;

rule "PI_Local_GetX_GetX94"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_S &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_GetX;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_GetX;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_GetX;
  Sta.Collecting := false;
  undefine Sta.UniMsg[Home].Data;
endrule;

ruleset  src : NODE do
rule "PI_Remote_GetX95"
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
begin
  Sta.Proc[src].ProcCmd := NODE_GetX;
  Sta.UniMsg[src].Cmd := UNI_GetX;
  Sta.UniMsg[src].Proc := Home;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;

rule "PI_Local_Get_Put96"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Proc[Home].InvMarked = true
==>
begin
  Sta.Dir.Local := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].InvMarked := false;
  Sta.Proc[Home].CacheState := CACHE_I;
  undefine Sta.Proc[Home].CacheData;
endrule;

rule "PI_Local_Get_Put97"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = false &
  Sta.Proc[Home].InvMarked = false
==>
begin
  Sta.Dir.Local := true;
  Sta.Proc[Home].ProcCmd := NODE_None;
  Sta.Proc[Home].CacheState := CACHE_S;
  Sta.Proc[Home].CacheData := Sta.MemData;
endrule;

rule "PI_Local_Get_Get98"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr != Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_Get;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_Get;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  undefine Sta.UniMsg[Home].Data;
  Sta.FwdCmd := UNI_Get;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_Get;
  Sta.Collecting := false;
endrule;

rule "PI_Local_Get_Get99"
  Sta.Proc[Home].ProcCmd = NODE_None &
  Sta.Proc[Home].CacheState = CACHE_I &
  Sta.Dir.Pending = false &
  Sta.Dir.Dirty = true &
  Sta.Dir.HeadPtr = Home
==>
begin
  Sta.Proc[Home].ProcCmd := NODE_Get;
  Sta.Dir.Pending := true;
  Sta.UniMsg[Home].Cmd := UNI_Get;
  Sta.UniMsg[Home].Proc := Sta.Dir.HeadPtr;
  undefine Sta.UniMsg[Home].Data;
  Sta.PendReqSrc := Home;
  Sta.PendReqCmd := UNI_Get;
  Sta.Collecting := false;
endrule;

ruleset  src : NODE do
rule "PI_Remote_Get100"
  src != Home &
  Sta.Proc[src].ProcCmd = NODE_None &
  Sta.Proc[src].CacheState = CACHE_I
==>
begin
  Sta.Proc[src].ProcCmd := NODE_Get;
  Sta.UniMsg[src].Cmd := UNI_Get;
  Sta.UniMsg[src].Proc := Home;
  undefine Sta.UniMsg[src].Data;
endrule;
endruleset;


ruleset  src : NODE; data : DATA  do
rule "Store101"
  Sta.Proc[src].CacheState = CACHE_E
==>
begin
  Sta.Proc[src].CacheData := data;
  Sta.CurrData := data;
  Sta.LastWrVld := true;
  Sta.LastWrPtr := src;
endrule;
endruleset;

ruleset  h : NODE; d : DATA do
startstate
  Home := h;
  undefine Sta;
  Sta.MemData := d;
  Sta.Dir.Pending := false;
  Sta.Dir.Local := false;
  Sta.Dir.Dirty := false;
  Sta.Dir.HeadVld := false;
  Sta.Dir.ShrVld := false;
  Sta.WbMsg.Cmd := WB_None;
  Sta.ShWbMsg.Cmd := SHWB_None;
  Sta.NakcMsg.Cmd := NAKC_None;
  for p : NODE do
    Sta.Proc[p].ProcCmd := NODE_None;
    Sta.Proc[p].InvMarked := false;
    Sta.Proc[p].CacheState := CACHE_I;
    Sta.Dir.ShrSet[p] := false;
    Sta.Dir.InvSet[p] := false;
    Sta.UniMsg[p].Cmd := UNI_None;
    Sta.InvMsg[p].Cmd := INV_None;
    Sta.RpMsg[p].Cmd := RP_None;
  endfor;
  Sta.CurrData := d;
  Sta.PrevData := d;
  Sta.LastWrVld := false;
  Sta.Collecting := false;
  Sta.FwdCmd := UNI_None;
endstartstate;
endruleset;

invariant "CacheStateProp"
  forall p : NODE do
    forall q : NODE do
      (p != q ->
      !(Sta.Proc[p].CacheState = CACHE_E &
      Sta.Proc[q].CacheState = CACHE_E))
    end
  end;

invariant "CacheDataPropE"
  forall p : NODE do
    (Sta.Proc[p].CacheState = CACHE_E ->
    Sta.Proc[p].CacheData = Sta.CurrData)
  end;

invariant "CacheDataPropSNC"
  forall p : NODE do
    (Sta.Proc[p].CacheState = CACHE_S ->
    (Sta.Collecting = false ->
    Sta.Proc[p].CacheData = Sta.CurrData))
  end;

invariant "CacheDataPropSC"
  forall p : NODE do
    (Sta.Proc[p].CacheState = CACHE_S ->
    (Sta.Collecting = true ->
    Sta.Proc[p].CacheData = Sta.PrevData))
  end;

invariant "MemDataProp"
  (Sta.Dir.Dirty = false ->
  Sta.MemData = Sta.CurrData);



-- No abstract rule for rule NI_Replace1



-- No abstract rule for rule NI_Replace2


rule "ABS_NI_InvAck_no_exists7_NODE_1"

	Sta.Dir.Pending = true &
	Sta.Dir.InvSet[Home] = false &
	Sta.Dir.Local = true &
	Sta.Dir.Dirty = false
	& forall NODE_2 : NODE do
			NODE_2 = Other |
    Sta.Dir.InvSet[NODE_2] = false
	end
 	& 
	forall NODE_1 : NODE; NODE_2 : NODE do
		Sta.Collecting = true &
		 &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := false ;
	Sta.Dir.Local := false ;
	Sta.Collecting := false ;
	Sta.LastInvAck := Other;
endrule;
rule "ABS_NI_InvAck_no_exists8_NODE_1"

	Sta.Dir.Pending = true &
	Sta.Dir.InvSet[Home] = false &
	Sta.Dir.Local = false
	& forall NODE_2 : NODE do
			NODE_2 = Other | Sta.Dir.InvSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		Sta.Collecting = true &
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.MemData = Sta.PrevData &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.PendReqSrc = NODE_2 &
		Sta.PendReqSrc != NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := false ;
	Sta.Collecting := false ;
	Sta.LastInvAck := Other;
endrule;
rule "ABS_NI_InvAck_no_exists9_NODE_1"

	Sta.Dir.Pending = true &
	Sta.Dir.InvSet[Home] = false &
	Sta.Dir.Dirty = true
	& forall NODE_2 : NODE do
			NODE_2 = Other |
    Sta.Dir.InvSet[NODE_2] = false
	end
 	& 
	forall NODE_1 : NODE; NODE_2 : NODE do
		Sta.Collecting = true &
		 &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.MemData = Sta.PrevData &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.Dir.Local = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := false ;
	Sta.Collecting := false ;
	Sta.LastInvAck := Other;
endrule;

ruleset NODE_2 : NODE do
rule "ABS_NI_InvAck_exists10_NODE_1"

	Sta.InvMsg[NODE_2].Cmd = INV_InvAck &
	Sta.Dir.Pending = true &
	Sta.Dir.InvSet[NODE_2] = true &
	Other != NODE_2
 	& 
	forall NODE_1 : NODE do
		Sta.Collecting = true &
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.Dir.Local = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.InvMsg[NODE_2].Cmd := INV_None ;
	Sta.LastInvAck := NODE_2 ;
	Sta.Dir.InvSet[NODE_2] := false;
	for NODE_3 : NODE do
		if (NODE_3 != NODE_2 & Sta.Dir.InvSet[NODE_3] = true) then
      Sta.LastOtherInvAck := NODE_3 ;
		endif
 ;
	endfor;
endrule;
endruleset;


ruleset NODE_1 : NODE do
rule "ABS_NI_InvAck_exists10_NODE_2"

	Sta.Dir.Pending = true &
	Other != Other
 	& 
	forall NODE_2 : NODE do
		Sta.Collecting = true &
		 &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.Dir.Local = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.LastInvAck := Other;
	for NODE_3 : NODE do
		if (NODE_3 != Other & Sta.Dir.InvSet[NODE_3] = true) then
      Sta.LastOtherInvAck := NODE_3 ;
		endif
 ;
	endfor;
endrule;
endruleset;

rule "ABS_NI_InvAck_exists10_NODE_1_NODE_2"

	Sta.Dir.Pending = true &
	Other != Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		Sta.Collecting = true &
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.Dir.Local = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.LastInvAck := Other;
	for NODE_3 : NODE do
		if (NODE_3 != Other & Sta.Dir.InvSet[NODE_3] = true) then
      Sta.LastOtherInvAck := NODE_3 ;
		endif
 ;
	endfor;
endrule;
rule "ABS_NI_InvAck_exists_Home11_NODE_1"

	Sta.Dir.Pending = true &
	Sta.Dir.InvSet[Home] = true
 	& 
	forall NODE_1 : NODE; NODE_2 : NODE do
		Sta.Collecting = true &
		 &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.LastInvAck := Other;
	for NODE_2 : NODE do
		if ((NODE_2 != Other & Sta.Dir.InvSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
endrule;

-- No abstract rule for rule NI_Inv12



-- No abstract rule for rule NI_Inv13



-- No abstract rule for rule NI_Remote_PutX14



-- No abstract rule for rule NI_Remote_Put16



-- No abstract rule for rule NI_Remote_Put17



ruleset NODE_2 : NODE do
rule "ABS_NI_Remote_GetX_PutX20_NODE_1"

	NODE_2 != Other &
	Other != Home &
	Sta.UniMsg[NODE_2].Cmd = UNI_GetX &
	Sta.UniMsg[NODE_2].Proc = Other &
	NODE_2 != Home
 	& 
	forall NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].ProcCmd != NODE_Get &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.ShrVld = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_2].Proc = Home &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_GetX &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd != UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.FwdCmd = UNI_GetX &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.UniMsg[NODE_2].Cmd := UNI_PutX ;
	Sta.UniMsg[NODE_2].Proc := Other ;
	Sta.UniMsg[NODE_2].Data := Sta.CurrData ;
	Sta.ShWbMsg.Cmd := SHWB_FAck ;
	Sta.ShWbMsg.Proc := NODE_2 ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := NODE_2;
endrule;
endruleset;


ruleset NODE_1 : NODE do
rule "ABS_NI_Remote_GetX_PutX20_NODE_2"

	Other != Other &
	Other != Home &
	Other != Home
 	& 
	forall NODE_2 : NODE do
		Sta.Proc[NODE_1].ProcCmd = NODE_None &
		 &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.PendReqSrc = NODE_1 &
		Sta.Proc[NODE_1].CacheData = Sta.CurrData &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.ShrVld = false &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[NODE_1].ProcCmd != NODE_GetX &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.UniMsg[NODE_1].Cmd != UNI_Nak &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd != UNI_None &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd = UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.Dir.HeadVld = true &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.FwdCmd = UNI_GetX &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.UniMsg[NODE_1].Cmd != UNI_Get &
		Sta.UniMsg[NODE_1].Cmd != UNI_GetX &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Proc[NODE_1].ProcCmd != NODE_Get &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.ShWbMsg.Cmd := SHWB_FAck ;
	Sta.ShWbMsg.Proc := Other ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;
endruleset;

rule "ABS_NI_Remote_GetX_PutX20_NODE_1_NODE_2"

	Other != Other &
	Other != Home &
	Other != Home
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].ProcCmd != NODE_Get &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Proc = Home &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd = UNI_GetX &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.PendReqSrc != NODE_1 &
		Sta.UniMsg[NODE_1].Cmd != UNI_Get &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.FwdCmd != UNI_GetX &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[NODE_1].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.UniMsg[NODE_1].Cmd != UNI_Nak &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd != UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.Dir.Dirty = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.UniMsg[NODE_1].Cmd != UNI_GetX &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Proc[NODE_1].CacheData = Sta.CurrData &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_1].ProcCmd != NODE_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_GetX &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.Dir.HeadVld = true &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Proc[NODE_1].ProcCmd != NODE_Get &
		Sta.Dir.Dirty = true
	end
==>
begin
	Sta.ShWbMsg.Cmd := SHWB_FAck ;
	Sta.ShWbMsg.Proc := Other ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;

ruleset NODE_2 : NODE do
rule "ABS_NI_Remote_GetX_PutX21_NODE_1"

	NODE_2 != Other &
	Other != Home &
	Sta.UniMsg[NODE_2].Cmd = UNI_GetX &
	Sta.UniMsg[NODE_2].Proc = Other &
	NODE_2 = Home
 	& 
	forall NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].ProcCmd != NODE_Get &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.ShrVld = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_2].Proc = Home &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_GetX &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd != UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.FwdCmd = UNI_GetX &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.UniMsg[NODE_2].Cmd := UNI_PutX ;
	Sta.UniMsg[NODE_2].Proc := Other ;
	Sta.UniMsg[NODE_2].Data := Sta.CurrData ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := NODE_2;
endrule;
endruleset;


ruleset NODE_1 : NODE do
rule "ABS_NI_Remote_GetX_PutX21_NODE_2"

	Other != Other &
	Other != Home &
	Other = Home
 	& 
	forall NODE_2 : NODE do
		Sta.Proc[NODE_1].ProcCmd = NODE_None &
		 &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.PendReqSrc = NODE_1 &
		Sta.Proc[NODE_1].CacheData = Sta.CurrData &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.ShrVld = false &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[NODE_1].ProcCmd != NODE_GetX &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.UniMsg[NODE_1].Cmd != UNI_Nak &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd != UNI_None &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd = UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.Dir.HeadVld = true &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.FwdCmd = UNI_GetX &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.UniMsg[NODE_1].Cmd != UNI_Get &
		Sta.UniMsg[NODE_1].Cmd != UNI_GetX &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Proc[NODE_1].ProcCmd != NODE_Get &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;
endruleset;

rule "ABS_NI_Remote_GetX_PutX21_NODE_1_NODE_2"

	Other != Other &
	Other != Home &
	Other = Home
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].ProcCmd != NODE_Get &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Proc = Home &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd = UNI_GetX &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.PendReqSrc != NODE_1 &
		Sta.UniMsg[NODE_1].Cmd != UNI_Get &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.FwdCmd != UNI_GetX &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[NODE_1].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.UniMsg[NODE_1].Cmd != UNI_Nak &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd != UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.Dir.Dirty = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.UniMsg[NODE_1].Cmd != UNI_GetX &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Proc[NODE_1].CacheData = Sta.CurrData &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_1].ProcCmd != NODE_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_GetX &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.Dir.HeadVld = true &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Proc[NODE_1].ProcCmd != NODE_Get &
		Sta.Dir.Dirty = true
	end
==>
begin
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;

ruleset NODE_2 : NODE do
rule "ABS_NI_Remote_GetX_Nak22_NODE_1"

	NODE_2 != Other &
	Other != Home &
	Sta.UniMsg[NODE_2].Cmd = UNI_GetX &
	Sta.UniMsg[NODE_2].Proc = Other
 	& 
	forall NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].ProcCmd != NODE_Get &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.ShrVld = false &
		Sta.Collecting = false &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_GetX &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd != UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.Proc[Home].InvMarked = false &
		Sta.FwdCmd = UNI_GetX &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.PendReqSrc != NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.UniMsg[NODE_2].Cmd := UNI_Nak ;
	Sta.UniMsg[NODE_2].Proc := Other ;
	Sta.NakcMsg.Cmd := NAKC_Nakc ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := NODE_2;
endrule;
endruleset;


ruleset NODE_1 : NODE do
rule "ABS_NI_Remote_GetX_Nak22_NODE_2"

	Other != Other &
	Other != Home
 	& 
	forall NODE_2 : NODE do
		 &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.ShrVld = false &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd != UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.Proc[Home].InvMarked = false &
		Sta.FwdCmd = UNI_GetX &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.PendReqSrc != NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.NakcMsg.Cmd := NAKC_Nakc ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;
endruleset;

rule "ABS_NI_Remote_GetX_Nak22_NODE_1_NODE_2"

	Other != Other &
	Other != Home
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].ProcCmd != NODE_Get &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.ShrVld = false &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.Collecting = false &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_GetX &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd != UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.Proc[Home].InvMarked = false &
		Sta.FwdCmd = UNI_GetX &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.PendReqSrc != NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.NakcMsg.Cmd := NAKC_Nakc ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;
rule "ABS_NI_Local_GetX_PutX23_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = true
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Local := false ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX24_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = true
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Local := false ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX25_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].InvMarked := true ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX26_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadPtr = Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get
	& forall NODE_2 : NODE do
			NODE_2 != Other ->
    Sta.Dir.ShrSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].InvMarked := true ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX27_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = false &
	Sta.Proc[Home].ProcCmd = NODE_Get
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].InvMarked := true ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX28_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadPtr = Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get
	& forall NODE_2 : NODE do
			NODE_2 != Other ->
    Sta.Dir.ShrSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].InvMarked := true ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX29_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX30_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadPtr = Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get
	& forall NODE_2 : NODE do
			NODE_2 != Other ->
    Sta.Dir.ShrSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX31_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = false &
	Sta.Proc[Home].ProcCmd != NODE_Get
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX32_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadPtr = Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get
	& forall NODE_2 : NODE do
			NODE_2 != Other ->
    Sta.Dir.ShrSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX33_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = false &
	Sta.Dir.Local = false
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX34_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadPtr = Other &
	Sta.Dir.Local = false
	& forall NODE_2 : NODE do
			NODE_2 != Other ->
    Sta.Dir.ShrSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX35_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = false &
	Sta.Dir.Local = false
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX36_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadPtr = Other &
	Sta.Dir.Local = false
	& forall NODE_2 : NODE do
			NODE_2 != Other ->
    Sta.Dir.ShrSet[NODE_2] = false
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.Dir.ShrVld := false ;
	Sta.Proc[Home].CacheState := CACHE_I ;
	Sta.Dir.Local := false;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		Sta.Dir.InvSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX37_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get &
	Sta.Dir.HeadPtr != Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home & NODE_2 != Other) & ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) | (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2))
    then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX38_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get &
	Sta.Dir.HeadPtr != Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX39_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get &
	Sta.Dir.HeadPtr != Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX40_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get &
	Sta.Dir.HeadPtr != Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX41_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get &
	Sta.Dir.HeadPtr = Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX42_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get &
	Sta.Dir.HeadPtr = Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX43_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get &
	Sta.Dir.HeadPtr = Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX44_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd = NODE_Get &
	Sta.Dir.HeadPtr = Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX45_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get &
	Sta.Dir.HeadPtr != Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX46_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get &
	Sta.Dir.HeadPtr != Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX47_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get &
	Sta.Dir.HeadPtr != Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX48_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get &
	Sta.Dir.HeadPtr != Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX49_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get &
	Sta.Dir.HeadPtr = Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX50_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get &
	Sta.Dir.HeadPtr = Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX51_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get &
	Sta.Dir.HeadPtr = Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX52_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = true &
	Sta.Proc[Home].ProcCmd != NODE_Get &
	Sta.Dir.HeadPtr = Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX53_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr != Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX54_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr != Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX55_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr != Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX56_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr != Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX57_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr = Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX58_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr = Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX59_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr = Other
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_PutX60_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr = Other	& exists NODE_2 : NODE do
		!(NODE_2 != Other -> Sta.Dir.ShrSet[NODE_2] = false)
	end
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.Dir.Dirty := true ;
	Sta.Dir.HeadPtr := Other;
	for NODE_2 : NODE do
		if (NODE_2 != Home &
    NODE_2 != Other) &
    ((Sta.Dir.ShrVld = true &
    Sta.Dir.ShrSet[NODE_2] = true) |
    (Sta.Dir.HeadVld = true &
    Sta.Dir.HeadPtr = NODE_2)) then
      Sta.Dir.InvSet[NODE_2] := true ;
		Sta.InvMsg[NODE_2].Cmd := INV_Inv ;
		else
      Sta.Dir.InvSet[NODE_2] := false ;
		Sta.InvMsg[NODE_2].Cmd := INV_None ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		if ((NODE_2 != Other &
    Sta.Dir.ShrSet[NODE_2] = true)) then
      Sta.LastOtherInvAck := NODE_2 ;
		endif
 ;
	endfor;
	for NODE_2 : NODE do
		Sta.Dir.ShrSet[NODE_2] := false ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_GetX_GetX61_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = true &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.HeadPtr != Home
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.FwdCmd := UNI_GetX ;
	Sta.PendReqSrc := Other ;
	Sta.PendReqCmd := UNI_GetX ;
	Sta.Collecting := false;
endrule;
rule "ABS_NI_Local_GetX_GetX62_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = true &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.HeadPtr = Home
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.PendReqSrc := Other ;
	Sta.PendReqCmd := UNI_GetX ;
	Sta.Collecting := false;
endrule;

-- No abstract rule for rule NI_Local_GetX_Nak63



-- No abstract rule for rule NI_Local_GetX_Nak64



-- No abstract rule for rule NI_Local_GetX_Nak65



ruleset NODE_2 : NODE do
rule "ABS_NI_Remote_Get_Put66_NODE_1"

	NODE_2 != Other &
	Other != Home &
	Sta.UniMsg[NODE_2].Cmd = UNI_Get &
	Sta.UniMsg[NODE_2].Proc = Other &
	NODE_2 != Home
 	& 
	forall NODE_1 : NODE do
		 &
		Sta.FwdCmd = UNI_Get &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.UniMsg[NODE_2].Proc = Home &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Collecting = false &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd != UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Dir.Dirty = false &
		Sta.Proc[NODE_2].ProcCmd != NODE_GetX &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.Proc[NODE_2].ProcCmd = NODE_Get &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.RpMsg[NODE_2].Cmd != RP_Replace &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.UniMsg[NODE_2].Cmd := UNI_Put ;
	Sta.UniMsg[NODE_2].Proc := Other ;
	Sta.UniMsg[NODE_2].Data := Sta.CurrData ;
	Sta.ShWbMsg.Cmd := SHWB_ShWb ;
	Sta.ShWbMsg.Proc := NODE_2 ;
	Sta.ShWbMsg.Data := Sta.CurrData ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := NODE_2;
endrule;
endruleset;


ruleset NODE_1 : NODE do
rule "ABS_NI_Remote_Get_Put66_NODE_2"

	Other != Other &
	Other != Home &
	Other != Home
 	& 
	forall NODE_2 : NODE do
		 &
		Sta.FwdCmd = UNI_Get &
		Sta.Proc[NODE_1].ProcCmd = NODE_None &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.PendReqSrc = NODE_1 &
		Sta.Proc[NODE_1].CacheData = Sta.CurrData &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[NODE_1].ProcCmd != NODE_GetX &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.UniMsg[NODE_1].Cmd != UNI_Nak &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd = UNI_None &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd != UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.Dir.Dirty = false &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.UniMsg[NODE_1].Cmd != UNI_Get &
		Sta.UniMsg[NODE_1].Cmd != UNI_GetX &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Proc[NODE_1].ProcCmd != NODE_Get &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.ShWbMsg.Cmd := SHWB_ShWb ;
	Sta.ShWbMsg.Proc := Other ;
	Sta.ShWbMsg.Data := Sta.CurrData ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;
endruleset;

rule "ABS_NI_Remote_Get_Put66_NODE_1_NODE_2"

	Other != Other &
	Other != Home &
	Other != Home
 	& 
	forall NODE_1 : NODE; NODE_2 : NODE do
		 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Proc = Home &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.PendReqSrc != NODE_2 &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.PendReqSrc != NODE_1 &
		Sta.UniMsg[NODE_1].Cmd != UNI_Get &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.FwdCmd = UNI_Get &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.FwdCmd != UNI_GetX &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.RpMsg[NODE_2].Cmd != RP_Replace &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[NODE_1].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.UniMsg[NODE_1].Cmd != UNI_Nak &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd != UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.Dir.Dirty = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.UniMsg[NODE_1].Cmd != UNI_GetX &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Proc[NODE_1].CacheData = Sta.CurrData &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_1].ProcCmd != NODE_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.Dir.HeadVld = true &
		Sta.Proc[NODE_2].ProcCmd != NODE_GetX &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_Get &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Proc[NODE_1].ProcCmd != NODE_Get &
		Sta.Dir.Dirty = true
	end
==>
begin
	Sta.ShWbMsg.Cmd := SHWB_ShWb ;
	Sta.ShWbMsg.Proc := Other ;
	Sta.ShWbMsg.Data := Sta.CurrData ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;

ruleset NODE_2 : NODE do
rule "ABS_NI_Remote_Get_Put67_NODE_1"

	NODE_2 != Other &
	Other != Home &
	Sta.UniMsg[NODE_2].Cmd = UNI_Get &
	Sta.UniMsg[NODE_2].Proc = Other &
	NODE_2 = Home
 	& 
	forall NODE_1 : NODE do
		 &
		Sta.FwdCmd = UNI_Get &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.UniMsg[NODE_2].Proc = Home &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Collecting = false &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd != UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Dir.Dirty = false &
		Sta.Proc[NODE_2].ProcCmd != NODE_GetX &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.Proc[NODE_2].ProcCmd = NODE_Get &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.RpMsg[NODE_2].Cmd != RP_Replace &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.UniMsg[NODE_2].Cmd := UNI_Put ;
	Sta.UniMsg[NODE_2].Proc := Other ;
	Sta.UniMsg[NODE_2].Data := Sta.CurrData ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := NODE_2;
endrule;
endruleset;


ruleset NODE_1 : NODE do
rule "ABS_NI_Remote_Get_Put67_NODE_2"

	Other != Other &
	Other != Home &
	Other = Home
 	& 
	forall NODE_2 : NODE do
		 &
		Sta.FwdCmd = UNI_Get &
		Sta.Proc[NODE_1].ProcCmd = NODE_None &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.PendReqSrc = NODE_1 &
		Sta.Proc[NODE_1].CacheData = Sta.CurrData &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[NODE_1].ProcCmd != NODE_GetX &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.UniMsg[NODE_1].Cmd != UNI_Nak &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.PendReqSrc != NODE_2 &
		Sta.FwdCmd = UNI_None &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd != UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.Dir.Dirty = false &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.UniMsg[NODE_1].Cmd != UNI_Get &
		Sta.UniMsg[NODE_1].Cmd != UNI_GetX &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Proc[NODE_1].ProcCmd != NODE_Get &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;
endruleset;

rule "ABS_NI_Remote_Get_Put67_NODE_1_NODE_2"

	Other != Other &
	Other != Home &
	Other = Home
 	& 
	forall NODE_1 : NODE; NODE_2 : NODE do
		 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Proc = Home &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.PendReqSrc != NODE_2 &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.PendReqSrc != NODE_1 &
		Sta.UniMsg[NODE_1].Cmd != UNI_Get &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.FwdCmd = UNI_Get &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.FwdCmd != UNI_GetX &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[NODE_1].CacheState != CACHE_E &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.RpMsg[NODE_2].Cmd != RP_Replace &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[NODE_1].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.UniMsg[NODE_1].Cmd != UNI_Nak &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd != UNI_None &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.Dir.Dirty = false &
		Sta.PendReqSrc = NODE_2 &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.UniMsg[NODE_1].Cmd != UNI_GetX &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Proc[NODE_1].CacheData = Sta.CurrData &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_1].ProcCmd != NODE_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.Dir.HeadVld = true &
		Sta.Proc[NODE_2].ProcCmd != NODE_GetX &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_Get &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Proc[NODE_1].ProcCmd != NODE_Get &
		Sta.Dir.Dirty = true
	end
==>
begin
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;

ruleset NODE_2 : NODE do
rule "ABS_NI_Remote_Get_Nak68_NODE_1"

	NODE_2 != Other &
	Other != Home &
	Sta.UniMsg[NODE_2].Cmd = UNI_Get &
	Sta.UniMsg[NODE_2].Proc = Other
 	& 
	forall NODE_1 : NODE do
		 &
		Sta.FwdCmd = UNI_Get &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Collecting = false &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd != UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.Proc[NODE_2].ProcCmd != NODE_GetX &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.PendReqSrc = NODE_2 &
		Sta.Dir.InvSet[Home] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.RpMsg[NODE_2].Cmd != RP_Replace &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.UniMsg[NODE_2].Cmd := UNI_Nak ;
	Sta.UniMsg[NODE_2].Proc := Other ;
	Sta.NakcMsg.Cmd := NAKC_Nakc ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := NODE_2;
endrule;
endruleset;


ruleset NODE_1 : NODE do
rule "ABS_NI_Remote_Get_Nak68_NODE_2"

	Other != Other &
	Other != Home
 	& 
	forall NODE_2 : NODE do
		 &
		Sta.FwdCmd = UNI_Get &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd != UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.PendReqSrc = NODE_2 &
		Sta.Dir.InvSet[Home] = false &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.NakcMsg.Cmd := NAKC_Nakc ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;
endruleset;

rule "ABS_NI_Remote_Get_Nak68_NODE_1_NODE_2"

	Other != Other &
	Other != Home
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.FwdCmd = UNI_Get &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrSet[NODE_1] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.InvSet[NODE_1] = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Proc[NODE_2].ProcCmd != NODE_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_1].Proc != NODE_2 &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[NODE_1].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.InvMsg[NODE_1].Cmd != INV_InvAck &
		Sta.FwdCmd != UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.Dirty = false &
		Sta.Proc[NODE_2].ProcCmd != NODE_GetX &
		Sta.InvMsg[NODE_1].Cmd != INV_Inv &
		Sta.Proc[Home].InvMarked = false &
		Sta.UniMsg[NODE_1].Cmd != UNI_Put &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.Proc[NODE_1].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.PendReqSrc = NODE_2 &
		Sta.Dir.InvSet[Home] = false &
		Sta.Proc[NODE_2].ProcCmd = NODE_Get &
		Sta.PendReqSrc != NODE_1 &
		Sta.Proc[NODE_1].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.RpMsg[NODE_2].Cmd != RP_Replace &
		Sta.UniMsg[NODE_1].Cmd != UNI_PutX &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.NakcMsg.Cmd := NAKC_Nakc ;
	Sta.FwdCmd := UNI_None ;
	Sta.FwdSrc := Other;
endrule;
rule "ABS_NI_Local_Get_Put69_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = true
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Dirty := false ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.MemData := Sta.Proc[Home].CacheData ;
	Sta.Proc[Home].CacheState := CACHE_S;
endrule;
rule "ABS_NI_Local_Get_Put70_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = true
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Dirty := false ;
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other ;
	Sta.MemData := Sta.Proc[Home].CacheData ;
	Sta.Proc[Home].CacheState := CACHE_S;
endrule;
rule "ABS_NI_Local_Get_Put71_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.ShrVld := true;
	for NODE_2 : NODE do
		Sta.Dir.InvSet[NODE_2] := (NODE_2 = Other |
    Sta.Dir.ShrSet[NODE_2] = true) ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_Get_Put72_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = true
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.ShrVld := true;
	for NODE_2 : NODE do
		Sta.Dir.InvSet[NODE_2] := (NODE_2 = Other |
    Sta.Dir.ShrSet[NODE_2] = true) ;
		;
	endfor;
endrule;
rule "ABS_NI_Local_Get_Put73_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = false
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.FwdCmd = UNI_None &
		Sta.MemData = Sta.CurrData &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv
	end
==>
begin
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other;
endrule;
rule "ABS_NI_Local_Get_Put74_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Local = true &
	Sta.Proc[Home].CacheState = CACHE_E &
	Sta.Dir.Dirty = false &
	Sta.Dir.HeadVld = false
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.MemData = Sta.CurrData &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.Proc[Home].CacheState = CACHE_S &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Dirty = true
	end
==>
begin
	Sta.Dir.HeadVld := true ;
	Sta.Dir.HeadPtr := Other;
endrule;
rule "ABS_NI_Local_Get_Get75_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = true &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.HeadPtr != Home
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.FwdCmd := UNI_Get ;
	Sta.PendReqSrc := Other ;
	Sta.PendReqCmd := UNI_Get ;
	Sta.Collecting := false;
endrule;
rule "ABS_NI_Local_Get_Get76_NODE_1"

	Other != Home &
	Sta.Dir.Pending = false &
	Sta.Dir.Dirty = true &
	Sta.Dir.Local = false &
	Sta.Dir.HeadPtr != Other &
	Sta.Dir.HeadPtr = Home
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Collecting = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.Dir.Pending := true ;
	Sta.PendReqSrc := Other ;
	Sta.PendReqCmd := UNI_Get ;
	Sta.Collecting := false;
endrule;

-- No abstract rule for rule NI_Local_Get_Nak77



-- No abstract rule for rule NI_Local_Get_Nak78



-- No abstract rule for rule NI_Local_Get_Nak79



-- No abstract rule for rule NI_Nak81



-- No abstract rule for rule PI_Remote_Replace83


rule "ABS_PI_Remote_PutX86_NODE_1"

	Other != Home
 	& 
	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.Dir.ShrVld = false &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.PendReqSrc != NODE_2 &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Dir.Dirty = true &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.WbMsg.Cmd := WB_Wb ;
	Sta.WbMsg.Proc := Other ;
	Sta.WbMsg.Data := Sta.CurrData;
endrule;

-- No abstract rule for rule PI_Remote_GetX95



-- No abstract rule for rule PI_Remote_Get100



ruleset DATA_1 : DATA do
rule "ABS_Store101_NODE_1"

	forall NODE_2 : NODE; NODE_1 : NODE do
		 &
		Sta.Proc[NODE_2].CacheState != CACHE_S &
		Sta.Dir.HeadPtr != NODE_1 &
		Sta.UniMsg[Home].Cmd != UNI_PutX &
		Sta.Dir.Local = false &
		Sta.UniMsg[Home].Cmd != UNI_Put &
		Sta.Dir.ShrSet[NODE_2] = false &
		Sta.PendReqSrc = NODE_1 &
		Sta.Dir.ShrVld = false &
		Sta.Dir.HeadPtr != NODE_2 &
		Sta.NakcMsg.Cmd != NAKC_Nakc &
		Sta.ShWbMsg.Proc != NODE_1 &
		Sta.Collecting = false &
		Sta.UniMsg[NODE_2].Cmd != UNI_PutX &
		Sta.Dir.Dirty = true &
		Sta.Proc[NODE_2].CacheState != CACHE_E &
		Sta.Proc[Home].CacheState = CACHE_I &
		Sta.Proc[Home].ProcCmd != NODE_Get &
		Sta.FwdCmd != UNI_GetX &
		Sta.ShWbMsg.Cmd != SHWB_FAck &
		Sta.Proc[Home].CacheData = Sta.CurrData &
		Sta.Proc[Home].CacheState != CACHE_I &
		Sta.Proc[Home].ProcCmd = NODE_None &
		Sta.Proc[NODE_2].InvMarked = false &
		Sta.Dir.InvSet[NODE_2] = false &
		Sta.Dir.HeadPtr = NODE_1 &
		Sta.ShWbMsg.Cmd != SHWB_ShWb &
		Sta.UniMsg[NODE_2].Cmd != UNI_Put &
		Sta.FwdCmd = UNI_None &
		Sta.PendReqSrc != NODE_2 &
		Sta.UniMsg[NODE_2].Proc != NODE_1 &
		Sta.ShWbMsg.Cmd = SHWB_FAck &
		Sta.Dir.HeadVld = true &
		Sta.Proc[Home].InvMarked = false &
		Sta.ShWbMsg.Proc != Home &
		Sta.Proc[NODE_2].CacheState = CACHE_I &
		Sta.InvMsg[NODE_2].Cmd != INV_InvAck &
		Sta.Dir.HeadPtr != Home &
		Sta.ShWbMsg.Proc != NODE_2 &
		Sta.WbMsg.Cmd != WB_Wb &
		Sta.Dir.InvSet[Home] = false &
		Sta.ShWbMsg.Proc = NODE_1 &
		Sta.FwdCmd != UNI_Get &
		Sta.Proc[Home].CacheState != CACHE_E &
		Sta.Dir.HeadPtr = NODE_2 &
		Sta.InvMsg[NODE_2].Cmd != INV_Inv &
		Sta.Proc[Home].CacheState != CACHE_S &
		Sta.Dir.Pending = true &
		Sta.Proc[Home].CacheState = CACHE_E &
		Sta.Dir.HeadVld = false
	end
==>
begin
	Sta.CurrData := DATA_1 ;
	Sta.LastWrVld := true ;
	Sta.LastWrPtr := Other;
endrule;
endruleset;
