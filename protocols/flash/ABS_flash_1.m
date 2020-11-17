
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


ruleset i : NODE do
invariant "rule_1"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_3"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_4"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_5"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Collecting = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_6"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[i] = false);
endruleset;
invariant "rule_7"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.FwdCmd != UNI_GetX);;


ruleset i : NODE ; j : NODE do
invariant "rule_8"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_9"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_10"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_11"
		(Home != i) ->	(Sta.Proc[i].InvMarked = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_12"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE ; j : NODE do
invariant "rule_13"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_14"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_15"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_16"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset j : NODE do
invariant "rule_17"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_18"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_19"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_20"
		(Home != i) ->	(Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_21"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_22"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_23"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_24"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Collecting = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_25"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_26"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_27"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_28"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_29"
		(Home != j) ->	(Sta.Dir.Local = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_30"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_31"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_32"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_33"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_34"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_35"
		(Home != i) ->	(Sta.Dir.ShrVld = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_36"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_37"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Collecting = true);
endruleset;
invariant "rule_38"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].CacheData = Sta.CurrData);;


ruleset i : NODE do
invariant "rule_39"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_40"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_41"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_42"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.PendReqSrc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_43"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_44"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_45"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_46"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.PendReqSrc != i);
endruleset;


ruleset i : NODE do
invariant "rule_47"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_48"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_49"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.UniMsg[j].Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_50"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_51"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_52"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_53"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_54"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_55"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_56"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_57"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_58"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd = NODE_GetX);
endruleset;
invariant "rule_59"
	(Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_60"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_61"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_62"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_63"
		(Home != i) ->	(Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_64"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_65"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_Get);
endruleset;
invariant "rule_66"
	(Sta.Dir.Pending = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_67"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_68"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;
invariant "rule_69"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE do
invariant "rule_70"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_71"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.HeadPtr != j);
endruleset;
invariant "rule_72"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_73"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_FAck);;
invariant "rule_74"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);;
invariant "rule_75"
	(Sta.Dir.Pending = false -> Sta.FwdCmd != UNI_GetX);;


ruleset i : NODE do
invariant "rule_76"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_77"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_78"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_79"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_80"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_81"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_82"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Collecting = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_83"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.Local = false);
endruleset;


ruleset j : NODE do
invariant "rule_84"
		(Home != j) ->	(Sta.Dir.ShrVld = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_85"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
invariant "rule_86"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE do
invariant "rule_87"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_88"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_89"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_90"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE do
invariant "rule_91"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_92"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_93"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_94"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_95"
		(Home != i) ->	(Sta.Dir.HeadPtr = i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_96"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_97"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_98"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_99"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_100"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_101"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_102"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_103"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_104"
		(Home != i) ->	(Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_105"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset j : NODE do
invariant "rule_106"
		(Home != j) ->	(Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_107"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_108"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_109"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_110"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr = i);
endruleset;
invariant "rule_111"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);;
invariant "rule_112"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset j : NODE do
invariant "rule_113"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Dir.HeadPtr != j);
endruleset;
invariant "rule_114"
	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_115"
		(Home != i) ->	(Sta.Dir.Pending = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_116"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_117"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_118"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_119"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_120"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset i : NODE do
invariant "rule_121"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_122"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_123"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_124"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Dir.Local = false);;


ruleset j : NODE do
invariant "rule_125"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_126"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_127"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_128"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_129"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_130"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_131"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_132"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].InvMarked = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_133"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_134"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_135"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_136"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_137"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_138"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_139"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_140"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != j -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_141"
		(Home != j) ->	(Sta.Dir.HeadPtr = j & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_142"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_143"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_144"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_145"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_146"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_147"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_148"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_149"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_150"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_151"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;
invariant "rule_152"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset j : NODE do
invariant "rule_153"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Dir.Dirty = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_154"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_155"
	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_156"
	(Sta.Dir.Pending = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset i : NODE do
invariant "rule_157"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_158"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_159"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_160"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_161"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_162"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_163"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_164"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;
invariant "rule_165"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset i : NODE ; j : NODE do
invariant "rule_166"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_167"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_168"
	(Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset i : NODE do
invariant "rule_169"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;
invariant "rule_170"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE do
invariant "rule_171"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_172"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_173"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_174"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_175"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_176"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_177"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_178"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_179"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_180"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_181"
		(Home != j) ->	(Sta.Dir.ShrVld = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_182"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_183"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadVld = true);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_184"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.Dirty = false);
endruleset;


ruleset i : NODE do
invariant "rule_185"
		(Home != i) ->	(Sta.Dir.Pending = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_186"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_187"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_188"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Collecting = true);
endruleset;


ruleset j : NODE do
invariant "rule_189"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_190"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheData = Sta.CurrData);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_191"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd != NODE_None);
endruleset;


ruleset j : NODE do
invariant "rule_192"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].ProcCmd != NODE_Get);
endruleset;


ruleset j : NODE do
invariant "rule_193"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState = CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_194"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_195"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_196"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_197"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_198"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_199"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_200"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE ; j : NODE do
invariant "rule_201"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_202"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_203"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_204"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_205"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_206"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_207"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_208"
		(Home != i) ->	(Sta.Proc[i].InvMarked = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_209"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_210"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_211"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_212"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.ShrSet[i] = false);
endruleset;
invariant "rule_213"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE ; j : NODE do
invariant "rule_214"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_215"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_216"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_217"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_218"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_I -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_219"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_220"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_221"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_222"
	(Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_223"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_224"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_225"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_226"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.ShrVld = true -> Sta.UniMsg[j].Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_227"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_228"
	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_229"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE ; j : NODE do
invariant "rule_230"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_231"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_232"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_233"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_234"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_235"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Local = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_236"
		(Home != j) ->	(Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_237"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_238"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = false -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_239"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset j : NODE do
invariant "rule_240"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_241"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_242"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_243"
	(Sta.Dir.HeadVld = true & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset j : NODE ; i : NODE do
invariant "rule_244"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_245"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Collecting = false);
endruleset;


ruleset j : NODE do
invariant "rule_246"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_247"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_248"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_249"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_250"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_251"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Dir.HeadVld = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_252"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_253"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != Home);
endruleset;


ruleset j : NODE do
invariant "rule_254"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_255"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_256"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_257"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_258"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_259"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_260"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.HeadPtr = i);
endruleset;
invariant "rule_261"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_262"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_263"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;
invariant "rule_264"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_265"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
invariant "rule_266"
		(Home != j) ->	(Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_267"
	(Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE ; j : NODE do
invariant "rule_268"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_269"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_270"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_271"
		(Home != i) ->	(Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_272"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_273"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_274"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_275"
	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_276"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_277"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_278"
		(Home != j) ->	(Sta.Dir.HeadPtr != j -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_279"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_280"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;
invariant "rule_281"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_Get);;


ruleset i : NODE do
invariant "rule_282"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_283"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
invariant "rule_284"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_285"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_286"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE ; j : NODE do
invariant "rule_287"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_288"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_289"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_290"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_291"
	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_292"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadVld = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_293"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_294"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_295"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_296"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_297"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_298"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_299"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_300"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_301"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_302"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_303"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_304"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_305"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.FwdCmd = UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_306"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_307"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_308"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheState != CACHE_I);
endruleset;


ruleset j : NODE do
invariant "rule_309"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_310"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_311"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr = i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_312"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_313"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr != Home);
endruleset;


ruleset i : NODE do
invariant "rule_314"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_315"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_316"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_317"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_318"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_319"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_320"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_321"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_322"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_323"
		(Home != i) ->	(Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_324"
	(Sta.Dir.Dirty = false -> Sta.Proc[Home].InvMarked = false);;
invariant "rule_325"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.HeadVld = false);;


ruleset j : NODE do
invariant "rule_326"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_327"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_328"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.FwdCmd != UNI_Get);
endruleset;
invariant "rule_329"
	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE ; i : NODE do
invariant "rule_330"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].ProcCmd = NODE_GetX);
endruleset;


ruleset j : NODE do
invariant "rule_331"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Collecting = true);
endruleset;


ruleset j : NODE do
invariant "rule_332"
		(Home != j) ->	(Sta.Dir.ShrVld = true -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_333"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_334"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_335"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_336"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE ; j : NODE do
invariant "rule_337"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
invariant "rule_338"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE do
invariant "rule_339"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
invariant "rule_340"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_341"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_342"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_343"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_344"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_345"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_346"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr != i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_347"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_348"
		(Home != j) ->	(Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
invariant "rule_349"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE ; j : NODE do
invariant "rule_350"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_351"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_352"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_353"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_354"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_355"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_356"
	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_357"
		(Home != i) ->	(Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_358"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_359"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Collecting = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_360"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_361"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_362"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_363"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_364"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_365"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_366"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_367"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.Local = false);;


ruleset i : NODE do
invariant "rule_368"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_369"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_370"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_371"
	(Sta.Dir.ShrVld = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_372"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_373"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_374"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE do
invariant "rule_375"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[j] = false);
endruleset;
invariant "rule_376"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState = CACHE_I);;
invariant "rule_377"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Dir.Dirty = true);;
invariant "rule_378"
	(Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE ; j : NODE do
invariant "rule_379"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_380"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_381"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_382"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_383"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_384"
	(Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE do
invariant "rule_385"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_386"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_387"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.FwdCmd != UNI_Get);;


ruleset i : NODE do
invariant "rule_388"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_389"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = false -> Sta.Dir.InvSet[Home] = false);;


ruleset j : NODE do
invariant "rule_390"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr = j);
endruleset;


ruleset i : NODE do
invariant "rule_391"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Nak -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_392"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.FwdCmd = UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_393"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_394"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_395"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_396"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_397"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_398"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.FwdCmd = UNI_None);
endruleset;
invariant "rule_399"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.FwdCmd = UNI_None);;


ruleset i : NODE ; j : NODE do
invariant "rule_400"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_401"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_402"
	(Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset j : NODE do
invariant "rule_403"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_404"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_405"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_406"
	(Sta.Dir.ShrVld = true -> Sta.Collecting = false);;


ruleset i : NODE do
invariant "rule_407"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_408"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_409"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrSet[i] = false);
endruleset;
invariant "rule_410"
	(Sta.Dir.Pending = true & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset j : NODE do
invariant "rule_411"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_412"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_413"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_414"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != j -> Sta.Dir.HeadVld = false);
endruleset;
invariant "rule_415"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset i : NODE ; j : NODE do
invariant "rule_416"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_417"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE do
invariant "rule_418"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_419"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_420"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_421"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != Home);
endruleset;


ruleset i : NODE do
invariant "rule_422"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_423"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[i].Cmd != UNI_Nak);
endruleset;


ruleset i : NODE do
invariant "rule_424"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_425"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_426"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.PendReqSrc != i);
endruleset;


ruleset i : NODE do
invariant "rule_427"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;
invariant "rule_428"
	(Sta.Dir.Pending = true -> Sta.Dir.ShrVld = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_429"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_430"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_I);;


ruleset j : NODE do
invariant "rule_431"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_432"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_433"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_434"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_GetX);
endruleset;
invariant "rule_435"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.WbMsg.Cmd != WB_Wb);;
invariant "rule_436"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset j : NODE do
invariant "rule_437"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_438"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_439"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
invariant "rule_440"
	(Sta.Dir.ShrVld = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE do
invariant "rule_441"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
invariant "rule_442"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_443"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_444"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_445"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_446"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_447"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_448"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Collecting = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_449"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_450"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_451"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
invariant "rule_452"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_453"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_454"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_455"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_456"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
invariant "rule_457"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
invariant "rule_458"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_459"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState = CACHE_S);;


ruleset j : NODE do
invariant "rule_460"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_461"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_462"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_463"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);;


ruleset j : NODE do
invariant "rule_464"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_465"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_466"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_467"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_468"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_469"
		(Home != j) ->	(Sta.Dir.HeadVld = true -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_470"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset j : NODE ; i : NODE do
invariant "rule_471"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HeadPtr != j);
endruleset;
invariant "rule_472"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_473"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_474"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_475"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_476"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_477"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_478"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE do
invariant "rule_479"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_480"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_481"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_482"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_483"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_484"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_485"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE ; j : NODE do
invariant "rule_486"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_487"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_488"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_489"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr != i -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;
invariant "rule_490"
	(Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE do
invariant "rule_491"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_492"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_493"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_494"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_495"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.WbMsg.Cmd != WB_Wb);;
invariant "rule_496"
	(Sta.Dir.ShrVld = true -> Sta.MemData = Sta.CurrData);;


ruleset i : NODE ; j : NODE do
invariant "rule_497"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_498"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_499"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_500"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_501"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_502"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;
invariant "rule_503"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.MemData = Sta.CurrData);;


ruleset j : NODE ; i : NODE do
invariant "rule_504"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_505"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_506"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE do
invariant "rule_507"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_508"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_509"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_510"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState = CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_511"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_512"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_513"
		(Home != i) ->	(Sta.Proc[i].CacheState != CACHE_E -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_514"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.ShrSet[i] = false);
endruleset;
invariant "rule_515"
	(Sta.Dir.Pending = true & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_516"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = false -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_517"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState = CACHE_E);
endruleset;
invariant "rule_518"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_GetX);;


ruleset j : NODE ; i : NODE do
invariant "rule_519"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_520"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_521"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr != Home);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_522"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_523"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_524"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_525"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_526"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_527"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;
invariant "rule_528"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE ; j : NODE do
invariant "rule_529"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_530"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_531"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_532"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_533"
		(Home != j) ->	(Sta.Dir.Local = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_534"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_535"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Cmd != UNI_Nak);
endruleset;


ruleset i : NODE do
invariant "rule_536"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_537"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
invariant "rule_538"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_539"
		(Home != j) ->	(Sta.Dir.ShrVld = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_540"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_541"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_542"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.FwdCmd != UNI_Get);;
invariant "rule_543"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;
invariant "rule_544"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE ; j : NODE do
invariant "rule_545"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_546"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_547"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_548"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_549"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_550"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_551"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE do
invariant "rule_552"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_553"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_554"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_555"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.PendReqSrc = i);
endruleset;
invariant "rule_556"
	(Sta.Dir.ShrVld = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);;
invariant "rule_557"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);;
invariant "rule_558"
	(Sta.Proc[Home].CacheState != CACHE_E -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_559"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_560"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_561"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_562"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_563"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;
invariant "rule_564"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Proc[Home].CacheData = Sta.CurrData);;


ruleset i : NODE do
invariant "rule_565"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != Home);
endruleset;


ruleset i : NODE do
invariant "rule_566"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_567"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;
invariant "rule_568"
	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.WbMsg.Cmd != WB_Wb);;
invariant "rule_569"
	(Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_570"
		(Home != i) ->	(Sta.Proc[i].CacheState != CACHE_E -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_571"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_572"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_573"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_574"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.UniMsg[j].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_575"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset j : NODE do
invariant "rule_576"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_577"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_578"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Proc[j].ProcCmd != NODE_None);
endruleset;


ruleset j : NODE do
invariant "rule_579"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_580"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_581"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_582"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;
invariant "rule_583"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE do
invariant "rule_584"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;
invariant "rule_585"
	(Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_586"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_587"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_588"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_589"
		(Home != j) ->	(Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr = j);
endruleset;


ruleset i : NODE do
invariant "rule_590"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_591"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_592"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_593"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_594"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != Home -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_595"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_596"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_597"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_598"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_599"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_600"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_601"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_602"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_603"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_604"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_605"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Collecting = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_606"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_607"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_608"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_609"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_610"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_611"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_612"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset j : NODE do
invariant "rule_613"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_614"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_615"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_616"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_617"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_618"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_619"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE do
invariant "rule_620"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_621"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_622"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_623"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE do
invariant "rule_624"
		(Home != j) ->	(Sta.Dir.Dirty = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_625"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_626"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_627"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_628"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_629"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_630"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_631"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_632"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_633"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != Home);;
invariant "rule_634"
	(Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_635"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_636"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd = NODE_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_637"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_638"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_639"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.HeadVld = false);
endruleset;
invariant "rule_640"
	(Sta.Dir.Pending = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_641"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_642"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_643"
		(Home != j) ->	(Sta.Dir.Pending = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_644"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_645"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
invariant "rule_646"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_647"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_648"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState != CACHE_E -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_649"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_650"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_651"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_652"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].InvMarked = false);
endruleset;
invariant "rule_653"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.FwdCmd != UNI_GetX);;
invariant "rule_654"
	(Sta.Dir.ShrVld = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;
invariant "rule_655"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Proc[Home].CacheData = Sta.CurrData);;


ruleset j : NODE do
invariant "rule_656"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_657"
	(Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE ; i : NODE do
invariant "rule_658"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_659"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_660"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_661"
		(Home != j) ->	(Sta.Dir.HeadPtr != j -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_662"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Collecting = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_663"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd = NODE_Get);
endruleset;
invariant "rule_664"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_665"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_666"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Dir.Dirty = false);
endruleset;
invariant "rule_667"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_668"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].InvMarked = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_669"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_670"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_671"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_672"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_673"
	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_674"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_675"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_676"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_677"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_678"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr = i -> Sta.Dir.HeadVld = true);
endruleset;


ruleset j : NODE do
invariant "rule_679"
		(Home != j) ->	(Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_680"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;
invariant "rule_681"
	(Sta.Dir.ShrVld = true -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE ; j : NODE do
invariant "rule_682"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_683"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_684"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr != Home);
endruleset;
invariant "rule_685"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset j : NODE ; i : NODE do
invariant "rule_686"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_687"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_688"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_689"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr = i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_690"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.FwdCmd = UNI_None);
endruleset;
invariant "rule_691"
	(Sta.Dir.HeadPtr != Home -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_692"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc = i);
endruleset;


ruleset i : NODE do
invariant "rule_693"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_694"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_695"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_696"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_697"
	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE do
invariant "rule_698"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset j : NODE do
invariant "rule_699"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE do
invariant "rule_700"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_701"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_702"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_703"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Local = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_704"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;
invariant "rule_705"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.MemData = Sta.CurrData);;


ruleset i : NODE ; j : NODE do
invariant "rule_706"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_707"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_708"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_709"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_710"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
invariant "rule_711"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;
invariant "rule_712"
	(Sta.Dir.Pending = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_713"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_714"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_715"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_716"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_717"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_718"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_719"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE do
invariant "rule_720"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Local = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_721"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_722"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_723"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Proc = Home);
endruleset;
invariant "rule_724"
	(Sta.Dir.Pending = false -> Sta.Dir.InvSet[Home] = false);;


ruleset j : NODE do
invariant "rule_725"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_726"
	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE ; j : NODE do
invariant "rule_727"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_728"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_729"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_730"
	(Sta.Dir.Dirty = false -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_731"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_732"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_733"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_734"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;
invariant "rule_735"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_Get);;


ruleset i : NODE ; j : NODE do
invariant "rule_736"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_737"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_738"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE do
invariant "rule_739"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != j -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_740"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_741"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_742"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_743"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_744"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_745"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
invariant "rule_746"
	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.Proc[Home].CacheState = CACHE_I);;
invariant "rule_747"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.FwdCmd = UNI_None);;


ruleset j : NODE do
invariant "rule_748"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_749"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset i : NODE ; j : NODE do
invariant "rule_750"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_751"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.PendReqSrc != i);
endruleset;


ruleset j : NODE do
invariant "rule_752"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_753"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_754"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_755"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.Pending = true);
endruleset;


ruleset i : NODE do
invariant "rule_756"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_757"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_758"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_759"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_760"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_761"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_762"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_763"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;
invariant "rule_764"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.FwdCmd != UNI_Get);;


ruleset j : NODE do
invariant "rule_765"
		(Home != j) ->	(Sta.Dir.ShrVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_766"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE do
invariant "rule_767"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_768"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset j : NODE do
invariant "rule_769"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_770"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_771"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;
invariant "rule_772"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset i : NODE do
invariant "rule_773"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_774"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_775"
		(Home != i) ->	(Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_776"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;
invariant "rule_777"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.FwdCmd = UNI_None);;


ruleset i : NODE do
invariant "rule_778"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_779"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_780"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.Local = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_781"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_782"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_783"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != Home);
endruleset;
invariant "rule_784"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE do
invariant "rule_785"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_786"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE do
invariant "rule_787"
		(Home != j) ->	(Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr = j);
endruleset;


ruleset i : NODE do
invariant "rule_788"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_789"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_790"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_791"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_792"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_793"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;
invariant "rule_794"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;
invariant "rule_795"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE ; i : NODE do
invariant "rule_796"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_797"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_798"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_799"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_800"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_801"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE ; j : NODE do
invariant "rule_802"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_803"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
invariant "rule_804"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_805"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_806"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_807"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_808"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_809"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_810"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_811"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_812"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_813"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_I -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_814"
	(Sta.Dir.ShrVld = true -> Sta.FwdCmd = UNI_None);;
invariant "rule_815"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_GetX);;


ruleset i : NODE ; j : NODE do
invariant "rule_816"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_817"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_818"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_819"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_820"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset i : NODE do
invariant "rule_821"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_822"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_823"
	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE ; j : NODE do
invariant "rule_824"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_825"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_826"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_827"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_828"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE do
invariant "rule_829"
		(Home != j) ->	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_830"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;
invariant "rule_831"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;
invariant "rule_832"
	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_833"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_834"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE do
invariant "rule_835"
		(Home != j) ->	(Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != j);
endruleset;
invariant "rule_836"
	(Sta.Dir.Pending = true & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE do
invariant "rule_837"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Dir.Local = true);
endruleset;
invariant "rule_838"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.WbMsg.Cmd != WB_Wb);;
invariant "rule_839"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_840"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_841"
	(Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_842"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_843"
		(Home != i) ->	(Sta.Dir.HeadPtr = i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_844"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE do
invariant "rule_845"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_846"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_847"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_848"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr != i -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_849"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_850"
		(Home != i) ->	(Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_851"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_852"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_853"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_854"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_855"
		(Home != i) ->	(Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_856"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_857"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_858"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_859"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_860"
	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_861"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_862"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.MemData = Sta.CurrData);
endruleset;
invariant "rule_863"
	(Sta.Dir.HeadVld = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_864"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_865"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_866"
	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_867"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_868"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_869"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_870"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE do
invariant "rule_871"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_872"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_873"
		(Home != j) ->	(Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
invariant "rule_874"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_875"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_876"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.Pending = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_877"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_878"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_879"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_880"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_881"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_882"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_883"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;
invariant "rule_884"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset i : NODE do
invariant "rule_885"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_886"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_887"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_888"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_889"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_890"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_891"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_892"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_893"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_894"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_895"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_896"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_897"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Proc != Home);
endruleset;


ruleset i : NODE do
invariant "rule_898"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_899"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_900"
		(Home != j) ->	(Sta.Dir.HeadPtr != j -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_901"
		(Home != i) ->	(Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_902"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;
invariant "rule_903"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_904"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;
invariant "rule_905"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_906"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_907"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;


ruleset j : NODE do
invariant "rule_908"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Collecting = true);
endruleset;
invariant "rule_909"
	(Sta.Dir.Pending = true & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);;
invariant "rule_910"
	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_911"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_912"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;
invariant "rule_913"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.FwdCmd != UNI_GetX);;


ruleset i : NODE ; j : NODE do
invariant "rule_914"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_915"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_916"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_917"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_918"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_919"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_920"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_921"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_922"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset j : NODE do
invariant "rule_923"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_924"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;
invariant "rule_925"
	(Sta.Dir.Local = true -> Sta.FwdCmd != UNI_GetX);;


ruleset i : NODE ; j : NODE do
invariant "rule_926"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_927"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_928"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.MemData = Sta.PrevData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_929"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_930"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_931"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_932"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_933"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE ; j : NODE do
invariant "rule_934"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_935"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd != NODE_GetX);
endruleset;
invariant "rule_936"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);;
invariant "rule_937"
	(Sta.Dir.Local = true -> Sta.WbMsg.Cmd != WB_Wb);;
invariant "rule_938"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_939"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
invariant "rule_940"
		(Home != j) ->	(Sta.Dir.Pending = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
invariant "rule_941"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset j : NODE do
invariant "rule_942"
		(Home != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_943"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.Pending = true);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_944"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.UniMsg[j].Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_945"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;
invariant "rule_946"
	(Sta.Dir.ShrVld = true -> Sta.Dir.HeadVld = true);;


ruleset i : NODE ; j : NODE do
invariant "rule_947"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_948"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_949"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_950"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_951"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.Dir.HeadVld = false);
endruleset;
invariant "rule_952"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != Home);;


ruleset i : NODE do
invariant "rule_953"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_954"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_955"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_956"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_957"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_958"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_959"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;
invariant "rule_960"
	(Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_961"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE do
invariant "rule_962"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_963"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_964"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_965"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_966"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_967"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc = i);
endruleset;


ruleset i : NODE do
invariant "rule_968"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_969"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_970"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_971"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_972"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_973"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;
invariant "rule_974"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Proc[Home].CacheState = CACHE_I);;
invariant "rule_975"
	(Sta.Dir.Pending = false -> Sta.FwdCmd != UNI_Get);;


ruleset j : NODE do
invariant "rule_976"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_977"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;
invariant "rule_978"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset j : NODE ; i : NODE do
invariant "rule_979"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;
invariant "rule_980"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_981"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_982"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_983"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
invariant "rule_984"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_985"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_986"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_987"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_988"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_989"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_990"
		(Home != i) ->	(Sta.Dir.HeadPtr = i -> Sta.Dir.HeadVld = true);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_991"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Dir.HeadPtr != j);
endruleset;
invariant "rule_992"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_993"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_994"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Dir.Local = false);
endruleset;
invariant "rule_995"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Dir.Local = false);;
invariant "rule_996"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_997"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_998"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_999"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1000"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.Local = false);
endruleset;


ruleset i : NODE do
invariant "rule_1001"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_1002"
		(Home != j) ->	(Sta.Dir.Pending = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1003"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Proc != i);
endruleset;
invariant "rule_1004"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE ; j : NODE do
invariant "rule_1005"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_1006"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1007"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1008"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;
invariant "rule_1009"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd = UNI_None);;
invariant "rule_1010"
	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState = CACHE_I);;
invariant "rule_1011"
	(Sta.Dir.ShrVld = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;
invariant "rule_1012"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_1013"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_1014"
		(Home != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1015"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
invariant "rule_1016"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE do
invariant "rule_1017"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1018"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1019"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1020"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1021"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1022"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1023"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1024"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_1025"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1026"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1027"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;
invariant "rule_1028"
	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE do
invariant "rule_1029"
		(Home != i) ->	(Sta.Dir.Local = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1030"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1031"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Nak);
endruleset;


ruleset i : NODE do
invariant "rule_1032"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_1033"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.FwdCmd != UNI_Get);;


ruleset i : NODE ; j : NODE do
invariant "rule_1034"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1035"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1036"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1037"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1038"
	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_1039"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_1040"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1041"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_1042"
		(Home != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Dir.ShrSet[j] = false);
endruleset;
invariant "rule_1043"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_1044"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1045"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;
invariant "rule_1046"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_1047"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1048"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1049"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_1050"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_1051"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_1052"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1053"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1054"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1055"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_1056"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1057"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1058"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1059"
		(Home != i) ->	(Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1060"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_1061"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1062"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1063"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Dirty = true);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1064"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_1065"
	(Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;
invariant "rule_1066"
	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_I);;


ruleset i : NODE do
invariant "rule_1067"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_1068"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1069"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1070"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1071"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1072"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1073"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1074"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;
invariant "rule_1075"
	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_1076"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Collecting = true);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1077"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.RpMsg[j].Cmd != RP_Replace);
endruleset;


ruleset i : NODE do
invariant "rule_1078"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1079"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1080"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1081"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1082"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1083"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1084"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1085"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1086"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1087"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1088"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.FwdCmd != UNI_Get);;


ruleset j : NODE ; i : NODE do
invariant "rule_1089"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_1090"
	(Sta.Dir.Pending = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.ShrVld = false);;


ruleset i : NODE do
invariant "rule_1091"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_1092"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1093"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1094"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_1095"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.PendReqSrc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1096"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1097"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheData = Sta.CurrData);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1098"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.InvSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1099"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset j : NODE do
invariant "rule_1100"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1101"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1102"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1103"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1104"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_1105"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1106"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1107"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1108"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1109"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_1110"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_1111"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.MemData = Sta.PrevData);
endruleset;


ruleset i : NODE do
invariant "rule_1112"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_1113"
		(Home != j) ->	(Sta.Dir.ShrVld = true -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
invariant "rule_1114"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;
invariant "rule_1115"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1116"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1117"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;
invariant "rule_1118"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1119"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1120"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].InvMarked = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1121"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;
invariant "rule_1122"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.WbMsg.Cmd != WB_Wb);;
invariant "rule_1123"
	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.ShrVld = false);;


ruleset i : NODE do
invariant "rule_1124"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1125"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1126"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1127"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_1128"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1129"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1130"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1131"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1132"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1133"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1134"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1135"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1136"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1137"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1138"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1139"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1140"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset j : NODE do
invariant "rule_1141"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Dir.Dirty = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1142"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_1143"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr != Home);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1144"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1145"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1146"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_1147"
	(Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE do
invariant "rule_1148"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE do
invariant "rule_1149"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1150"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1151"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
invariant "rule_1152"
		(Home != j) ->	(Sta.Dir.HeadPtr != j -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_1153"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Collecting = false);;


ruleset j : NODE ; i : NODE do
invariant "rule_1154"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_1155"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE do
invariant "rule_1156"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1157"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1158"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1159"
	(Sta.Dir.ShrVld = false -> Sta.Dir.InvSet[Home] = false);;


ruleset j : NODE ; i : NODE do
invariant "rule_1160"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1161"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
invariant "rule_1162"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false);;


ruleset j : NODE ; i : NODE do
invariant "rule_1163"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1164"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1165"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1166"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1167"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1168"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1169"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE do
invariant "rule_1170"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_1171"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1172"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1173"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
invariant "rule_1174"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_1175"
	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE ; j : NODE do
invariant "rule_1176"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1177"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.PendReqSrc = i);
endruleset;


ruleset j : NODE do
invariant "rule_1178"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1179"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1180"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1181"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Local = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1182"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_1183"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Pending = false -> Sta.Dir.InvSet[Home] = false);;


ruleset j : NODE do
invariant "rule_1184"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE do
invariant "rule_1185"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1186"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1187"
	(Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.Local = false);;


ruleset j : NODE do
invariant "rule_1188"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
invariant "rule_1189"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Pending = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1190"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != j -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1191"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1192"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1193"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_1194"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Pending = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1195"
		(Home != j) ->	(Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1196"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1197"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_1198"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1199"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1200"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1201"
		(Home != j) ->	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1202"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1203"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_1204"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1205"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1206"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1207"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1208"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1209"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1210"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != j -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1211"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != Home -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1212"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_1213"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1214"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1215"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
invariant "rule_1216"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1217"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1218"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_1219"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1220"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1221"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1222"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd = NODE_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1223"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_1224"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1225"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_I -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1226"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1227"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1228"
	(Sta.Dir.Dirty = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE ; j : NODE do
invariant "rule_1229"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1230"
	(Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_1231"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1232"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1233"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1234"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1235"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1236"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1237"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;
invariant "rule_1238"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1239"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1240"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1241"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1242"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1243"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1244"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.PendReqSrc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1245"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1246"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1247"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1248"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1249"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1250"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_1251"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1252"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadVld = true);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1253"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1254"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1255"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].ProcCmd != NODE_Get);
endruleset;


ruleset j : NODE do
invariant "rule_1256"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_1257"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1258"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1259"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1260"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_1261"
	(Sta.Dir.Pending = false -> Sta.FwdCmd = UNI_None);;


ruleset i : NODE do
invariant "rule_1262"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1263"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1264"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1265"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Dir.Pending = false);
endruleset;


ruleset i : NODE do
invariant "rule_1266"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1267"
		(Home != i) ->	(Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1268"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.FwdCmd != UNI_GetX);;
invariant "rule_1269"
	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_1270"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_1271"
	(Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1272"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_1273"
	(Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset j : NODE do
invariant "rule_1274"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
invariant "rule_1275"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Dir.Dirty = true);;


ruleset i : NODE do
invariant "rule_1276"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1277"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE do
invariant "rule_1278"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_1279"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Dir.Dirty = false);
endruleset;


ruleset i : NODE do
invariant "rule_1280"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1281"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1282"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1283"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.PendReqSrc = j);
endruleset;


ruleset i : NODE do
invariant "rule_1284"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1285"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1286"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_1287"
	(Sta.Dir.Dirty = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE ; j : NODE do
invariant "rule_1288"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_1289"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1290"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1291"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1292"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1293"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_1294"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1295"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_1296"
		(Home != i) ->	(Sta.Dir.Dirty = false -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1297"
	(Sta.Dir.Local = false & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset i : NODE do
invariant "rule_1298"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE do
invariant "rule_1299"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1300"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_1301"
	(Sta.Dir.Local = true & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_1302"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset j : NODE do
invariant "rule_1303"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_1304"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.FwdCmd = UNI_None);;


ruleset j : NODE do
invariant "rule_1305"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1306"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1307"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
invariant "rule_1308"
		(Home != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1309"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1310"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1311"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1312"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;
invariant "rule_1313"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.FwdCmd = UNI_None);;


ruleset j : NODE do
invariant "rule_1314"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1315"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1316"
	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;
invariant "rule_1317"
	(Sta.Dir.ShrVld = true -> Sta.Dir.Dirty = false);;


ruleset i : NODE do
invariant "rule_1318"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_1319"
		(Home != j) ->	(Sta.Dir.ShrVld = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1320"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_1321"
	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;
invariant "rule_1322"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE ; j : NODE do
invariant "rule_1323"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_1324"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1325"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1326"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1327"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1328"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.Pending = true);
endruleset;
invariant "rule_1329"
	(Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr != Home);;


ruleset i : NODE do
invariant "rule_1330"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1331"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1332"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1333"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1334"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_1335"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Proc[Home].CacheData = Sta.CurrData);;
invariant "rule_1336"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_1337"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1338"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1339"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1340"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1341"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1342"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.Local = true);
endruleset;


ruleset i : NODE do
invariant "rule_1343"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_1344"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != j);
endruleset;
invariant "rule_1345"
	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.MemData = Sta.CurrData);;


ruleset j : NODE do
invariant "rule_1346"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1347"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_1348"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1349"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_1350"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheData = Sta.CurrData);;


ruleset j : NODE do
invariant "rule_1351"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Pending = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1352"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1353"
		(Home != i) ->	(Sta.Proc[i].InvMarked = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1354"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1355"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr = i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1356"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1357"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_1358"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1359"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_1360"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_1361"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1362"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_1363"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1364"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1365"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1366"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1367"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1368"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1369"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1370"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1371"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;
invariant "rule_1372"
	(Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE ; j : NODE do
invariant "rule_1373"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_1374"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1375"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1376"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1377"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
invariant "rule_1378"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
invariant "rule_1379"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1380"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1381"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE ; j : NODE do
invariant "rule_1382"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1383"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1384"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1385"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].InvMarked = false);
endruleset;
invariant "rule_1386"
	(Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_1387"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_1388"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_1389"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
invariant "rule_1390"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1391"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1392"
		(Home != i) ->	(Sta.Dir.HeadPtr = i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1393"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_1394"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1395"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1396"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrSet[i] = false);
endruleset;
invariant "rule_1397"
	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_1398"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1399"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_1400"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset j : NODE do
invariant "rule_1401"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1402"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1403"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1404"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1405"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
invariant "rule_1406"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE ; j : NODE do
invariant "rule_1407"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1408"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1409"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1410"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1411"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1412"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_1413"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.Local = false);
endruleset;


ruleset j : NODE do
invariant "rule_1414"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1415"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1416"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1417"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1418"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1419"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1420"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;
invariant "rule_1421"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE ; j : NODE do
invariant "rule_1422"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1423"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1424"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1425"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false);
endruleset;
invariant "rule_1426"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE ; j : NODE do
invariant "rule_1427"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1428"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1429"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd = NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1430"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1431"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_1432"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1433"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1434"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_1435"
	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.Proc[Home].CacheData = Sta.CurrData);;
invariant "rule_1436"
	(Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE do
invariant "rule_1437"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1438"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1439"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1440"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1441"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1442"
	(Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE do
invariant "rule_1443"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1444"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1445"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1446"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1447"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1448"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1449"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_1450"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_1451"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1452"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1453"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.Local = false);
endruleset;
invariant "rule_1454"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset j : NODE ; i : NODE do
invariant "rule_1455"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_1456"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = true -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_1457"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset i : NODE do
invariant "rule_1458"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1459"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1460"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_1461"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1462"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1463"
		(Home != i) ->	(Sta.Proc[i].InvMarked = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1464"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1465"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_1466"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_1467"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Pending = false -> Sta.Proc[Home].InvMarked = false);;
invariant "rule_1468"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.InvSet[Home] = false);;


ruleset j : NODE ; i : NODE do
invariant "rule_1469"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_1470"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Pending = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1471"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_1472"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_1473"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1474"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1475"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1476"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1477"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1478"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1479"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE do
invariant "rule_1480"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;
invariant "rule_1481"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.FwdCmd != UNI_GetX);;
invariant "rule_1482"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE ; i : NODE do
invariant "rule_1483"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1484"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1485"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1486"
	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);;
invariant "rule_1487"
	(Sta.Dir.ShrVld = true -> Sta.FwdCmd != UNI_GetX);;


ruleset j : NODE do
invariant "rule_1488"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1489"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Collecting = false);
endruleset;
invariant "rule_1490"
	(Sta.Dir.Pending = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1491"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1492"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1493"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1494"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1495"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1496"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.FwdCmd != UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1497"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1498"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1499"
	(Sta.Dir.HeadVld = true & Sta.Dir.Pending = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1500"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_1501"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_GetX);;
invariant "rule_1502"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_1503"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1504"
		(Home != j) ->	(Sta.Dir.HeadPtr = j & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1505"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1506"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1507"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1508"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1509"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1510"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1511"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1512"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1513"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_1514"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_1515"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset j : NODE do
invariant "rule_1516"
		(Home != j) ->	(Sta.Dir.HeadVld = true -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1517"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1518"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_I -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1519"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_1520"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1521"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1522"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);;
invariant "rule_1523"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.Proc[Home].CacheState = CACHE_I);;
invariant "rule_1524"
	(Sta.Dir.Pending = true -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE do
invariant "rule_1525"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1526"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1527"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE do
invariant "rule_1528"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_1529"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1530"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_I -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1531"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadVld = true);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1532"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1533"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_I);
endruleset;
invariant "rule_1534"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset i : NODE ; j : NODE do
invariant "rule_1535"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1536"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_1537"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;


ruleset j : NODE do
invariant "rule_1538"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1539"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1540"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_1541"
	(Sta.Dir.Dirty = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE ; j : NODE do
invariant "rule_1542"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1543"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1544"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1545"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1546"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1547"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1548"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE do
invariant "rule_1549"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1550"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Collecting = true);
endruleset;


ruleset j : NODE do
invariant "rule_1551"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrSet[j] = false);
endruleset;
invariant "rule_1552"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.FwdCmd = UNI_None);;


ruleset i : NODE do
invariant "rule_1553"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1554"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;
invariant "rule_1555"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE do
invariant "rule_1556"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1557"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE do
invariant "rule_1558"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_1559"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1560"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1561"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1562"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1563"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1564"
	(Sta.Dir.Local = true & Sta.Dir.HeadVld = false -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset j : NODE do
invariant "rule_1565"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1566"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1567"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1568"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1569"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1570"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1571"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1572"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1573"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1574"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Nak -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1575"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1576"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1577"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1578"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1579"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1580"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1581"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1582"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != Home -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1583"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1584"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.FwdCmd != UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1585"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1586"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1587"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1588"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr != Home);
endruleset;
invariant "rule_1589"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_1590"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset j : NODE do
invariant "rule_1591"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_1592"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_1593"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1594"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;
invariant "rule_1595"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_1596"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_1597"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1598"
		(Home != i) ->	(Sta.Proc[i].InvMarked = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1599"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1600"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1601"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1602"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1603"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1604"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_1605"
	(Sta.Dir.Local = false & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE ; j : NODE do
invariant "rule_1606"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;
invariant "rule_1607"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1608"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1609"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1610"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;
invariant "rule_1611"
	(Sta.Dir.Pending = true & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1612"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1613"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_1614"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1615"
		(Home != i) ->	(Sta.Dir.Pending = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1616"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1617"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1618"
		(Home != i) ->	(Sta.Dir.Dirty = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1619"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1620"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_1621"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1622"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1623"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1624"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset j : NODE do
invariant "rule_1625"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1626"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1627"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1628"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1629"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1630"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_1631"
	(Sta.Dir.HeadPtr != Home -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_1632"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1633"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_1634"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_1635"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_1636"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1637"
		(Home != i) ->	(Sta.Proc[i].InvMarked = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1638"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Pending = true);
endruleset;


ruleset i : NODE do
invariant "rule_1639"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1640"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1641"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1642"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_1643"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset i : NODE do
invariant "rule_1644"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1645"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1646"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_1647"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1648"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1649"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1650"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1651"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Collecting = false);
endruleset;
invariant "rule_1652"
	(Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr != Home);;


ruleset i : NODE ; j : NODE do
invariant "rule_1653"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1654"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_1655"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_1656"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Dir.ShrVld = false);;
invariant "rule_1657"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_1658"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1659"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1660"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1661"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_1662"
		(Home != j) ->	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_1663"
	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE ; j : NODE do
invariant "rule_1664"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1665"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.Local = false);
endruleset;


ruleset j : NODE do
invariant "rule_1666"
		(Home != j) ->	(Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
invariant "rule_1667"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_1668"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE do
invariant "rule_1669"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1670"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.UniMsg[j].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1671"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1672"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].InvMarked = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_1673"
		(Home != j) ->	(Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1674"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1675"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1676"
	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset j : NODE do
invariant "rule_1677"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_1678"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
invariant "rule_1679"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1680"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1681"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.FwdCmd = UNI_None);;


ruleset i : NODE ; j : NODE do
invariant "rule_1682"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1683"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1684"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1685"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1686"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1687"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1688"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1689"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_1690"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1691"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1692"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1693"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;
invariant "rule_1694"
	(Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1695"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1696"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1697"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1698"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.UniMsg[j].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1699"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_1700"
	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.ShrVld = false);;


ruleset i : NODE do
invariant "rule_1701"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.FwdCmd != UNI_Get);
endruleset;
invariant "rule_1702"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrVld = false);;


ruleset j : NODE do
invariant "rule_1703"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_1704"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1705"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1706"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1707"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1708"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.PendReqSrc = i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1709"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1710"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1711"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_1712"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1713"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1714"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1715"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1716"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1717"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1718"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.FwdCmd != UNI_GetX);
endruleset;
invariant "rule_1719"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset i : NODE do
invariant "rule_1720"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1721"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1722"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1723"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1724"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_1725"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE ; j : NODE do
invariant "rule_1726"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1727"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1728"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1729"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1730"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_1731"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1732"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1733"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_1734"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1735"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1736"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1737"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;
invariant "rule_1738"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset i : NODE ; j : NODE do
invariant "rule_1739"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1740"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1741"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1742"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_1743"
	(Sta.Dir.Pending = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].CacheState != CACHE_S);;
invariant "rule_1744"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].CacheData = Sta.CurrData);;


ruleset i : NODE ; j : NODE do
invariant "rule_1745"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_1746"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_1747"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd = UNI_None);;
invariant "rule_1748"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.FwdCmd = UNI_None);;


ruleset i : NODE do
invariant "rule_1749"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1750"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_1751"
		(Home != j) ->	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1752"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1753"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_1754"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE ; j : NODE do
invariant "rule_1755"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.PendReqSrc = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1756"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1757"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1758"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1759"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1760"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_1761"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Dir.HeadVld = false);;


ruleset i : NODE do
invariant "rule_1762"
		(Home != i) ->	(Sta.Proc[i].InvMarked = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
invariant "rule_1763"
	(Sta.Dir.ShrVld = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_1764"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1765"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1766"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1767"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;
invariant "rule_1768"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_1769"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1770"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1771"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1772"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.ShrSet[j] = false);
endruleset;
invariant "rule_1773"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_1774"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1775"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_1776"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1777"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1778"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1779"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1780"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_1781"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1782"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;
invariant "rule_1783"
	(Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_1784"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
invariant "rule_1785"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.Dir.Dirty = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1786"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1787"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_1788"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1789"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;
invariant "rule_1790"
	( -> );;
invariant "rule_1791"
	(Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE ; j : NODE do
invariant "rule_1792"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1793"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_1794"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1795"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1796"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE do
invariant "rule_1797"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_1798"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_1799"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1800"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1801"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE do
invariant "rule_1802"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1803"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1804"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1805"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1806"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1807"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1808"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1809"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1810"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1811"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;
invariant "rule_1812"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.FwdCmd != UNI_Get);;


ruleset j : NODE ; i : NODE do
invariant "rule_1813"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1814"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1815"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1816"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1817"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_1818"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1819"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1820"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1821"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Cmd = SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1822"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_1823"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1824"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1825"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1826"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1827"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1828"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1829"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1830"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;
invariant "rule_1831"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_S);;
invariant "rule_1832"
	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE do
invariant "rule_1833"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_1834"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1835"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
invariant "rule_1836"
	(Sta.Dir.ShrVld = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_1837"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1838"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1839"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE ; j : NODE do
invariant "rule_1840"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;
invariant "rule_1841"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_1842"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1843"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1844"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1845"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1846"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1847"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1848"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1849"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;
invariant "rule_1850"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.Dirty = true);;


ruleset i : NODE ; j : NODE do
invariant "rule_1851"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1852"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1853"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;
invariant "rule_1854"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_Get);;


ruleset j : NODE ; i : NODE do
invariant "rule_1855"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.FwdCmd != UNI_GetX);
endruleset;
invariant "rule_1856"
	(Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_1857"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1858"
	(Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_1859"
	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE ; j : NODE do
invariant "rule_1860"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1861"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1862"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1863"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1864"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_1865"
	(Sta.Dir.HeadVld = false -> Sta.Dir.ShrVld = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_1866"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_1867"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_1868"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1869"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;
invariant "rule_1870"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.MemData = Sta.CurrData);;


ruleset i : NODE ; j : NODE do
invariant "rule_1871"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_1872"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Local = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
invariant "rule_1873"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;
invariant "rule_1874"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset i : NODE do
invariant "rule_1875"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_1876"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_1877"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE do
invariant "rule_1878"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_1879"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;
invariant "rule_1880"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_1881"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1882"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_1883"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Proc[Home].CacheState = CACHE_E -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1884"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr = i);
endruleset;
invariant "rule_1885"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE do
invariant "rule_1886"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1887"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_1888"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
invariant "rule_1889"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1890"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_1891"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.FwdCmd != UNI_GetX);;


ruleset i : NODE do
invariant "rule_1892"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_1893"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1894"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Local = true -> Sta.Dir.ShrSet[i] = false);
endruleset;
invariant "rule_1895"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_1896"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_1897"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1898"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1899"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_1900"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE ; j : NODE do
invariant "rule_1901"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1902"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.HeadPtr != i -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1903"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1904"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1905"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1906"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1907"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_1908"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1909"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1910"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_1911"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1912"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_1913"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1914"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != Home);
endruleset;


ruleset i : NODE do
invariant "rule_1915"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1916"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1917"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1918"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1919"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_1920"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1921"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadVld = true);
endruleset;
invariant "rule_1922"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_1923"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1924"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_1925"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].ProcCmd = NODE_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1926"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;
invariant "rule_1927"
	(Sta.Dir.HeadVld = true & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_1928"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1929"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_1930"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1931"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1932"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE do
invariant "rule_1933"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].ProcCmd != NODE_None);
endruleset;


ruleset j : NODE do
invariant "rule_1934"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_1935"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_1936"
	(Sta.Dir.Pending = true & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset j : NODE do
invariant "rule_1937"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE do
invariant "rule_1938"
		(Home != j) ->	(Sta.Dir.HeadPtr = j & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_1939"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.FwdCmd = UNI_None);
endruleset;
invariant "rule_1940"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].CacheData = Sta.CurrData);;


ruleset i : NODE ; j : NODE do
invariant "rule_1941"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1942"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1943"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1944"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1945"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1946"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1947"
		(Home != i) ->	(Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_1948"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_1949"
	(Sta.Dir.Local = true & Sta.Dir.HeadVld = false -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE do
invariant "rule_1950"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_1951"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE ; j : NODE do
invariant "rule_1952"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1953"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1954"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1955"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1956"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1957"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.InvSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1958"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1959"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_1960"
	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_1961"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1962"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1963"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1964"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_1965"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1966"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_1967"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1968"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.FwdCmd != UNI_GetX);
endruleset;
invariant "rule_1969"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset j : NODE ; i : NODE do
invariant "rule_1970"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.ShrSet[j] = false);
endruleset;
invariant "rule_1971"
	(Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset j : NODE do
invariant "rule_1972"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_1973"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1974"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1975"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1976"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.PendReqSrc = j);
endruleset;


ruleset j : NODE do
invariant "rule_1977"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_Get);
endruleset;
invariant "rule_1978"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE ; j : NODE do
invariant "rule_1979"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1980"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_1981"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.FwdCmd != UNI_GetX);
endruleset;
invariant "rule_1982"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE ; j : NODE do
invariant "rule_1983"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_1984"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_1985"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1986"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_1987"
	(Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_S);;
invariant "rule_1988"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset i : NODE do
invariant "rule_1989"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE do
invariant "rule_1990"
		(Home != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1991"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_1992"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.MemData = Sta.PrevData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1993"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_1994"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_1995"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_1996"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_1997"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_1998"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_1999"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;
invariant "rule_2000"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_2001"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2002"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2003"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2004"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2005"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr = i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2006"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2007"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2008"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_2009"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2010"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_2011"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2012"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2013"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;
invariant "rule_2014"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_2015"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2016"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2017"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2018"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2019"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.FwdCmd != UNI_GetX);
endruleset;
invariant "rule_2020"
	(Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE ; j : NODE do
invariant "rule_2021"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_2022"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset i : NODE do
invariant "rule_2023"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2024"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2025"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2026"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2027"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2028"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2029"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2030"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2031"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2032"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2033"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.FwdCmd = UNI_None);
endruleset;
invariant "rule_2034"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset j : NODE do
invariant "rule_2035"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_2036"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_2037"
		(Home != i) ->	(Sta.Dir.Pending = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2038"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2039"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2040"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2041"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_2042"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2043"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2044"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != Home -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2045"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_2046"
	(Sta.Dir.Pending = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);;
invariant "rule_2047"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE ; j : NODE do
invariant "rule_2048"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_2049"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_2050"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2051"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2052"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2053"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2054"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2055"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2056"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
invariant "rule_2057"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2058"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2059"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2060"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2061"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2062"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2063"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2064"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2065"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2066"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2067"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.InvSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2068"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2069"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2070"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2071"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_2072"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2073"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_2074"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_2075"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_2076"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2077"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_2078"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2079"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2080"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_2081"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset i : NODE do
invariant "rule_2082"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2083"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;
invariant "rule_2084"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.Local = false);;


ruleset i : NODE do
invariant "rule_2085"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState = CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2086"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2087"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2088"
		(Home != i) ->	(Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2089"
		(Home != j) ->	(Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_2090"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_2091"
	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_2092"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2093"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_2094"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_2095"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2096"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2097"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_2098"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2099"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2100"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2101"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2102"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_2103"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2104"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2105"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2106"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2107"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2108"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_2109"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_2110"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_2111"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadVld = true);
endruleset;


ruleset j : NODE do
invariant "rule_2112"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2113"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2114"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2115"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE do
invariant "rule_2116"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_2117"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.UniMsg[j].Cmd != UNI_Put);
endruleset;
invariant "rule_2118"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Pending = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_2119"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_2120"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2121"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2122"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_2123"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2124"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd = SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_2125"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_2126"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2127"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2128"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2129"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2130"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_2131"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
invariant "rule_2132"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2133"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Cmd != UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_2134"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_Get);
endruleset;
invariant "rule_2135"
	(Sta.Dir.HeadPtr != Home -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_2136"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2137"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2138"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2139"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2140"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2141"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE do
invariant "rule_2142"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_2143"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2144"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_2145"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2146"
		(Home != j) ->	(Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2147"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2148"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2149"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2150"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2151"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2152"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Proc != i);
endruleset;
invariant "rule_2153"
	(Sta.Dir.Local = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset j : NODE do
invariant "rule_2154"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_I);
endruleset;
invariant "rule_2155"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2156"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2157"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2158"
		(Home != j) ->	(Sta.Dir.Dirty = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2159"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_2160"
	(Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2161"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2162"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2163"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2164"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2165"
		(Home != i) ->	(Sta.Proc[i].CacheState != CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2166"
		(Home != i) ->	(Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2167"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_2168"
	(Sta.Dir.Local = true -> Sta.FwdCmd = UNI_None);;


ruleset i : NODE do
invariant "rule_2169"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE do
invariant "rule_2170"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_2171"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadVld = false);;
invariant "rule_2172"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.MemData = Sta.CurrData);;


ruleset i : NODE do
invariant "rule_2173"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2174"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;
invariant "rule_2175"
	(Sta.Dir.Local = true & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;
invariant "rule_2176"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.WbMsg.Cmd != WB_Wb);;
invariant "rule_2177"
	(Sta.Dir.Local = true & Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);;
invariant "rule_2178"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.Dirty = true);;
invariant "rule_2179"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2180"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2181"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2182"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2183"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;
invariant "rule_2184"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2185"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2186"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != Home -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2187"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2188"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2189"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Proc != Home);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2190"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2191"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2192"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2193"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2194"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2195"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2196"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2197"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2198"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_2199"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2200"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2201"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2202"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Local = false);
endruleset;


ruleset i : NODE do
invariant "rule_2203"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2204"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2205"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2206"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_2207"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_2208"
	(Sta.Dir.Dirty = false -> Sta.MemData = Sta.CurrData);;


ruleset i : NODE ; j : NODE do
invariant "rule_2209"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2210"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2211"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_2212"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_2213"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2214"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2215"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2216"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2217"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2218"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Dir.ShrSet[j] = false);
endruleset;
invariant "rule_2219"
	(Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2220"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2221"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2222"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_2223"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE ; j : NODE do
invariant "rule_2224"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2225"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_2226"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_2227"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrSet[j] = false);
endruleset;
invariant "rule_2228"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_2229"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2230"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2231"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2232"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2233"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2234"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;
invariant "rule_2235"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_2236"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2237"
		(Home != i) ->	(Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2238"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Pending = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2239"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2240"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.HeadPtr != i -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2241"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2242"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_2243"
	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_2244"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2245"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_2246"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadVld = false);;


ruleset i : NODE do
invariant "rule_2247"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2248"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2249"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadVld = true);
endruleset;


ruleset j : NODE do
invariant "rule_2250"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2251"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;
invariant "rule_2252"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE do
invariant "rule_2253"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2254"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2255"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2256"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE do
invariant "rule_2257"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_2258"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2259"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Proc = Home);
endruleset;


ruleset i : NODE do
invariant "rule_2260"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2261"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2262"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_2263"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2264"
		(Home != i) ->	(Sta.Dir.HeadPtr != i -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_2265"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2266"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].CacheData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_2267"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2268"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_2269"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2270"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2271"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2272"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
invariant "rule_2273"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE do
invariant "rule_2274"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Local = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2275"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_2276"
	(Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset j : NODE ; i : NODE do
invariant "rule_2277"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_2278"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2279"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2280"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2281"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2282"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2283"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2284"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2285"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_2286"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Dir.ShrVld = false);;


ruleset i : NODE do
invariant "rule_2287"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2288"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_2289"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_2290"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2291"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2292"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.UniMsg[j].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2293"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;
invariant "rule_2294"
	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2295"
		(Home != i) ->	(Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_2296"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Dir.ShrVld = false);;
invariant "rule_2297"
	(Sta.Dir.HeadVld = true & Sta.Dir.Pending = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_2298"
		(Home != i) ->	(Sta.Proc[i].InvMarked = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2299"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2300"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE do
invariant "rule_2301"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].ProcCmd != NODE_None);
endruleset;
invariant "rule_2302"
	(Sta.Dir.Pending = false -> Sta.Collecting = false);;


ruleset i : NODE do
invariant "rule_2303"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2304"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2305"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr = i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2306"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.Pending = true);
endruleset;
invariant "rule_2307"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_2308"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Dir.HeadVld = false);
endruleset;
invariant "rule_2309"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;
invariant "rule_2310"
	(Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_2311"
	(Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE ; j : NODE do
invariant "rule_2312"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE do
invariant "rule_2313"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_2314"
	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Collecting = false);;


ruleset i : NODE do
invariant "rule_2315"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2316"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2317"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_2318"
	(Sta.Dir.Local = false & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].InvMarked = false);;
invariant "rule_2319"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2320"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_2321"
	(Sta.Dir.Dirty = false -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE do
invariant "rule_2322"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2323"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2324"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2325"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2326"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2327"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2328"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2329"
		(Home != j) ->	(Sta.Dir.Dirty = false -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_2330"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2331"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE do
invariant "rule_2332"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2333"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2334"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2335"
		(Home != j) ->	(Sta.Dir.HeadVld = true -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2336"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2337"
		(Home != j) ->	(Sta.Dir.HeadVld = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2338"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2339"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2340"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2341"
		(Home != j) ->	(Sta.Dir.Pending = false -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_2342"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2343"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Proc = i);
endruleset;


ruleset i : NODE do
invariant "rule_2344"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2345"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Local = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2346"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.FwdCmd != UNI_GetX);
endruleset;
invariant "rule_2347"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.ShrVld = false);;


ruleset i : NODE do
invariant "rule_2348"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2349"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2350"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2351"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2352"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.Pending = true);
endruleset;


ruleset i : NODE do
invariant "rule_2353"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Cmd = SHWB_FAck);
endruleset;
invariant "rule_2354"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_2355"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2356"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE do
invariant "rule_2357"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;
invariant "rule_2358"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset j : NODE ; i : NODE do
invariant "rule_2359"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;
invariant "rule_2360"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset j : NODE do
invariant "rule_2361"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2362"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2363"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2364"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2365"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2366"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2367"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE do
invariant "rule_2368"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2369"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2370"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2371"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2372"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2373"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE do
invariant "rule_2374"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2375"
		(Home != i) ->	(Sta.Dir.HeadPtr != i -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2376"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2377"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2378"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE do
invariant "rule_2379"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_2380"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2381"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_2382"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr = i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2383"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2384"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2385"
		(Home != i) ->	(Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2386"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Cmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_2387"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.Dir.InvSet[Home] = false);
endruleset;
invariant "rule_2388"
	(Sta.Dir.Local = true & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_2389"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_Get);
endruleset;
invariant "rule_2390"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_2391"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_2392"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.Local = true);
endruleset;


ruleset j : NODE do
invariant "rule_2393"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2394"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2395"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2396"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2397"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2398"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2399"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2400"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2401"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.Pending = true);
endruleset;


ruleset j : NODE do
invariant "rule_2402"
		(Home != j) ->	(Sta.Dir.HeadPtr != j -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2403"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_2404"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_2405"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr = i -> Sta.Dir.HeadVld = true);
endruleset;
invariant "rule_2406"
	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset j : NODE ; i : NODE do
invariant "rule_2407"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2408"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_2409"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_I -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_2410"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_2411"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_2412"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_2413"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2414"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_2415"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2416"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE do
invariant "rule_2417"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2418"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2419"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState != CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2420"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
invariant "rule_2421"
		(Home != j) ->	(Sta.Dir.Pending = true -> Sta.Dir.ShrSet[j] = false);
endruleset;
invariant "rule_2422"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_2423"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2424"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE do
invariant "rule_2425"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.Local = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2426"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2427"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2428"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.HeadPtr != j -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2429"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2430"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_2431"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2432"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2433"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2434"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2435"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != Home -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2436"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_2437"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState = CACHE_E);;


ruleset j : NODE ; i : NODE do
invariant "rule_2438"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Collecting = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2439"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE do
invariant "rule_2440"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2441"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2442"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2443"
		(Home != i) ->	(Sta.Dir.ShrVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2444"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;
invariant "rule_2445"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_2446"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2447"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2448"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.InvSet[j] = false);
endruleset;


ruleset j : NODE do
invariant "rule_2449"
		(Home != j) ->	(Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2450"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;
invariant "rule_2451"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_2452"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2453"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2454"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2455"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2456"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.PendReqSrc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2457"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2458"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2459"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2460"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.PendReqSrc != j);
endruleset;


ruleset i : NODE do
invariant "rule_2461"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Dir.Dirty = false);
endruleset;


ruleset i : NODE do
invariant "rule_2462"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_2463"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2464"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2465"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2466"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2467"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = true -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2468"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2469"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2470"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.PendReqSrc = i);
endruleset;


ruleset i : NODE do
invariant "rule_2471"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Cmd = SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_2472"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2473"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2474"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;
invariant "rule_2475"
	(Sta.Dir.Local = true & Sta.Dir.InvSet[Home] = false -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE do
invariant "rule_2476"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2477"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.ShrSet[i] = false);
endruleset;
invariant "rule_2478"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);;
invariant "rule_2479"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);;
invariant "rule_2480"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset i : NODE do
invariant "rule_2481"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2482"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[Home] = false -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2483"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_2484"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.FwdCmd != UNI_GetX);;


ruleset i : NODE do
invariant "rule_2485"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2486"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2487"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2488"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2489"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2490"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2491"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_2492"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2493"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_2494"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2495"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != Home);
endruleset;


ruleset i : NODE do
invariant "rule_2496"
		(Home != i) ->	(Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2497"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2498"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr = i -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_2499"
		(Home != j) ->	(Sta.Dir.HeadPtr = j & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState = CACHE_S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2500"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;
invariant "rule_2501"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.HeadVld = true);;


ruleset i : NODE ; j : NODE do
invariant "rule_2502"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2503"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2504"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2505"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_2506"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2507"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2508"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset j : NODE do
invariant "rule_2509"
		(Home != j) ->	(Sta.UniMsg[j].Cmd = UNI_GetX -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2510"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2511"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_2512"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.HeadPtr != Home);;


ruleset i : NODE ; j : NODE do
invariant "rule_2513"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2514"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2515"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2516"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2517"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2518"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2519"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_2520"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[Home].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE do
invariant "rule_2521"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_2522"
	(Sta.Dir.Dirty = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset j : NODE do
invariant "rule_2523"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.InvSet[j] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2524"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2525"
		(Home != i) ->	(Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2526"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2527"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2528"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Local = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2529"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_2530"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE do
invariant "rule_2531"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2532"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2533"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_2534"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE do
invariant "rule_2535"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_2536"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != Home);
endruleset;


ruleset j : NODE do
invariant "rule_2537"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2538"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2539"
		(Home != i) ->	(Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2540"
		(Home != i) ->	(Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2541"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2542"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2543"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Nak -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_2544"
	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;
invariant "rule_2545"
	(Sta.Dir.HeadPtr != Home -> Sta.Dir.HeadVld = true);;


ruleset i : NODE do
invariant "rule_2546"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2547"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_2548"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.HeadVld = false);
endruleset;
invariant "rule_2549"
	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset j : NODE do
invariant "rule_2550"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2551"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2552"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;
invariant "rule_2553"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE ; j : NODE do
invariant "rule_2554"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2555"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2556"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;
invariant "rule_2557"
	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_2558"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Dir.Dirty = true -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2559"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2560"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2561"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2562"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_2563"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2564"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2565"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset i : NODE do
invariant "rule_2566"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_2567"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_2568"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2569"
		(Home != i) ->	(Sta.Proc[i].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2570"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd = SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_2571"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2572"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2573"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2574"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2575"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2576"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2577"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2578"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_2579"
	(Sta.Dir.HeadVld = true & Sta.Dir.Pending = false -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_2580"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr = i);
endruleset;


ruleset j : NODE do
invariant "rule_2581"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2582"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2583"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2584"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2585"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2586"
		(Home != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2587"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_2588"
	(Sta.Dir.Local = true -> Sta.FwdCmd != UNI_Get);;


ruleset i : NODE do
invariant "rule_2589"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;
invariant "rule_2590"
	(Sta.Dir.HeadVld = false -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE ; j : NODE do
invariant "rule_2591"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2592"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2593"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2594"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2595"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.Dirty = true);
endruleset;
invariant "rule_2596"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE do
invariant "rule_2597"
		(Home != i) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2598"
		(Home != i) ->	(Sta.Dir.HeadVld = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2599"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2600"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_2601"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_2602"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2603"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2604"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2605"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2606"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2607"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2608"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.FwdCmd != UNI_Get);
endruleset;
invariant "rule_2609"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_GetX);;


ruleset i : NODE ; j : NODE do
invariant "rule_2610"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2611"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2612"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;
invariant "rule_2613"
	(Sta.Dir.HeadVld = true -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset j : NODE do
invariant "rule_2614"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr = j);
endruleset;
invariant "rule_2615"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrVld = false);;


ruleset j : NODE do
invariant "rule_2616"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2617"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Nak -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2618"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2619"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2620"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2621"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2622"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_2623"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.ShWbMsg.Proc = i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2624"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.HeadPtr != Home);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2625"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].InvMarked = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
invariant "rule_2626"
	(Sta.Dir.Dirty = true -> Sta.Dir.InvSet[Home] = false);;


ruleset j : NODE do
invariant "rule_2627"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2628"
		(Home != i) ->	(Sta.Dir.HeadVld = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2629"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.Dir.ShrVld = false);
endruleset;
invariant "rule_2630"
	(Sta.Dir.Dirty = true & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset i : NODE do
invariant "rule_2631"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Collecting = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2632"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2633"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2634"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2635"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_2636"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2637"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2638"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].CacheState = CACHE_E);
endruleset;
invariant "rule_2639"
	(Sta.Dir.HeadPtr != Home & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_2640"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.FwdCmd = UNI_None);
endruleset;
invariant "rule_2641"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset j : NODE do
invariant "rule_2642"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2643"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != Home);
endruleset;


ruleset j : NODE do
invariant "rule_2644"
		(Home != j) ->	(Sta.Dir.HeadVld = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2645"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2646"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_2647"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_2648"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2649"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2650"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2651"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2652"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_2653"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;
invariant "rule_2654"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2655"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_2656"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Dir.Local = false);;
invariant "rule_2657"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.FwdCmd != UNI_Get);;


ruleset j : NODE do
invariant "rule_2658"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2659"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
invariant "rule_2660"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset i : NODE do
invariant "rule_2661"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.PendReqSrc = i);
endruleset;


ruleset i : NODE do
invariant "rule_2662"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2663"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_2664"
		(Home != i) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2665"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2666"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE do
invariant "rule_2667"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2668"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2669"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2670"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
invariant "rule_2671"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = false -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_2672"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;
invariant "rule_2673"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset i : NODE ; j : NODE do
invariant "rule_2674"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd = SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_2675"
		(Home != i) ->	(Sta.Dir.Dirty = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2676"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.Pending = true);
endruleset;


ruleset j : NODE do
invariant "rule_2677"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;
invariant "rule_2678"
	(Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd != NODE_Get);;


ruleset j : NODE do
invariant "rule_2679"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_2680"
	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_2681"
	(Sta.Proc[Home].CacheState != CACHE_E -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_2682"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_2683"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2684"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2685"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2686"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_2687"
	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_2688"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_2689"
	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset j : NODE ; i : NODE do
invariant "rule_2690"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Dir.Dirty = false);
endruleset;


ruleset i : NODE do
invariant "rule_2691"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2692"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2693"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != Home & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_2694"
		(Home != j) ->	(Sta.Dir.Pending = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2695"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_2696"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2697"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_2698"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.Local = false);
endruleset;


ruleset i : NODE do
invariant "rule_2699"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_2700"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_2701"
	(Sta.Dir.HeadVld = true -> Sta.Proc[Home].InvMarked = false);;
invariant "rule_2702"
	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE do
invariant "rule_2703"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2704"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[i].Data = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_2705"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2706"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2707"
		(Home != j) ->	(Sta.Dir.HeadPtr != Home & Sta.Dir.Dirty = true -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2708"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2709"
		(Home != i) ->	(Sta.Proc[i].InvMarked = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2710"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2711"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2712"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2713"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE do
invariant "rule_2714"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2715"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2716"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2717"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2718"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Collecting = false);
endruleset;


ruleset i : NODE do
invariant "rule_2719"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.PendReqSrc = i);
endruleset;


ruleset i : NODE do
invariant "rule_2720"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2721"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2722"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.Dirty = true);
endruleset;


ruleset i : NODE do
invariant "rule_2723"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_2724"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);;
invariant "rule_2725"
	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[Home].InvMarked = false);;


ruleset j : NODE do
invariant "rule_2726"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;
invariant "rule_2727"
	(Sta.Dir.ShrVld = true -> Sta.Dir.Pending = false);;


ruleset i : NODE do
invariant "rule_2728"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2729"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2730"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2731"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2732"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.Dir.HeadVld = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2733"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_2734"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.Dirty = true);;


ruleset i : NODE do
invariant "rule_2735"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2736"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2737"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.InvSet[i] = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2738"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.UniMsg[j].Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_2739"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2740"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2741"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Dirty = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2742"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset j : NODE do
invariant "rule_2743"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset i : NODE do
invariant "rule_2744"
		(Home != i) ->	(Sta.Dir.Local = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2745"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2746"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2747"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2748"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2749"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_2750"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.FwdCmd != UNI_Get);;


ruleset i : NODE do
invariant "rule_2751"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_2752"
	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);;


ruleset j : NODE do
invariant "rule_2753"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2754"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2755"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2756"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2757"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr = j);
endruleset;


ruleset j : NODE do
invariant "rule_2758"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2759"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].ProcCmd != NODE_None);
endruleset;


ruleset j : NODE do
invariant "rule_2760"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2761"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2762"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadPtr = i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2763"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2764"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Cmd != UNI_Nak);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2765"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2766"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset i : NODE do
invariant "rule_2767"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2768"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.Proc[j].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_2769"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Pending = false -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2770"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Collecting = true);
endruleset;


ruleset i : NODE do
invariant "rule_2771"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState != CACHE_E -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2772"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2773"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2774"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2775"
		(Home != i) ->	(Sta.Dir.HeadPtr != i -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2776"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;
invariant "rule_2777"
	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE ; j : NODE do
invariant "rule_2778"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd = NODE_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_2779"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2780"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_2781"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2782"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_Inv & Sta.Proc[i].ProcCmd != NODE_Get -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2783"
		(Home != i) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2784"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2785"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_S -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2786"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != Home);
endruleset;
invariant "rule_2787"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.NakcMsg.Cmd != NAKC_Nakc);;


ruleset i : NODE ; j : NODE do
invariant "rule_2788"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2789"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2790"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2791"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;
invariant "rule_2792"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = true -> Sta.Dir.InvSet[Home] = false);;
invariant "rule_2793"
	(Sta.Dir.Pending = true & Sta.Dir.Local = true -> Sta.Proc[Home].ProcCmd = NODE_None);;


ruleset j : NODE ; i : NODE do
invariant "rule_2794"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2795"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2796"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.UniMsg[i].Cmd != UNI_Put);
endruleset;
invariant "rule_2797"
	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_2798"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2799"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true & Sta.Dir.InvSet[j] = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE do
invariant "rule_2800"
		(Home != j) ->	(Sta.Dir.HeadVld = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2801"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].ProcCmd != NODE_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_2802"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2803"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2804"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2805"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadVld = false -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2806"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset j : NODE do
invariant "rule_2807"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.InvMsg[j].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2808"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2809"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2810"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_2811"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2812"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.HeadPtr != i -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2813"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Dir.InvSet[i] = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2814"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2815"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[Home].CacheState != CACHE_S);
endruleset;


ruleset i : NODE do
invariant "rule_2816"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2817"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.ShrSet[i] = false);
endruleset;
invariant "rule_2818"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.Dir.ShrVld = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_2819"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2820"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = true -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2821"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.FwdCmd = UNI_None);
endruleset;


ruleset j : NODE do
invariant "rule_2822"
		(Home != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[Home] = false -> Sta.Dir.ShrSet[j] = false);
endruleset;
invariant "rule_2823"
	(Sta.Dir.Pending = false & Sta.Dir.HeadVld = false -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE do
invariant "rule_2824"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Proc[Home].CacheState = CACHE_E -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2825"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_E -> Sta.InvMsg[i].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2826"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_Get & Sta.InvMsg[i].Cmd = INV_Inv -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2827"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2828"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Local = false & Sta.Dir.HeadPtr != i -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2829"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Local = true -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;
invariant "rule_2830"
	(Sta.Dir.ShrVld = true -> Sta.FwdCmd != UNI_Get);;


ruleset i : NODE do
invariant "rule_2831"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset i : NODE do
invariant "rule_2832"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE do
invariant "rule_2833"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2834"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j -> Sta.Dir.HeadPtr != j);
endruleset;


ruleset j : NODE do
invariant "rule_2835"
		(Home != j) ->	(Sta.Dir.Dirty = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2836"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE do
invariant "rule_2837"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2838"
		(Home != j & Home != i & j != i) ->	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = true -> Sta.UniMsg[j].Proc != j);
endruleset;


ruleset i : NODE do
invariant "rule_2839"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2840"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[i].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2841"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2842"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE do
invariant "rule_2843"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;
invariant "rule_2844"
	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.Pending = false -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE ; j : NODE do
invariant "rule_2845"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2846"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrVld = false);
endruleset;


ruleset j : NODE do
invariant "rule_2847"
		(Home != j) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2848"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadVld = false -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2849"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2850"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset i : NODE do
invariant "rule_2851"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.FwdCmd != UNI_GetX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2852"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2853"
		(Home != i) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2854"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_2855"
	(Sta.Dir.Dirty = false & Sta.Dir.HeadVld = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE do
invariant "rule_2856"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2857"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Cmd = UNI_GetX & Sta.UniMsg[j].Proc = j -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;
invariant "rule_2858"
	(Sta.Dir.ShrVld = true -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE do
invariant "rule_2859"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2860"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr != i -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2861"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2862"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.Dir.HeadPtr != i);
endruleset;
invariant "rule_2863"
	(Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset j : NODE ; i : NODE do
invariant "rule_2864"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.Pending = true);
endruleset;


ruleset i : NODE do
invariant "rule_2865"
		(Home != i) ->	(Sta.Dir.Local = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;
invariant "rule_2866"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE ; j : NODE do
invariant "rule_2867"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Proc = i);
endruleset;
invariant "rule_2868"
	(Sta.Dir.Dirty = false & Sta.Dir.Pending = false -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset i : NODE do
invariant "rule_2869"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Dir.Local = false);
endruleset;


ruleset i : NODE do
invariant "rule_2870"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;
invariant "rule_2871"
	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.Proc[Home].CacheState = CACHE_I);;


ruleset i : NODE ; j : NODE do
invariant "rule_2872"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.HeadPtr != i -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2873"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != Home -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2874"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2875"
		(Home != i) ->	(Sta.Proc[Home].CacheState = CACHE_E & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_2876"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
invariant "rule_2877"
	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.Dir.InvSet[Home] = false);;


ruleset i : NODE do
invariant "rule_2878"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Pending = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2879"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2880"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Dir.HeadPtr != Home);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2881"
		(Home != i & Home != j & i != j) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Proc[i].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2882"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd = NODE_None);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2883"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_Get & Sta.Dir.Local = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2884"
		(Home != i) ->	(Sta.Proc[i].CacheState = CACHE_E -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset j : NODE do
invariant "rule_2885"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Local = false -> Sta.InvMsg[j].Cmd != INV_Inv);
endruleset;


ruleset i : NODE do
invariant "rule_2886"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset j : NODE do
invariant "rule_2887"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.HeadVld = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2888"
		(Home != i) ->	(Sta.Dir.HeadPtr != i & Sta.Dir.Dirty = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2889"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true & Sta.Dir.InvSet[Home] = false -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2890"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.InvMsg[i].Cmd != INV_InvAck);
endruleset;


ruleset j : NODE do
invariant "rule_2891"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2892"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.Dirty = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2893"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.ShrVld = false);
endruleset;


ruleset i : NODE do
invariant "rule_2894"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2895"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset i : NODE do
invariant "rule_2896"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = true -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2897"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = false & Sta.Dir.HeadPtr != i -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2898"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState != CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2899"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Pending = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2900"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.Local = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2901"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_I -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2902"
		(Home != i) ->	(Sta.Proc[i].InvMarked = true -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;
invariant "rule_2903"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.FwdCmd = UNI_None);;
invariant "rule_2904"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE ; j : NODE do
invariant "rule_2905"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Proc = Home & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2906"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Proc[j].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2907"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2908"
		(Home != i) ->	(Sta.Dir.InvSet[i] = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;


ruleset j : NODE do
invariant "rule_2909"
		(Home != j) ->	(Sta.Dir.Dirty = false & Sta.Dir.Local = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2910"
		(Home != i) ->	(Sta.Dir.Dirty = false & Sta.Proc[Home].ProcCmd = NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset j : NODE do
invariant "rule_2911"
		(Home != j) ->	(Sta.Dir.HeadPtr != j -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;


ruleset i : NODE do
invariant "rule_2912"
		(Home != i) ->	(Sta.Dir.HeadPtr = i & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2913"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
invariant "rule_2914"
		(Home != j) ->	(Sta.InvMsg[j].Cmd = INV_InvAck -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2915"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Proc = i -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2916"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None -> Sta.Dir.InvSet[Home] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2917"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[i].ProcCmd != NODE_Get);
endruleset;


ruleset i : NODE do
invariant "rule_2918"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.MemData = Sta.CurrData);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2919"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.Dir.InvSet[i] = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2920"
		(Home != j) ->	(Sta.Dir.Local = false & Sta.Dir.Dirty = true -> Sta.Proc[j].InvMarked = false);
endruleset;
invariant "rule_2921"
	(Sta.Proc[Home].CacheState = CACHE_E -> Sta.ShWbMsg.Cmd != SHWB_FAck);;


ruleset i : NODE do
invariant "rule_2922"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2923"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_I -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE ; i : NODE do
invariant "rule_2924"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.UniMsg[Home].Cmd != UNI_Put);
endruleset;
invariant "rule_2925"
	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_I);;


ruleset i : NODE do
invariant "rule_2926"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState = CACHE_I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2927"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.ShrSet[i] = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2928"
		(Home != i & Home != j & i != j) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.Proc[i].CacheState != CACHE_E);
endruleset;


ruleset j : NODE do
invariant "rule_2929"
		(Home != j) ->	(Sta.Dir.HeadPtr != j & Sta.Proc[Home].CacheState = CACHE_E -> Sta.Dir.HeadVld = false);
endruleset;
invariant "rule_2930"
	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.UniMsg[Home].Cmd != UNI_Put);;


ruleset j : NODE ; i : NODE do
invariant "rule_2931"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_2932"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Local = true -> Sta.WbMsg.Cmd != WB_Wb);;


ruleset i : NODE do
invariant "rule_2933"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_Put & Sta.Proc[i].InvMarked = false -> Sta.ShWbMsg.Cmd != SHWB_ShWb);
endruleset;


ruleset j : NODE do
invariant "rule_2934"
		(Home != j) ->	(Sta.Dir.Pending = false -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2935"
		(Home != i) ->	(Sta.Proc[Home].ProcCmd = NODE_Get & Sta.Dir.HeadPtr = i -> Sta.Dir.Local = false);
endruleset;


ruleset j : NODE do
invariant "rule_2936"
		(Home != j) ->	(Sta.Dir.HeadVld = true & Sta.Dir.Local = true -> Sta.UniMsg[j].Cmd != UNI_PutX);
endruleset;
invariant "rule_2937"
	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);;


ruleset i : NODE ; j : NODE do
invariant "rule_2938"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].ProcCmd = NODE_GetX & Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.Dir.InvSet[i] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2939"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.HeadPtr != Home -> Sta.Dir.HeadVld = true);
endruleset;


ruleset i : NODE do
invariant "rule_2940"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.UniMsg[i].Cmd = UNI_GetX -> Sta.Proc[Home].InvMarked = false);
endruleset;
invariant "rule_2941"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.HeadVld = false -> Sta.Proc[Home].CacheData = Sta.CurrData);;


ruleset j : NODE ; i : NODE do
invariant "rule_2942"
		(Home != j & Home != i & j != i) ->	(Sta.UniMsg[j].Proc = j & Sta.UniMsg[j].Cmd = UNI_Get -> Sta.Dir.ShrSet[j] = false);
endruleset;


ruleset i : NODE do
invariant "rule_2943"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = false -> Sta.Collecting = false);
endruleset;


ruleset i : NODE do
invariant "rule_2944"
		(Home != i) ->	(Sta.InvMsg[i].Cmd = INV_InvAck -> Sta.NakcMsg.Cmd != NAKC_Nakc);
endruleset;


ruleset j : NODE do
invariant "rule_2945"
		(Home != j) ->	(Sta.Dir.InvSet[j] = true -> Sta.ShWbMsg.Proc != j);
endruleset;


ruleset j : NODE do
invariant "rule_2946"
		(Home != j) ->	(Sta.Dir.Local = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;
invariant "rule_2947"
	(Sta.Dir.Dirty = true -> Sta.Proc[Home].InvMarked = false);;


ruleset i : NODE ; j : NODE do
invariant "rule_2948"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState = CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Dir.Pending = true);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2949"
		(Home != i & Home != j & i != j) ->	(Sta.UniMsg[i].Cmd = UNI_PutX -> Sta.PendReqSrc != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2950"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.Pending = true & Sta.RpMsg[i].Cmd != RP_Replace -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE do
invariant "rule_2951"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Local = true -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2952"
		(Home != i) ->	(Sta.Proc[i].ProcCmd = NODE_None & Sta.Proc[i].CacheState = CACHE_S -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2953"
		(Home != i & Home != j & i != j) ->	(Sta.Proc[i].CacheState != CACHE_E & Sta.UniMsg[i].Cmd = UNI_Get -> Sta.Proc[i].CacheState != CACHE_S);
endruleset;


ruleset j : NODE do
invariant "rule_2954"
		(Home != j) ->	(Sta.Proc[Home].CacheState != CACHE_E & Sta.Dir.Local = true -> Sta.Proc[j].CacheState != CACHE_E);
endruleset;


ruleset i : NODE do
invariant "rule_2955"
		(Home != i) ->	(Sta.Dir.HeadVld = true & Sta.Proc[Home].ProcCmd != NODE_Get -> Sta.ShWbMsg.Proc != i);
endruleset;


ruleset i : NODE do
invariant "rule_2956"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Pending = true -> Sta.Dir.HeadPtr != i);
endruleset;


ruleset j : NODE do
invariant "rule_2957"
		(Home != j) ->	(Sta.Dir.Dirty = true & Sta.Dir.InvSet[Home] = false -> Sta.ShWbMsg.Proc != j);
endruleset;
invariant "rule_2958"
	(Sta.Dir.Pending = false & Sta.Dir.Local = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset j : NODE do
invariant "rule_2959"
		(Home != j) ->	(Sta.Dir.Pending = false & Sta.Dir.Dirty = true -> Sta.Dir.InvSet[j] = false);
endruleset;
invariant "rule_2960"
	(Sta.Proc[Home].CacheState = CACHE_E & Sta.Dir.Dirty = true -> Sta.NakcMsg.Cmd != NAKC_Nakc);;
invariant "rule_2961"
	(Sta.Dir.ShrVld = true -> Sta.Dir.InvSet[Home] = false);;


ruleset j : NODE ; i : NODE do
invariant "rule_2962"
		(Home != j & Home != i & j != i) ->	(Sta.InvMsg[j].Cmd = INV_InvAck & Sta.Dir.InvSet[j] = true -> Sta.Dir.HeadVld = false);
endruleset;
invariant "rule_2963"
	(Sta.Dir.Local = false & Sta.Dir.InvSet[Home] = false -> Sta.Proc[Home].CacheState != CACHE_S);;


ruleset i : NODE do
invariant "rule_2964"
		(Home != i) ->	(Sta.UniMsg[i].Proc = Home & Sta.Dir.Dirty = false -> Sta.UniMsg[Home].Cmd != UNI_PutX);
endruleset;


ruleset i : NODE do
invariant "rule_2965"
		(Home != i) ->	(Sta.Proc[i].InvMarked = true -> Sta.ShWbMsg.Cmd != SHWB_FAck);
endruleset;
invariant "rule_2966"
	(Sta.Dir.Dirty = false & Sta.Dir.Local = true -> Sta.Proc[Home].CacheState != CACHE_E);;


ruleset i : NODE do
invariant "rule_2967"
		(Home != i) ->	(Sta.Proc[i].InvMarked = false -> Sta.Proc[Home].InvMarked = false);
endruleset;


ruleset i : NODE do
invariant "rule_2968"
		(Home != i) ->	(Sta.UniMsg[i].Cmd = UNI_GetX & Sta.Dir.HeadPtr != i -> Sta.WbMsg.Cmd != WB_Wb);
endruleset;


ruleset i : NODE do
invariant "rule_2969"
		(Home != i) ->	(Sta.RpMsg[i].Cmd = RP_Replace & Sta.Dir.ShrVld = true -> Sta.FwdCmd != UNI_Get);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2970"
		(Home != i & Home != j & i != j) ->	(Sta.Dir.InvSet[i] = true -> Sta.UniMsg[i].Cmd != UNI_PutX);
endruleset;
