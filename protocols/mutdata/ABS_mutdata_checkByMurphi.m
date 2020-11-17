const 
    NODENUMS : 2;
	  DATANUMS: 2;
			
type 
     state : enum{I, T, C, E};

     DATA: scalarset(DATANUMS);

     status : record st:state; data: DATA; end;
     
     NODE: scalarset(NODENUMS);

var n : array [NODE] of status;

    x : boolean; 
    
    auxDATA : DATA;
    
    memDATA: DATA;
    

ruleset i : NODE do
rule "Try" 
      n[i].st = I 
==>
begin
      n[i].st := T;
endrule;endruleset;


ruleset i : NODE do
rule "Crit"
      n[i].st = T & 
      x = true 
==>
begin
      n[i].st := C;
      x := false;
      n[i].data := memDATA; 
endrule;endruleset;


ruleset i : NODE do
rule "Exit"
      n[i].st = C 
==>
begin
      n[i].st := E;
endrule;endruleset;
      
 
ruleset i : NODE do
rule "Idle"
      n[i].st = E 
==>
begin 
      n[i].st := I;
      x := true; 
      memDATA := n[i].data; 
endrule;endruleset;

ruleset i : NODE; data : DATA do rule "Store"
	n[i].st = C
==>
begin
      auxDATA := data;
      n[i].data := data; 
endrule;endruleset;    

ruleset d : DATA do 
startstate
begin
 for i: NODE do
    n[i].st := I; 
    n[i].data:=d;
  endfor;
  x := true;
  auxDATA := d;
  memDATA:=d;
endstartstate;
endruleset;


ruleset i: NODE; j: NODE do
invariant "coherence"
  i != j -> (n[i].st = C -> n[j].st != C);
endruleset;

ruleset i:NODE  do 
invariant "c51"

  (n[i].st= C -> n[i].data =auxDATA);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_27"
		(i != j) ->	(n[j].st = E -> n[i].st != E);
endruleset;


ruleset j : NODE do
Invariant "rule_15"
	(n[j].st = C -> n[j].data = auxDATA);
endruleset;


ruleset j : NODE do
Invariant "rule_22"
	(n[j].st = C -> x = false);
endruleset;


ruleset j : NODE do
Invariant "rule_3"
	(n[j].st = E -> x = false);
endruleset;


ruleset j : NODE do
Invariant "rule_39"
	(n[j].st = E -> n[j].data = auxDATA);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_48"
		(i != j) ->	(n[j].st = E -> n[i].st != C);
endruleset;


ruleset i : NODE do
Invariant "rule_52"
	(n[i].data != auxDATA -> n[i].st != C);
endruleset;


ruleset j : NODE do
Invariant "rule_9"
	(x = true -> n[j].st != C);
endruleset;


ruleset j : NODE do
Invariant "rule_19"
	(x = true -> n[j].st != E);
endruleset;


ruleset j : NODE do
Invariant "rule_21"
	(n[j].data != auxDATA -> n[j].st != C);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_10"
		(i != j) ->	(n[j].st = C -> n[i].st != C);
endruleset;


ruleset j : NODE do
Invariant "rule_63"
	(n[j].st != T & n[j].st != I -> x = false);
endruleset;


ruleset j : NODE do
Invariant "rule_55"
	(n[j].data != auxDATA -> n[j].st != E);
endruleset;


ruleset i : NODE do
Invariant "rule_49"
	(x = true -> n[i].st != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_31"
		(i != j) ->	(n[i].data != auxDATA -> n[j].data = auxDATA);
endruleset;


ruleset i : NODE do
Invariant "rule_37"
	(n[i].data != auxDATA -> n[i].st != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_46"
		(i != j) ->	(n[j].st = C -> n[i].st != E);
endruleset;


ruleset i : NODE do
Invariant "rule_29"
	(x = true -> n[i].st != C);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_25"
		(i != j) ->	(n[j].data != auxDATA -> n[i].data = auxDATA);
endruleset;
