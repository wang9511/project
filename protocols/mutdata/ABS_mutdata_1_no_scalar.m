const 
    NODENUMS : 2;
	  DATANUMS: 2;
			
type 
     state : enum{I, T, C, E};

     DATA: 1..DATANUMS;

     status : record st:state; data: DATA; end;
     
     NODE: 1..NODENUMS;

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


-- No abstract rule for rule Try


rule "n_ABS_Crit_NODE_1"

	x = true
 	& 
	forall NODE_2 : NODE do
		n[NODE_2].st != E &
		n[NODE_2].st != C
	end
==>
begin
	x := false;
endrule;

-- No abstract rule for rule Exit


rule "n_ABS_Idle_NODE_1"

	forall NODE_2 : NODE do
		x = false &
		n[NODE_2].st != E &
		n[NODE_2].st != C
	end
==>
begin
	x := true ;
	memDATA := auxDATA;
endrule;

ruleset DATA_1 : DATA do
rule "n_ABS_Store_NODE_1"

	forall NODE_2 : NODE do
		x = false &
		n[NODE_2].st != E &
		n[NODE_2].st != C
	end
==>
begin
	auxDATA := DATA_1;
endrule;
endruleset;



ruleset i : NODE ; j : NODE do
Invariant "rule_1"
		(i != j) ->	(n[i].st = C -> n[j].st != E);
endruleset;


ruleset j : NODE do
Invariant "rule_2"
	(x = true -> n[j].st != C);
endruleset;


ruleset i : NODE do
Invariant "rule_3"
	(n[i].st = E -> x = false);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_4"
		(i != j) ->	(n[i].st = E -> n[j].st != E);
endruleset;


ruleset i : NODE do
Invariant "rule_5"
	(n[i].st = C -> x = false);
endruleset;


ruleset i : NODE do
Invariant "rule_6"
	(n[i].st = E -> n[i].data = auxDATA);
endruleset;


ruleset j : NODE do
Invariant "rule_7"
	(x = true -> n[j].st != E);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_8"
		(i != j) ->	(n[i].st = C -> n[j].st != C);
endruleset;


ruleset i : NODE ; j : NODE do
Invariant "rule_9"
		(i != j) ->	(n[i].st = E -> n[j].st != C);
endruleset;
