const 
    NODENUMS : 2;

type 
     state : enum{I, T, C, E};
     NODE: 1..NODENUMS;
     
var 
    n : array [NODE] of state;

    x : boolean; 
    
startstate "Init"
for i: NODE do
    n[i] := I; 
endfor;
x := true;
endstartstate;


ruleset i : NODE
do rule "Try"
  n[i] = I 
==> 
begin
  n[i] := T;
endrule;endruleset;


ruleset i : NODE
do rule "Crit"
  n[i] = T & x = true 
==>
begin
  n[i] := C; 
  x := false;
endrule;endruleset;

ruleset i : NODE
do rule "Exit"
  n[i] = C
==>
begin
  n[i] := E;
endrule;endruleset;

ruleset i : NODE
do rule "Idle"
  n[i] = E
==>
begin
  n[i] := I;
  x := true;

endrule;endruleset;

invariant "mutualEx"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (n[i] = C -> n[j] != C)
 end  end ;


-- No abstract rule for rule Try


rule "n_ABS_Crit_NODE_1"

	x = true
 	& 
	forall NODE_2 : NODE do
		n[NODE_2] != E &
		n[NODE_2] != I &
		n[NODE_2] != C &
		n[NODE_2] = T
	end
==>
begin
	x := false;
endrule;

-- No abstract rule for rule Exit


rule "n_ABS_Idle_NODE_1"

	forall NODE_2 : NODE do
		n[NODE_2] != E &
		x = false &
		n[NODE_2] != C
	end
==>
begin
	x := true;
endrule;

ruleset i : NODE do
invariant "rule_1"
	(n[i] = E -> x = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2"
		(i != j) ->	(x = true & n[i] = T -> n[i] != I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_3"
		(i != j) ->	(n[i] = C -> n[i] != C);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_4"
		(i != j) ->	(n[i] = C -> n[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_5"
		(i != j) ->	(x = true & n[i] = T -> n[i] != C);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_6"
		(i != j) ->	(n[i] = I -> n[i] != C);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_7"
		(i != j) ->	(n[i] = E -> n[i] != C);
endruleset;


ruleset i : NODE do
invariant "rule_8"
	(n[i] = I -> x = true);
endruleset;


ruleset j : NODE do
invariant "rule_9"
	(x = true -> n[j] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_10"
		(i != j) ->	(n[i] = T -> n[i] != C);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_11"
		(i != j) ->	(n[i] = T -> n[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_12"
		(i != j) ->	(n[i] = T -> n[i] != I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_13"
		(i != j) ->	(x = true & n[i] = T -> n[i] != E);
endruleset;


ruleset i : NODE do
invariant "rule_14"
	(n[i] = C -> x = false);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_15"
		(i != j) ->	(x = true & n[i] = T -> n[i] = T);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_16"
		(i != j) ->	(n[i] = I -> n[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_17"
		(i != j) ->	(n[i] = I -> n[i] != T);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_18"
		(i != j) ->	(n[i] = E -> n[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_19"
		(i != j) ->	(n[i] = I -> n[i] = I);
endruleset;


ruleset j : NODE do
invariant "rule_20"
	(x = true -> n[j] != C);
endruleset;
