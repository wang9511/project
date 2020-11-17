const 
    num_NODEs : 2;

type 
    NODE : 1..num_NODEs;
    locationType: enum{M, OSTATUS, E, S, I};

var 
    a : array[NODE] of locationType;
    ABS_NODE : union {NODE, enum{Other}};
ruleset i : NODE do
rule "rule_t1"
    a[i] = E ==>
begin
    a[i] := M;
endrule;endruleset;

ruleset i : NODE do
rule "rule_t2"
    a[i] = I ==>
begin
    for j: NODE do
        if (j = i)
            then a[j] := S;
        elsif (a[j] = E)
            then a[j] := S;
        elsif (a[j] = M)
            then a[j] := OSTATUS;
        else a[j] := a[j];
        endif;
        endfor;
endrule;
endruleset;

ruleset i : NODE do
rule "rul_t3"
    a[i] = S ==>
begin
    for j: NODE do
    if (j = i) then a[j] := E;
    else a[j] := I;
    endif;
    endfor;
endrule;
endruleset;

ruleset i : NODE do
rule "rul_t4"
    a[i] = OSTATUS
==>
begin
    for j: NODE do
    if (j = i) then a[j] := E;
    else a[j] := I;
    endif;
    endfor;
endrule;endruleset;

ruleset i : NODE do
rule "rul_t5"
    a[i] = I ==>
begin
    for j: NODE do
    if (j = i) then a[j] := E;
    else a[j] := I;
    endif;
    endfor;
endrule;
endruleset;

startstate
begin
 for i: NODE do
    a[i] := I; 
  endfor; 
endstartstate;


invariant "Moesi"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (a[i] = M -> a[j] != M
)
 end  end ;




-- No abstract rule for rule rule_t1


rule "n_ABS_rule_t2_NODE_1"

	forall NODE_2 : NODE do
		a[NODE_2] = I &
		a[NODE_2] != E &
		a[NODE_2] != OSTATUS &
		a[NODE_2] != M &
		a[NODE_2] != S
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other)
            then a[NODE_2] := S ;
		elsif (a[NODE_2] = E)
            then a[NODE_2] := S ;
		elsif (a[NODE_2] = M)
            then a[NODE_2] := OSTATUS ;
		else a[NODE_2] := a[NODE_2] ;
		endif
 ;
	endfor;
endrule;
rule "n_ABS_rul_t3_NODE_1"

	forall NODE_2 : NODE do
		a[NODE_2] != I &
		a[NODE_2] != OSTATUS &
		a[NODE_2] != E &
		a[NODE_2] != M
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other) then a[NODE_2] := E ;
		else a[NODE_2] := I ;
		endif
 ;
	endfor;
endrule;
rule "n_ABS_rul_t4_NODE_1"

	forall NODE_2 : NODE do
		a[NODE_2] != I &
		a[NODE_2] != OSTATUS &
		a[NODE_2] = S &
		a[NODE_2] != M &
		a[NODE_2] != E
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other) then a[NODE_2] := E ;
		else a[NODE_2] := I ;
		endif
 ;
	endfor;
endrule;
rule "n_ABS_rul_t5_NODE_1"

	forall NODE_2 : NODE do
		a[NODE_2] = I &
		a[NODE_2] != E &
		a[NODE_2] != OSTATUS &
		a[NODE_2] != M &
		a[NODE_2] != S
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other) then a[NODE_2] := E ;
		else a[NODE_2] := I ;
		endif
 ;
	endfor;
endrule;

ruleset i : NODE ; j : NODE do
invariant "rule_1"
		(i != j) ->	(a[i] = OSTATUS -> a[i] != I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_2"
		(i != j) ->	(a[i] = OSTATUS -> a[i] != M);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_3"
		(i != j) ->	(a[i] = I -> a[i] != OSTATUS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_4"
		(i != j) ->	(a[i] = S -> a[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_5"
		(i != j) ->	(a[i] = I -> a[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_6"
		(i != j) ->	(a[i] = OSTATUS -> a[i] != OSTATUS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_7"
		(i != j) ->	(a[i] = S -> a[i] != M);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_8"
		(i != j) ->	(a[i] = S -> a[i] != OSTATUS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_9"
		(i != j) ->	(a[i] = E -> a[i] != OSTATUS);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_10"
		(i != j) ->	(a[i] = E -> a[i] != E);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_11"
		(i != j) ->	(a[i] = I -> a[i] != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_12"
		(i != j) ->	(a[i] = E -> a[i] != M);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_13"
		(i != j) ->	(a[i] = E -> a[i] != S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_14"
		(i != j) ->	(a[i] = I -> a[i] != M);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_15"
		(i != j) ->	(a[i] = S -> a[i] != I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_16"
		(i != j) ->	(a[i] = E -> a[i] = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_17"
		(i != j) ->	(a[i] = I -> a[i] = I);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_18"
		(i != j) ->	(a[i] = OSTATUS -> a[i] = S);
endruleset;


ruleset i : NODE ; j : NODE do
invariant "rule_19"
		(i != j) ->	(a[i] = OSTATUS -> a[i] != E);
endruleset;
