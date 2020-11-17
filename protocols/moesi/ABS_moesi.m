const 
    num_NODEs : 2;

type 
    NODE : scalarset(num_NODEs);
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


rule "ABS_rule_t2_NODE_1"

	forall NODE_2 : NODE do
		a[NODE_2] = I &
		a[NODE_2] != E &
		a[NODE_2] != S &
		a[NODE_2] != OSTATUS &
		a[NODE_2] != M
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
rule "ABS_rul_t3_NODE_1"

	forall NODE_2 : NODE do
		a[NODE_2] != OSTATUS &
		a[NODE_2] != E &
		a[NODE_2] != I &
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
rule "ABS_rul_t4_NODE_1"

	forall NODE_2 : NODE do
		a[NODE_2] = S &
		a[NODE_2] != I &
		a[NODE_2] != E &
		a[NODE_2] != OSTATUS &
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
rule "ABS_rul_t5_NODE_1"

	forall NODE_2 : NODE do
		a[NODE_2] = I &
		a[NODE_2] != E &
		a[NODE_2] != S &
		a[NODE_2] != OSTATUS &
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