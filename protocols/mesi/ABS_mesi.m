const 
      NODENUMS : 2;
type 
     location: enum{ M, E, S, I};

     NODE : scalarset(NODENUMS);
    ABS_NODE : union {NODE, enum{Other}};

var 
    state : array [NODE] of location;

    
ruleset i : NODE do rule "t1"
    state[i] = E ==>
begin
    state[i]  :=  M;
    endrule; endruleset;

      
ruleset i : NODE do rule "t2"
    state[i] = I ==>
begin
  for j: NODE do
      if (j = i) then
        state[j] := S;
      elsif (state[j]=E) then
        state[j] := S;
      elsif (state[j]=M) then
        state[j] := S;
      elsif (state[j]=I) then
        state[j] := I;
      else   
        state[j] := S;
      endif;
  endfor; 
endrule;endruleset;
          

ruleset i : NODE 
do rule "t3"
      state[i] = S ==>
begin
  for j: NODE do
    if (j = i) then
      state[j] := E;
    else   
      state[j] := I;
    endif;
    endfor; 
endrule;endruleset;
      

ruleset i : NODE do rule "t4"
  state[i] = M
==>
begin
  for j: NODE do
      if (j = i) then
            state[j] := E ;
      else   
            state[j] := I;
      endif;
  endfor; 
endrule;
endruleset;

startstate
begin
 for i: NODE do
    state[i]  :=  I; 
  endfor; 
endstartstate;

invariant "Mesi"
forall i : NODE do forall j : NODE do 
i != j   -> 
  (state[i] = M -> state[j] != M
)
 end  end ;


-- No abstract rule for rule t1


rule "ABS_t2_NODE_1"

	forall NODE_2 : NODE do
		state[NODE_2] = I &
		state[NODE_2] != M &
		state[NODE_2] != E &
		state[NODE_2] != S
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other) then
        state[NODE_2] := S ;
		elsif (state[NODE_2]=E) then
        state[NODE_2] := S ;
		elsif (state[NODE_2]=M) then
        state[NODE_2] := S ;
		elsif (state[NODE_2]=I) then
        state[NODE_2] := I ;
		else   
        state[NODE_2] := S ;
		endif
 ;
	endfor;
endrule;
rule "ABS_t3_NODE_1"

	forall NODE_2 : NODE do
		state[NODE_2] != M &
		state[NODE_2] != I &
		state[NODE_2] != E &
		state[NODE_2] = S
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other) then
      state[NODE_2] := E ;
		else   
      state[NODE_2] := I ;
		endif
 ;
	endfor;
endrule;
rule "ABS_t4_NODE_1"

	forall NODE_2 : NODE do
		state[NODE_2] = I &
		state[NODE_2] != M &
		state[NODE_2] != E &
		state[NODE_2] != S
	end
==>
begin
	for NODE_2 : NODE do
		if (NODE_2 = Other) then
            state[NODE_2] := E ;
		else   
            state[NODE_2] := I ;
		endif
 ;
	endfor;
endrule;