% --- files and uris --------------------------------------------------------
:- dynamic proofName/1.

% --- check to see if system or anyone loaded a fact for specifying the name of the proof
proof_name(Name) :- proofName(Name).

protocol_name(Name) :-
  Name = 'file://'.

remote_protocol_name(Name) :-
  Name = 'http://'.

proof_file(Name) :-
  working_directory(Dir,Dir),
  proof_name(Proof),
  string_concat(Dir,Proof,Name1),
  string_concat(Name1,'1',Name2),
  string_concat(Name2,'.owl',Name).

remote_proof_file(Name) :-
  tomcat_directory(Dir),
  proof_name(Proof),
  string_concat(Dir,Proof,Name1),
  string_concat(Name1,'.owl',Name).

tomcat_directory(Name) :-
  Name = 'C:/Users/Nicholas/Desktop/visko-prolog/'.

proof_uri(Label,URI) :-
  proof_file(FileName),
  string_length(FileName,L),
  M is L - 2,
  sub_string(FileName,2,M,_,FileName2),
  protocol_name(ProtocolName),
  string_concat(ProtocolName,FileName2,Tmp1),
  string_concat(Tmp1,'#',Tmp2),
  proof_name(ProofName),
  string_concat(Tmp2,ProofName,Tmp3),
  string_concat(Tmp3,'1_',Tmp4),
  string_concat(Tmp4,Label,URI).

remote_proof_uri(Label,URI) :-
  proof_name(ProofName),
  remote_protocol_name(ProtocolName),
  string_concat(ProtocolName,'iw.cs.utep.edu/dhs/examples/',Tmp0),
  string_concat(Tmp0,ProofName,Tmp1),
  string_concat(Tmp1,'.owl',Tmp2),
  string_concat(Tmp2,'#',Tmp3),
  string_concat(Tmp3,ProofName,Tmp4),
  string_concat(Tmp4,'_',Tmp5),
  string_concat(Tmp5,Label,URI).

uri_no_quote(URI,URInq) :-
  string_length(URI,L),
  N is L - 2,
  sub_string(URI,1,N,_,URInq).

shell_command(URI,Command) :-
  uri_no_quote(URI,URInq),
  string_concat('cmd.exe /c probeit ',URInq,Command).

% --- a main predicate: why(Goal) ----------------------------------------------

why(Goal) :-
  write('Generating proof tree file at '),
  proof_file(FileName),
  write(FileName),
  clause_tree(Goal,[],T),
  !, %% for now, print just the first answer.
  nl,
  label_tree(T,0,_,[],_,T2),
  dump_pml(T2),
  proof_uri('1',URI),
  writeln(URI),
  writeln('Loading Probe-It...'),
  shell_command(URI,Command),
  writeln(Command),
  shell(Command).
  %win_exec(Command,0).

% --- a main predicate: why(Goal, URI) ----------------------------------------------

why(Goal,URI) :-
% write('Generating proof tree file at '),
  remote_proof_file(FileName),
% write(FileName),
  clause_tree(Goal,[],T),
  !, %% for now, print just the first answer.
% nl,
  label_tree(T,0,_,[],_,T2),
  dump_pml(T2),
  remote_proof_uri('1',URI),
  !.

% --- String replace rules ---------------------------------------------------

replace(X,Y,[],[]).
replace(X,Y,[X|R],[Y|S]) :- replace(X,Y,R,S).
replace(X,Y,[F|R],[F|S]) :- replace(X,Y,R,S).


replaceLessThan(Input, Output) :- string_to_list(Input,List),replace(60,76,List,OutputList),!,string_to_list(Output,OutputList).
replaceGreaterThan(Input, Output) :- string_to_list(Input,List),replace(62,71,List,OutputList),!,string_to_list(Output,OutputList).

toLegalXML(Input, Output) :- term_to_atom(Input,InputA),replaceLessThan(InputA,NLT),replaceGreaterThan(NLT,Output).


% --- Meta-interpreter for building proof tree --------------------------------
% need to consider two different cases now, one for building standard conjunctive clause trees and one for building clause trees
% when disjuctive bodies are encountered

% base case, the most simple clause tree contains a root "true"
clause_tree(true,_,true) :- !.

% handles case when clause body is disjunctive,
clause_tree((G;R),Trail,TR) :-
   not(call(G)),
   call(R),
   clause_tree(R,Trail,TR).

clause_tree((G;R),Trail,TG) :-
   call(G),
   not(call(R)),
   clause_tree(G,Trail,TG).

clause_tree((G;R),Trail,(TG,TR)) :-
   !,
   clause_tree(G,Trail,TG),
   clause_tree(R,Trail,TR).

% handles the case when the clause body is conjunctive
clause_tree((G,R),Trail,(TG,TR)) :-
   !,
   writeln('conjunction found'),
   clause_tree(G,Trail,TG),
   clause_tree(R,Trail,TR).

% checks to see if a clause is built-in, if so let prolog prove it.
% this results in smaller proofs
clause_tree(G,_,CG) :-
   (predicate_property(G,built_in);
     predicate_property(G,compiled)),
   call(G),
   toLegalXML(G,CG).
   
% check for loops e.g., suppose t(X) :- a(X) and a(X) :- t(X), then a loop results
clause_tree(G,Trail,_) :-
   loop_detect(G,Trail),
   !,
   fail.

% builds a tree node for a clause
clause_tree(G,Trail,disjunctive_tree(G,([G,Body],T))) :-
   clause(G,Body),
   disjunctiveClause(Body),
   clause_tree(Body,[G|Trail],T).
   
clause_tree(G,Trail,tree(G,([G,Body],T))) :-
   clause(G,Body),
   clause_tree(Body,[G|Trail],T).
   
loop_detect(G,[G1,_]) :- G == G1.
loop_detect(G,[_,R]) :- loop_detect(G,R).

disjunctiveClause((_;_)).
% --- label_tree for labelling proof nodes with a unique number -------

label_tree(tree(Root,Branches),N1,N3,TA1,TA2,tree(A2,LB)) :- !,
  addOne(N1,N2),
  label_tree(Branches,N2,N3,[],A1,LB),
  append([N2,Root],A1,A2),
  append(TA1,[N2],TA2).

label_tree(disjunctive_tree(Root,Branches),N1,N3,TA1,TA2,disjunctive_tree(A2,LB)) :- !,
  addOne(N1,N2),
  label_tree(Branches,N2,N3,[],A1,LB),
  append([N2,Root],A1,A2),
  append(TA1,[N2],TA2).
  
label_tree((B,Bs),N1,N3,A1,A3,(TH,TR)) :- !,
  label_tree(B,N1,N2,A1,A2,TH),
  label_tree(Bs,N2,N3,A2,A3,TR).

label_tree(true,N,N,A,A,true) :- !.
label_tree(Node,N1,N2,A1,A2,[N2,Node]) :-
  addOne(N1,N2),
  append(A1,[N2],A2).

addOne(N,N1) :-
  N1 is N + 1.

% --- dumping_pml for dumping PML ---------------------------------------

dump_pml(Tree) :-
  telling(CurrentOutput), /* current write output */
  remote_proof_file(ProofFile), /* get proof file name */
  string_to_atom(ProofFile, AProofFile),
  tell(AProofFile), /* open this file */
  pml_header,
  draw_tree(Tree),
  pml_footer,
  told, /* close ToFile */
  tell(CurrentOutput). /* resume previous output */
  
draw_tree(tree(Root,Branches)) :- !,
   nodeset(Root),
   draw_tree(Branches).

draw_tree(disjunctive_tree(Root,Branches)) :- !,
   mis_nodeset(Root),
   draw_tree(Branches).
   
draw_tree((B,Bs)) :- !,
   draw_tree(B),
   draw_tree(Bs).

draw_tree(Node) :-
   hasDisjunctiveConclusion(Node),
   mis_nodeset(Node).
   
draw_tree(Node) :-
   nodeset(Node).
  
hasDisjunctiveConclusion((_;_)).

% --- predicates for printing pml elements ---------------------------

pml_header :-
  writeln('<rdf:RDF'),
  writeln(' xmlns:pmlp="http://inference-web.org/2.0/pml-provenance.owl#"'),
  writeln(' xmlns="http://inference-web.org/2.0/pml-justification.owl#"'),
  writeln(' xmlns:ds="http://inference-web.org/2.0/ds.owl#"'),
  writeln(' xmlns:rdf="http://www.w3.org/1999/02/22-rdf-syntax-ns#"'),
  writeln(' xmlns:rdfs="http://www.w3.org/2000/01/rdf-schema#"'),
  writeln(' xmlns:owl="http://www.w3.org/2002/07/owl#"'),
  writeln(' xmlns:daml="http://www.daml.org/2001/03/daml+oil#">').
  
pml_footer :-
  writeln('</rdf:RDF>').

mis_nodeset([Label|Node]) :-
  hasInferenceStepsAntecedents(Node,Conclusion,Rule,Antecedents),
  mis_nodeset(Label,Conclusion,Rule,Antecedents).
mis_nodeset(true).
mis_nodeset(Label,Conclusion,Rule,Antecedents) :-
  nodesetH(Label),
  conclusion(Conclusion),
  inferenceSteps(Rule,Antecedents),
  nodesetF.

nodeset([Label|Node]) :-
  hasAntecedents(Node,Conclusion,Antecedents),
  nodeset(Label,Conclusion,Antecedents).
nodeset(true).
nodeset(Label,Conclusion,Antecedents) :-
  nodesetH(Label),
  conclusion(Conclusion),
  inferenceStep(Antecedents),
  nodesetF.

hasAntecedents([Conclusion|Antecedents],Conclusion,Antecedents) :- !.
hasAntecedents([Conclusion],Conclusion,[]) :- !.

hasInferenceStepsAntecedents([Conclusion|[Rule|Antecedents]],Conclusion,Rule,Antecedents) :- !.

nodesetH(Label) :-
  write('<NodeSet rdf:about="'),
  remote_proof_uri(Label,URI),
  write(URI),
  write('"'),
  writeln('>').

nodesetF :-
  tab(3),
  writeln('</NodeSet>').
  
conclusion(Conclusion) :-
  tab(3),
  writeln('<hasConclusion>'),
  writeln('<pmlp:Information>'),
  writeln('<pmlp:hasRawString rdf:datatype="http://www.w3.org/2001/XMLSchema#string">'),
  renderConclusion(Conclusion),
  writeln('</pmlp:hasRawString>'),
  writeln('<pmlp:hasLanguage rdf:resource="http://inference-web.org/registry/LG/English.owl#English"/>'),
  writeln('</pmlp:Information>'),
  writeln('</hasConclusion>').
  

renderConclusion([C|true]) :-
  write(C),
  write('.').
renderConclusion([C]) :-
  write(C),
  write('.').
renderConclusion([Header|Body]) :-
  write(Header),
  write(' :- '),
  toLegalXML(Body, CleanBody),
  renderConclusionBody([CleanBody]),
  write('.').
renderConclusion(C) :-
  write(C),
  write('.').
renderConclusionBody([Body]) :-
  write(Body).

%---------------- Inference Steps -------------------------------
inferenceSteps(Rule,[]).
inferenceSteps(Rule,[Ante|Rest]) :-
  merge([Rule],[Ante],Antes),
  inferenceStep(Antes),
  inferenceSteps(Rule,Rest).

inferenceStep(Antecedents) :-
  tab(3),
  writeln('<isConsequentOf>'),
  tab(5),
  writeln('<InferenceStep>'),
  engine_and_rule(Antecedents),
  antecedents(Antecedents),
  writeln('</InferenceStep>'),
  tab(3),
  writeln('</isConsequentOf>').

engine_and_rule([]) :-
  tab(7),
  writeln('<hasInferenceEngine rdf:resource="http://inference-web.org/registry/IE/SWIPL.owl#SWIPL"/>'),
  writeln('<hasInferenceRule rdf:resource="http://inference-web.org/registry/DPR/Told.owl#Told"/>').

engine_and_rule(_) :-
  tab(7),
  writeln('<hasInferenceEngine rdf:resource="http://inference-web.org/registry/IE/SWIPL.owl#SWIPL"/>'),
  writeln('<hasInferenceRule rdf:resource="http://inference-web.org/registry/DPR/Hyp-Resolution.owl#Hyp-Resolution"/>').

antecedents([]).
antecedents(Antecedents) :-
  tab(7),
  writeln('<hasAntecedentList>'),
  oneAntecedent(Antecedents),
  tab(7),
  writeln('</hasAntecedentList>').

oneAntecedent([]).
oneAntecedent([A1|A2]) :-
  tab(7),
  writeln('<NodeSetList>'),
  tab(9),
  write('<ds:first rdf:resource="'),
  remote_proof_uri(A1,URI),
  write(URI),
  write('"'),
  writeln('/>'),
  restOfAntecedents(A2),
  tab(7),
  writeln('</NodeSetList>').
  
  
restOfAntecedents([]).
restOfAntecedents(A) :-
  tab(7),
  writeln('<ds:rest>'),
  oneAntecedent(A),
  tab(7),
  writeln('</ds:rest>').