:- module(_, _, [dcg, iso_strict, datafacts]).

:- use_module(library(stream_utils), [file_to_string/2]).
:- use_module(library(toplevel_proc)).
:- use_module(library(format), [format/2]).

main([File]):-
    file_to_string(File, TestStr), 
    main_(_, TestStr, []).
main([File, I]):-
    atom_number(I, N),
    file_to_string(File, TestStr), 
    main_(N, TestStr, []).

main_(N) -->
    ("PASSED: " -> get_passed; ""),
    loop(N), 
    {summary}.

summary:-
    retract_fact(counter(T, X)), 
    format("~w: ~w\n", [T, X]), 
    summary.
summary.

:- data passed/1.

failed(X):-
    \+ passed(X).

:- data counter/2.

incr(X):-
    (retract_fact(counter(X, N)) -> true ; N = 0), 
    M is N +1, 
    assertz_fact(counter(X, M)).
    

hide_known_results :-
    fail,
    true.

get_passed -->
    get_number(N), 
    (" "; ""), !,  
    {assertz_fact(passed(N))}, 
    get_passed.
get_passed --> "\n".

get_failed -->
    get_number(N), 
    (" "; ""), !, 
    {assertz_fact(failed(N))}, 
    get_failed.
get_failed --> "\n".

get_number(X) -->
    get_number_([H|T]), 
    {number_codes(X, [H|T])}.

get_number_([C|T]) -->
    [C], 
    {0'0 =< C, C =< 0'9}, !,
    get_number_(T).
get_number_([]) --> "".

loop(N) --> 
    "TEST: ", get_line(Id_), {number_codes(Id, Id_)}, 
    get_inits(Inits),
    get_input(Input), 
    get_eoutput(EOutput),
    {
        (var(N) ; N == Id) ->
         test(Id, Inits, Input, EOutput) 
    ; 
        %format("Test ~w skipped.\n", [Id])
        true
    }, 
    loop(N).
loop(_) --> "".
     

get_line([]) -->
    [0'\n], !.
get_line([C|T]) -->
    [C], 
    get_line(T).
 
get_inits([S|T]) -->
    "Init   : ", !,
    get_string(S), 
    "\n", 
    get_inits(T).
get_inits([]) --> [].

get_input(string(S)) -->
    "Input  : ", 
    get_string(S), 
    "\n".

get_eoutput(S) -->
    "Output : ",
    get_eoutput_(S), !,
    "\n".

get_eoutput_(waits) -->
    "<waits/>".
get_eoutput_(syntax_err) -->
    "<syntax_err\>".
get_eoutput_(succeeds) -->
    "<succeeds\>".
get_eoutput_(fails) -->
    "<fails\>".
get_eoutput_(string(S)) -->
    get_string(S).

get_string(S) -->
    "<string>", 
    get_string_(S).
get_string_([]) -->
    "</string>", !.
get_string_([C|T]) -->
    [C], 
    get_string_(T).

test(Id, Inits, Input, EOutput):-
%       message(user, 'start ciao'),    
    toplevel_proc:start(TL),
%       message(user, 'start test'),
    exec_test(TL, ["use_package(iso_strict)."|Inits], Input, Output), 
    toplevel_proc:kill(TL),
    compare_output(Id, Input, EOutput, Output, _).

compare_output(Id, string(Input), EOutput, Output, _) :-
    incr(total),
    (
       (
           EOutput = waits -> Output = waits
       ;
           EOutput = syntax_err -> Output = syntax_err
       ;
           EOutput = fails -> Output = no(_) 
       ;
           EOutput = succeeds -> Output =  yes(_)
       ;
           EOutput = string(ES) -> Output = yes(S), compare_string(ES, S)
       ) ->
       incr(success),
       (
           hide_known_results,  current_fact(passed(Id)) -> true 
       ;
           format("**** TEST ~w: PASSED ****\n", [Id])
       )
    ;
        incr(fail),
        (
             hide_known_results, failed(Id) -> true 
        ;
            format("**** TEST ~w : FAILED ****\n>>>> Input:\n~s\n", [Id, Input]),
            (
                EOutput = string(EOS) ->
                format(">>>> Expected Output:\n~s\n",  [EOS])
            ;
                format(">>>> Expected Output: ~w\n", [EOutput])
            ),
            (
                Output = yes(OS) ->
                format(">>>> Output: succeeds  with\n~s\n",  [OS])
            ;
                Output = no(OS) ->
                format(">>>> Output: fails  with\n~s\n",  [OS])
            ;
                format(">>>> Output:  ~w\n",  [Output])
            )
        )
    ).

compare_string([C|T1], [C|T2]) :-
    compare_string(T1, T2).
compare_string(" "||T1, "\n"||T2):-
    compare_string(T1, T2).
compare_string([], _).

exec_test(TL, Inits, string(Input), Output):-
    inits(Inits, TL),
    toplevel_proc:format(TL, "~s\n\n", [Input]), 
    (
        toplevel_proc:wait_for_answer(TL, Str, EStr, 1000000) ->
        (
            get_error(Output, EStr, _) ->
            true
        ;
            get_output(Output, Str, _)
        )
        
    ;
        Output = waits
    ).


inits([], _TL).
inits([H|T], TL):-
    toplevel_proc:format(TL, "~s\n", [H]), 
    toplevel_proc:wait_for_answer(TL, _, _, 100000),
    inits(T, TL).

get_str(S) -->
    {get_code(S, C), C > 0}, !, 
    [C], 
    get_str(S).
get_str(_) --> [].

get_error(syntax_err) -->
    "{SYNTAX ERROR:", !.
get_error(X) -->
    [_], 
     get_error(X).
 
get_output(X) -->
    "\n",
    get_output_(S, T), !,
    {
        T = yes -> 
        X = yes(S)
    ;
        T = no ->
        X = no(S)
    ;
        T = dieds ->
        X = dieds
    }.
get_output_([], yes) --> 
    "yes".
get_output_([], no) --> 
    "no".
get_output_([], dieds) -->
    [-1].
get_output_([C|T], Ty) -->
    [C],
    get_output_(T, Ty).


t --> 
    [A,B,C,D,E,F,G, H], 
    {format("~s\n", [A,B,C,D,E,F,G, H])}, 
    {fail}.
t --> [].

