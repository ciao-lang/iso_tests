:- module(iso_tests_common, [], [iso_strict]).

:- use_module(library(lists), [member/2]).

% ---------------------------------------------------------------------------
% TODO: copy of lists:sublist/2

% @var{List2} contains all the elements of @var{List1}
:- export(sublist/2).
sublist([], _).
sublist([Element|Residue], List) :-
    member(Element, List),
    sublist(Residue, List).

% ---------------------------------------------------------------------------
% TODO: duplicated stream_utils:read_string_to_end/2; remove once stream aliases are integrated

:- export(read_string_to_end/2).
read_string_to_end(S, L) :-
    get_code(S, C),
    ( C = -1 -> L = []
    ; L = [C|L0],
      read_string_to_end(S, L0)
    ).

:- export(read_bytes_to_end/2).
read_bytes_to_end(S, L) :-
    get_byte(S, C),
    ( C = -1 -> L = []
    ; L = [C|L0],
      read_bytes_to_end(S, L0)
    ).
