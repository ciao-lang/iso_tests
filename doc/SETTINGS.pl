:- module(_, [], [doccfg]).

%! \title Config for iso_tests reference manual

:- include(core_docsrc(common/'LPDOCCOMMON')).

filepath := at_bundle(ciaodbg, 'lib').
filepath := ~ciaofilepath_common.

output_name := 'iso_tests'.

doc_structure := 'iso_tests_doc'.

bibfile := ~ciao_bibfile.

allow_markdown   := yes.
syntax_highlight := no.
