:- bundle(iso_tests).
% An ISO Prolog test suite for Ciao
version('1.21.0').
depends([
  ciaodbg
]).
alias_paths([
  iso_tests = src
]).
manual('iso_tests', [main='doc/SETTINGS.pl']).
