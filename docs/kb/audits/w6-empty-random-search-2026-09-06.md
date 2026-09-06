# W6 empty candidate handling

The W6 three-witness random search dereferenced `best` even when every trial failed its pair-law filter. A concrete reproduction with one trial and seed 12 raised `TypeError: NoneType object is not subscriptable`. It now reports that no admissible family was found in the requested trials and returns None, explicitly leaving the search unresolved.

The failing seed and zero-trial case now return cleanly. A one-trial seed-zero run still reports its candidate with 60 balanced triples and maximum witness count eight. Search enumeration, predicates and candidate ranking are unchanged. No exhaustive infeasibility claim or completed retention review follows; the total remains 69 of 92.
