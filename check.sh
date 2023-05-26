cargo creusot --output-file why3.mlcfg
why3 --extra-config why3conf/no_mbqi.conf prove why3.mlcfg -L ../creusot/prelude/ -P z3 -a split_vc -a eliminate_algebraic -t 15 --color $@