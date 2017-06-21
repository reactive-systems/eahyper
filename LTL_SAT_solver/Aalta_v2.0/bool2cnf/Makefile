
a.out : lex parse
	cc parse.tab.c trans.c -ll
lex : 
	flex scan.l
parse : 
	bison parse.y

.PHONY : clean

clean : 
	rm a.out
