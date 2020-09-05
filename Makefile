all : util.vo atan2.vo atan2.html FrenetSerret.vo FrenetSerret.html egeof.vo egeof.html 

util.vo: util.v
	coqc util.v

atan2.vo : atan2.v util.vo
	coqc atan2.v

atan2.html : atan2.v atan2.vo
	coqdoc -g -utf8 atan2.v

FrenetSerret.vo : FrenetSerret.v util.vo atan2.vo
	coqc FrenetSerret.v

FrenetSerret.html : FrenetSerret.v FrenetSerret.vo
	coqdoc -g -utf8 FrenetSerret.v

atan2.tex :  atan2.v atan2.vo
	coqdoc -g -utf8 -latex atan2.v

egeof.vo : egeof.v util.vo atan2.vo FrenetSerret.vo
	coqc egeof.v

egeof.html : egeof.v egeof.vo
	coqdoc -g -utf8 egeof.v

egeof.tex :  egeof.v egeof.vo
	coqdoc -g -utf8 -latex egeof.v

clean :
	rm *.vo *.glob *.log *.out *.tex *.html *.aux *~
