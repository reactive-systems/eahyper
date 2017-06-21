VERSION=3.3.5
#SVNVERSION=`svnversion .`
SVNVERSION=$(word 2,$$Rev: 2013 $$)
#DEBUG=-g
DEBUG=-O3 -g

STATIC=
#STATIC=-static 

WSIZE:=$(shell if [ `uname -m` = 'x86_64' ] ; then echo 64; else echo 32; fi )

CFLAGS=-Dtmpdebug -Wall -DVERSION=\"$(VERSION)\" -DSVNVERSION=\"$(SVNVERSION)\" -DWSIZE=$(WSIZE) -fpermissive
LDFLAGS=-Wl,--build-id $(STATIC)

SRC=runsolver.cc SignalNames.cc
OBJ=$(SRC:.cc=.o)

all:runsolver

install: runsolver
	cp runsolver $(INSTROOT)/usr/bin

include $(SRC:.cc=.d)

.cc.o:
	g++ $(CFLAGS) $(DEBUG) -c $*.cc

runsolver: $(OBJ)
	g++  $(LDFLAGS) $(DEBUG) -o $@ $^ -pthread

testlimit: testlimit.cc
	g++ -o testlimit testlimit.cc

testthread: testthread.cc
	g++ -o testthread testthread.cc -pthread

.PHONY: clean realclean archive

tar: /tmp/runsolver-$(VERSION).tar.bz2
archive: /tmp/runsolver-$(VERSION).tar.bz2

/tmp/runsolver-$(VERSION).tar.bz2: realclean $(SRC) Makefile
	sed -i -e 's/^Version:.*/Version:\t'$(VERSION)'/' runsolver.spec
	tar cvjf /tmp/runsolver-$(VERSION).tar.bz2 -C ../.. runsolver/src --exclude .svn

rpm: /tmp/runsolver-$(VERSION).tar.bz2
	rpmbuild -tb /tmp/runsolver-$(VERSION).tar.bz2

srpm: /tmp/runsolver-$(VERSION).tar.bz2
	rpmbuild -ts /tmp/runsolver-$(VERSION).tar.bz2

clean:
	rm -f runsolver $(OBJ) *.class testlimit testtimestamper vlineSplitter testProcessTree runtestlimit testthread

realclean: clean
	rm -f *.d *~


%.d: %.cc
	$(SHELL) -ec '$(CC) -MM $(CFLAGS) $< \
	| sed -e '\''s/$*\.o[ :]*/$@ &/g'\'' > $@'


