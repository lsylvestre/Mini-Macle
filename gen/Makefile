
SRC=dram
DST=gen-platform

STACK_SIZE=6400
HEAP_SIZE=131072

DOT_VHDL=.vhdl

all:
	cp -R ../$(SRC) ../$(DST)

	mkdir -p ../$(DST)/rtl/misc
	for f in rtl/*.vhd rtl/misc/*.vhd; do (cp -R $${f} "../$(DST)/$${f}"); done
	for c in c/*platform-bindings.c ;  do (cat $${c} >> ../$(DST)/c/platform-bindings.c); done
	for c in c/*platform.c;            do (cat $${c} >> ../$(DST)/c/platform.c); done
	for c in c/*platform.h;            do (cat $${c} >> ../$(DST)/c/platform.h); done
	for c in c/*simul.c;               do (cat $${c} >> ../$(DST)/c/simul.c); done
	for c in c/*simul.h;               do (cat $${c} >> ../$(DST)/c/simul.h); done
	cat ml/prelude.ml >> ../$(DST)/ml/platform.mli
	cat ml/prelude.ml >> ../$(DST)/ml/platform.ml
	for c in ml/*platform.ml;          do (cat $${c} >> ../$(DST)/ml/platform.ml); done
	for c in ml/*platform.mli;         do (cat $${c} >> ../$(DST)/ml/platform.mli); done
	for f in apps; do (cp -R $${f} "../$(DST)/$${f}"); done

	for f in apps/*.ml ; do \
	  D=../$(DST)/apps/`basename $${f} ".ml"`;\
	  mkdir -p $${D};\
	  cat $${f} > "$${D}/main.ml";\
	  echo "PLATFORM_DIR=../..\nOMICROB_OPTS='-no-shortcut-initialization -stack-size $(STACK_SIZE) -heap-size $(HEAP_SIZE)'" > "$${D}/config";\
	  echo "../../../_etc/make_makefiles" > "$${D}/make_makefiles";\
	  chmod 755 "$${D}/make_makefiles";\
	done

	for f in qsys/*_hw.tcl; do (cp -R $${f} "../$(DST)/$${f}"); done
	cat qsys/platform.tcl > "../$(DST)/qsys/platform_hw.tcl"
	for f in qsys/*_ext.tcl; do (cat $${f} >> "../$(DST)/qsys/platform_hw.tcl"); done
	echo "save_system platform.qsys" >> "../$(DST)/qsys/platform_hw.tcl"

	# '-' ignore les erreurs
	-(cd ../$(DST)/qsys/ ; rm -R platform.qsys; qsys-script --script=platform_hw.tcl) 

	qsys-generate --synthesis=VHDL ../$(DST)/qsys/platform.qsys

	cp bsp/bsp_update.tcl ../$(DST)/bsp/bsp_update.tcl

	(cd ../$(DST); nios2-bsp-update-settings --script=bsp/bsp_update.tcl --bsp-dir=bsp --settings=bsp/settings.bsp)

	(cd ../$(DST) ; make hw-build ; make omicrob ; nios2-bsp-generate-files --bsp-dir=bsp --settings=bsp/settings.bsp)

	cp bsp/bsp_onchip.tcl ../$(DST)/bsp/bsp_onchip.tcl
	cp bsp/bsp_sdram.tcl ../$(DST)/bsp/bsp_sdram.tcl

	echo "\nonchip:\n	nios2-bsp-update-settings --script=bsp/bsp_onchip.tcl --bsp-dir=bsp --settings=bsp/settings.bsp; nios2-bsp-generate-files --bsp-dir=bsp --settings=bsp/settings.bsp\n" >> ../$(DST)/Makefile

	echo "sdram:\n	nios2-bsp-update-settings --script=bsp/bsp_sdram.tcl --bsp-dir=bsp --settings=bsp/settings.bsp; nios2-bsp-generate-files --bsp-dir=bsp --settings=bsp/settings.bsp\n" >> ../$(DST)/Makefile


clean:
	#rm -Rf apps c ml rtl qsys
	rm -f bsp/bsp_update.tcl
	rm -f  rtl/*$(DOT_VHDL) c/*.c  c/*.h  ml/*.ml  ml/*.mli qsys/*_hw.tcl qsys/*_ext.tcl

check:
	ghdl -a -fno-color-diagnostics rtl/misc/*$(DOT_VHDL) rtl/*$(DOT_VHDL);
	rm -f *.o *.cf
