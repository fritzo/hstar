
HOLE_COUNT:=$(shell ./metrics.py print-hole-count src/*.v)

all: src sandbox doc metrics
	@echo '---------------------------------'
	@echo 'PASSED WITH' $(HOLE_COUNT) 'HOLES'

src: FORCE
	cd src ; ./make.sh
	$(MAKE) -C src

sandbox: FORCE
	cd sandbox ; ./make.sh
	$(MAKE) -C sandbox

doc: FORCE
	$(MAKE) -C doc

metrics: FORCE
	pyflakes metrics.py
	./metrics.py update-readme src/*.v

clean: FORCE
	git clean -dfx

FORCE:
