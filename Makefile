

all: src sandbox doc metrics
	@echo '---------------------------------'
	@echo 'PASSED WITH' \
		$(shell ./metrics.py print-hole-count src/*.v) 'HOLES'

src: FORCE
	cd src ; ./make.sh
	$(MAKE) -C src

sandbox: FORCE
	cd sandbox ; ./make.sh
	$(MAKE) -C sandbox
	pep8 sandbox/*.py
	pyflakes sandbox/*.py

doc: FORCE
	$(MAKE) -C doc

metrics: FORCE
	pyflakes metrics.py
	./metrics.py update-readme src/*.v

clean: FORCE
	git clean -dfx -e 'coq-*' -n

FORCE:
