all: src sandbox doc metrics

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
	./metrics.py

clean:
	git clean -dfx

FORCE:
