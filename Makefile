all: src sandbox doc

src: FORCE
	cd src ; ./make.sh
	$(MAKE) -C src

sandbox: FORCE
	cd sandbox ; ./make.sh
	$(MAKE) -C sandbox

doc: FORCE
	$(MAKE) -C doc

clean:
	git clean -dfx

FORCE:
