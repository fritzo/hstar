all: src sandbox doc badge

src: FORCE
	cd src ; ./make.sh
	$(MAKE) -C src

sandbox: FORCE
	cd sandbox ; ./make.sh
	$(MAKE) -C sandbox

doc: FORCE
	$(MAKE) -C doc

badge: FORCE
	./proof_badge.sh

clean:
	git clean -dfx

FORCE:
