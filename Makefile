.PHONY: all doc stack-build stack-install

all: doc stack-build

install: stack-install

doc:
	$(MAKE) -C doc

stack-build:
	stack build

stack-install:
	stack install
