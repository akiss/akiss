.PHONY: src/akiss

all: src/akiss

src/akiss:
	$(MAKE) -C src

clean::
	$(MAKE) -C src clean

# STATS

STATS_TESTS = \
  $(wildcard examples/everlasting-ind/*.api) \
  $(wildcard examples/foo/*.api) \
  $(wildcard examples/guessing/*.api) \
  $(wildcard examples/needham-schroeder/*.api) \
  $(wildcard examples/okamoto/*.api) \
  $(wildcard examples/running-example/*.api) \
  $(wildcard examples/strong-secrecy/*.api) \
  $(wildcard examples/privchannels/*.api) \

STATS_STATS = $(STATS_TESTS:.api=.stats)

stats: $(STATS_STATS)

clean::
	rm -f $(STATS_STATS)

%.stats: %.api src/akiss
	/usr/bin/time sh -c "src/akiss $(AKISS_OPTIONS) < $< > /dev/null 2>&1" > $@ 2>&1
