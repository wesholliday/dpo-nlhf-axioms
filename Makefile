.PHONY: figures verify check-supplement check-lean check-lean-docker check-lean-host

PYTHON ?= python3

LEAN_DOCKER_IMAGE ?= ptpv-lean-check:4.30.0
LEAN_DOCKER_MEMORY ?= 12g
LEAN_DOCKER_CPUS ?= 4

check-supplement:
	scripts/check_supplement.sh

figures:
	$(PYTHON) -m scripts.figures.rebuild_camera_ready --output-dir output/figures

verify:
	$(PYTHON) scripts/verify_camera_ready.py

check-lean: check-lean-docker

check-lean-docker:
	docker build --memory=12g -f formalization/docker/lean-check.Dockerfile -t $(LEAN_DOCKER_IMAGE) formalization/docker
	docker run --rm --memory=$(LEAN_DOCKER_MEMORY) --cpus=$(LEAN_DOCKER_CPUS) -v "$(PWD):/work" -w /work/formalization $(LEAN_DOCKER_IMAGE) lake exe cache get
	docker run --rm --memory=$(LEAN_DOCKER_MEMORY) --cpus=$(LEAN_DOCKER_CPUS) -v "$(PWD):/work" -w /work/formalization $(LEAN_DOCKER_IMAGE) bash -lc 'scripts/check_artifact.sh'

check-lean-host:
	@printf '%s\n' 'Disabled: run Lean only through check-lean-docker.' >&2
	@exit 2
