ARG MC_TAG="1.13.0-coq-8.14"
FROM mathcomp/mathcomp:${MC_TAG}

COPY ssprove.opam ./

# hadolint ignore=SC2046
RUN set -x \
  && eval $(opam env "--switch=${COMPILER}" --set-switch) \
  && opam config list; opam repo list; opam list \
  && opam update -y \
  && opam install -y ./ssprove.opam --deps-only \
  && opam list

# Restore default shell to fully preserve backward compatibility
SHELL ["/bin/sh", "-c"]
