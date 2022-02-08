ARG MATHCOMP_VERSION="latest"
ENV MATHCOMP_VERSION=${MATHCOMP_VERSION}

ARG COQ_VERSION="dev"
ENV COQ_VERSION=${COQ_VERSION}

FROM mathcomp/mathcomp:${MATHCOMP_VERSION}-coq-${COQ_VERSION}

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
