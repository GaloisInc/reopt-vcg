FROM ubuntu:20.04

# Install needed packages for building
ARG DEBIAN_FRONTEND=noninteractive
ENV TZ=America/Los_Angeles
RUN apt-get update \
    && apt-get install -y cmake ccache gcc g++ git \
    libgmp-dev zlib1g-dev lib32z1-dev clang-8 llvm-8
# create a `vadd` user and home directory
RUN useradd -m vadd && chown -R vadd:vadd /home/vadd
# copy over reopt-vcg content
COPY . /home/vadd/reopt-vcg
WORKDIR /home/vadd/reopt-vcg


# Clone the git submodules (first replacing `git@` with `https://` for simplicity)
RUN sed -r -i 's:git@([^/]+)\:(.*\.git):https\://\1/\2:g' .gitmodules
RUN git submodule update --init --depth 50
# Build and install lean4 from submodule
RUN .github/ci.sh lean4-build
# Build reopt-vcg
RUN .github/ci.sh build

