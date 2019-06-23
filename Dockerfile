# Dockerfile to use with GitLab CI

FROM fpco/stack-build:latest

RUN apt-add-repository "deb http://apt.llvm.org/xenial/ llvm-toolchain-xenial-8 main" && \
    apt update -y && \
    apt install -y llvm-8