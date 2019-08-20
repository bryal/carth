#!/bin/bash
sudo docker build -t jojoz/stack-build-llvm:lts-14.1 .
sudo docker login
sudo docker push jojoz/stack-build-llvm:lts-14.1
