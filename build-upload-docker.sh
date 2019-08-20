#!/bin/bash
sudo docker build -t jojoz/stack-build-llvm:latest .
sudo docker login
sudo docker push jojoz/stack-build-llvm:latest
