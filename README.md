# planalyzer [![Build Status](https://travis-ci.com/KDL-umass/PlanAlyzer-private.svg?token=nzdC4L1kLqgvpfrr9NH5&branch=master)](https://travis-ci.com/KDL-umass/PlanAlyzer)

`planalyzer` is a tool for statically checking PlanOut programs and producing ATE contrasts.

`planalyzer` must be [built](#build) from source. [Usage](#usage) is for command-line applications.

# Build

We have provided a Dockerfile to facilitate builds using [Docker](https://www.docker.com/products/docker-desktop), which you must download and install to use. Our Travis build uses Docker.

Note that there are still many elements of the build setup that could be further Dockerized!

`docker build -t planalyzer .`.

# Usage

## Tests

`docker run -t planalyzer ./build_and_test.sh`

## Analyzing scripts
Before you begin, you will need to acquire some PlanOut scripts. There are some examples in the testing code and in our paper.
 
`planalyzer path/to/script.json -report`

You can run this command after spinning up a prompt:

`docker run -i -t planalyzer /bin/bash`

## Using annotations 

You can have both local and global annotations on planout variables.
The environment variable `PLANALYZER_CONFIG` must point to the file holding
the global annoatations. Local annotations must be supplied using the 
`-config` command line argument. Local annotations referring to variables
defined in the global annotations file will alias the global properties.




