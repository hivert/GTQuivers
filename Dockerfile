FROM sagemath/sagemath:8.0-2

# Inspired from https://mybinder.readthedocs.io/en/latest/dockerfile.html#preparing-your-dockerfile
# Make sure the contents of our repo are in ${HOME}
COPY . ${HOME}

RUN git clone https://github.com/nthiery/sage-semigroups/; \
    cd sage-semigroups; \
    sage -pip install .
