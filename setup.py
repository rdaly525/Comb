from setuptools import setup
import sys

setup(
    name='Comb',
    version='0.0.1',
    url='https://github.com/rdaly525/Comb',
    license='MIT',
    maintainer='Ross Daly',
    maintainer_email='rdaly525@stanford.edu',
    description='comb language and synth',
    packages=[
        "comb"
    ],
    install_requires=[
        "hwtypes",
        "ply",
        "more_itertools",
        "DagVisitor",
        #"delegator.py"
    ],
    python_requires='>=3.8'
)
