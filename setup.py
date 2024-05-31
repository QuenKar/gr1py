#!/usr/bin/env python
from __future__ import print_function
from setuptools import setup


# Version
MAJOR = 0
MINOR = 3
MICRO = 1

gr1py_version = '{major}.{minor}.{micro}'.format(major=MAJOR, minor=MINOR, micro=MICRO)

with open('gr1py/_version.py', 'w') as f:
    f.write("""# Automatically generated by setup.py of gr1py. Do not edit.
version = '{version}'""".format(version=gr1py_version))

# Build parsing tables
try:
    import gr1py.form.gr1c
    import os.path
    assert os.path.exists('gr1py/form/parsetab.py'), 'Failed to build parsing table.'
except ImportError:
    print('!'*60)
    print('Please run again to cache the parsing table.')
    print('!'*60)

setup(name='gr1py',
      version=gr1py_version,
      author='Scott C. Livingston',
      author_email='slivingston@cds.caltech.edu',
      url='https://github.com/slivingston/gr1py',
      license='BSD',
      description='enumerative (or concrete) reactive synthesis tool for the GR(1) fragment of LTL',
      long_description=open('README.rst').read(),
      packages=['gr1py', 'gr1py.form'],
      package_data={'gr1py.form': ['parsetab.py']},
      install_requires=['ply'],
      entry_points={'console_scripts': ['gr1py = gr1py.cli:main']},
      classifiers=['Programming Language :: Python :: 2',
                   'Programming Language :: Python :: 2.7',
                   'Programming Language :: Python :: 3',
                   'Programming Language :: Python :: 3.5',
                   'Programming Language :: Python :: 3.6',
                   'Programming Language :: Python :: 3.7',
                   'Programming Language :: Python :: 3.8',
                   'Programming Language :: Python :: 3.9',
                   'Programming Language :: Python :: 3.10',
                   'Programming Language :: Python :: 3.11']
      )
