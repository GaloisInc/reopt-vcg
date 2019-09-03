#! /usr/bin/env python3
import os
import string
import subprocess

submodules_dir_path = os.path.join(
  os.path.dirname(
    os.path.dirname(
      os.path.dirname(
        os.path.dirname(
          os.path.dirname(
            os.path.realpath(__file__),
          ),
        ),
      ),
    ),
  ),
  'submodules',
)

kprove_path = os.path.join(
  os.path.join(
    os.path.join(
      os.path.join(
        submodules_dir_path,
        'k',
      ),
      'k-distribution',
    ),
    'bin',
  ),
  'kprove',
)

lean_dir_path = os.path.dirname(os.path.realpath(__file__))

def generate_lean(suffix):
  kompiled_semantics_dir_path = os.path.join(
    lean_dir_path,
    f'x86-semantics-{suffix}',
  )

  subprocess.check_call(
    [ f'{kprove_path}',
      '-v',
      '--smt',
      'none',
      '-d',
      kompiled_semantics_dir_path,
      'instruction-template-spec.k',
    ],
    cwd=lean_dir_path,
  )

def generate_lean_all(start=0, stop=14):
  for suffix in range(start, stop):
    generate_lean(suffix)

generate_lean_all()

