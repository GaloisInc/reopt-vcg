#! /usr/bin/env python3
import os
import string
import subprocess
import shutil

skip_opcode_prefixes = [
  'bsf', # mi(64, scanForward(...)) starts with 56 zeros
  'bsr', # mi(64, scanReverse(...)) starts with 56 zeros
  'cmpxchgb',
  'cmpxchgl',
  'lzcntl',
  'maskmovdqu', # non-terminating execution
  'mpsadbw', # non-terminating execution
  'pclmulqdq', # non-terminating execution
  'pcmpestri', # non-terminating execution
  'pcmpestrm', # non-terminating execution
  'pcmpistri', # non-terminating execution
  'pcmpistrm', # non-terminating execution
  'pdep', # non-terminating execution
  'pext', # non-terminating execution
  'rep', # non-terminating execution
  'tzcntl',
  'vmaskmovdqu', # non-terminating execution
  'vmpsadbw', # non-terminating execution
  'vpclmulqdq', # non-terminating execution
  'vpcmpestri', # non-terminating execution
  'vpcmpestrm', # non-terminating execution
  'vpcmpistri', # non-terminating execution
  'vpcmpistrm', # non-terminating execution
  'vpshuf', # parser out of memory
  'xaddb',
  'xchgb',
  'xchgw',

  # Causes the K lean translator to crash

  'vfmadd231ps',
  'vfnmadd213ps',
  'vfnmadd231pd',
  
  'vfnmadd213os',
  'vfnmadd213od',
  'vfnmadd213pd',
  
  # conditions
  'lods', # string operation
  'movs_', # string operation, the '_' is a hack
  'stos', # string operation
  'cmps', # string operation
  'scas', # string operation
  'shld', # double precision shift
  'shrd', # double precision shift
  'cmpxchgq', # convSubRegsToRegs
  'cmpxchgw', # convSubRegsToRegs
  'xaddl', # convSubRegsToRegs
  'xaddq', # convSubRegsToRegs
  'xaddw', # convSubRegsToRegs
  'xchgl', # convSubRegsToRegs
  'xchgq', # convSubRegsToRegs

  # sjw -- apparently control flow causes issues
  'popq', # this is in the systemIn
  'popq', # this is in the systemIn  
  # 'leave',
  # 'ja',
  # 'jae',
  # 'jb',
  # 'jbe',
  # 'jc',
  # 'je',
  # 'jecxz',
  # 'jg',
  # 'jge',
  # 'jl',
  # 'jle',
  # 'jmp',
  # 'jna',
  # 'jnae',
  # 'jnb',
  # 'jnbe',
  # 'jnc',
  # 'jne',
  # 'jng',
  # 'jnge',
  # 'jnl',
  # 'jnle',
  # 'jno',
  # 'jnp',
  # 'jns',
  # 'jnz',
  # 'jo',
  # 'jp',
  # 'jpe',
  # 'jpo',
  # 'jrcxz',
  # 'js',
  # 'jz',
  # 'loop',
  
]

submodules_dir_path = os.path.join(
    os.path.dirname(
      os.path.dirname(
        os.path.dirname(
          os.path.dirname(
            os.path.realpath(__file__),
          ),
        ),
      ),
    ),
  'submodules',
)

semantics_dir_path = os.path.join(
  os.path.join(
    submodules_dir_path,
    'X86-64-semantics',
  ),
  'semantics',
)

instructions_semantics_file_path = os.path.join(
  semantics_dir_path,
  'x86-instructions-semantics.k',
)

kompile_path = os.path.join(
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
  'kompile',
)

lean_dir_path = os.path.dirname(os.path.realpath(__file__))

def partition_imm(s):
  (imm_prefix, imm_sep, imm_suffix) = s.partition('_imm')
  if imm_sep:
    return (imm_prefix, int(imm_suffix[:-len('.k')]))
  return (None, None)

def generate_instructions_semantics_file(chunk_size=200, prefix=''):
  require_paths = []

  def add_semantics(instructions_dirname):
    instructions_dir_path = os.path.join(semantics_dir_path, instructions_dirname)
    for k_filename in sorted(os.listdir(instructions_dir_path)):
      if any(k_filename.startswith(opcode_prefix) for opcode_prefix in skip_opcode_prefixes):
        continue

      if 'label' in k_filename:
        continue

      if k_filename.startswith(prefix):
        k_file_path = os.path.join(instructions_dir_path, k_filename)

        if require_paths:
          (prev_imm_prefix, prev_imm_bitwidth) = partition_imm(require_paths[-1])
          (imm_prefix, imm_bitwidth) = partition_imm(k_file_path)
          if prev_imm_prefix == imm_prefix and prev_imm_bitwidth is not None and imm_bitwidth is not None:
            if prev_imm_bitwidth < imm_bitwidth:
              require_paths[-1] = k_file_path
            else:
              pass
            continue

        require_paths.append(k_file_path)

  # Most of these are problematic.
  # add_semantics('systemInstructions')
  add_semantics('registerInstructions')
  add_semantics('memoryInstructions')
  add_semantics('immediateInstructions')

  require_paths.sort(key=os.path.basename)
  def get_opcode_variant(i):
    return os.path.basename(require_paths[i]).partition('_')[0]

  index = 0
  chunk_id = 0
  while index < len(require_paths):
    next_index = index + chunk_size
    while next_index < len(require_paths) and get_opcode_variant(next_index - 1) == get_opcode_variant(next_index):
      next_index = next_index + 1

    with open(instructions_semantics_file_path, mode='w') as instructions_semantics_file:
      print(
'''require "x86-configuration.k"

module X86-INSTRUCTIONS-SEMANTICS
  import X86-CONFIGURATION
''',
        file=instructions_semantics_file
      )

      for require_path in require_paths[index:next_index]:
        print(f'select {require_path}')
        with open(require_path, 'r') as file_:
          for line in file_:
            if line.startswith('require'):
              continue
            if any(line.strip().startswith(keywork) for keywork in ['module', 'import', 'endmodule']):
              continue

            instructions_semantics_file.write(line)

      print('endmodule', file=instructions_semantics_file)

    subprocess.check_call(
      [ f'{kompile_path}',
        '-v',
        '--backend',
        'java',
        '-I',
        '.',
        '-I',
        'common/x86-config',
        '--syntax-module',
        'X86-SYNTAX',
        '--main-module',
        'X86-SEMANTICS',
        'x86-semantics.k',
      ],
      cwd=semantics_dir_path,
    )

    if prefix:
      target_kompiled_dir = f'x86-semantics-{prefix}_{chunk_id}'
    else:
      target_kompiled_dir = f'x86-semantics-{chunk_id}'
    target_kompiled_dir_path = os.path.join(
      os.path.join(lean_dir_path, target_kompiled_dir),
      'x86-semantics-kompiled',
    )
    if os.path.exists(target_kompiled_dir_path):
      shutil.rmtree(target_kompiled_dir_path)
    shutil.copytree(
      os.path.join(semantics_dir_path, 'x86-semantics-kompiled'),
      target_kompiled_dir_path,
    )

    index = next_index
    chunk_id = chunk_id + 1

generate_instructions_semantics_file()

