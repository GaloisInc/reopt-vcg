# Vagrant VM and `reopt-vcg` setup

These instructions include details for setting up the Vagrant VM described by the `Vagrantfile` from the `reopt-vcg` and building/setting things up for the first time.

First, `git clone` and `cd` into the `reopt-vcg` git repo on your host machine and roughly follow the below steps as needed.

## Setting up the Vagrant VM

(These steps assume you want to use Virtualbox as the backend for Vagrant.)

1. If not present already, install Virtualbox, Vagrant (e.g., `brew cask install vagrant` or `sudo apt install vagrant`), and the `vagrant-vbguest` (e.g., `vagrant plugin install vagrant-vbguest`)

2. Run `vagrant up`; if you see an error similar to "A host only
   network interface you're attempting to configure via DHCP", either
   upgrade your vagrant/virtualbox installs (a patch for the issue
   should be in an upcoming release) or consider adding the following
   monkey patch to the top of the `Vagrantfile` code contents:

```
class VagrantPlugins::ProviderVirtualBox::Action::Network
  def dhcp_server_matches_config?(dhcp_server, config)
    true
  end
end
```                                                                                                                                                 
3. `vagrant ssh` into the machine - if all went well you should land in an empty running virtual machine!


## Building and installing `repot-vcg`'s lean4 submodule

Assuming you've just `vagrant ssh`'d into the freshly provisioned VM described by the `repot-vcg`'s `Vagrantfile`:

1. Set up SSH keys if necessary for your `git` workflow

2. `git clone git@github.com:GaloisInc/reopt-vcg.git`

3. `cd reopt-vcg`

4. `git submodule update --init`

5. `sudo apt install -y g++`

6. Build the lean4 submodule, e.g. `./scripts/build-lean4.sh lean4/deps/lean4 build/lean4 local llvm-config-8 -DCMAKE_C_COMPILER=gcc -DCMAKE_CXX_COMPILER=g++`


## Building `reopt-vcg`

Assuming you're in the `reopt-vcg` repo top level directory:

1. `cd lean4/`
2. `./local_build.sh`

## Running Examples

1. Once the local `reopt-vcg` build finishes, `cd test-programs`
2. `../build/reopt-vcg test_add_diet_reopt.ann`
3. `../build/reopt-vcg test_fib_diet_reopt.ann`

## (Optional) Setting up `lean4-mode`

1. In the `lean4/` directory, run `make env`, which will print the
   `LEAN_PATH` environment variable value used by the build. That is
   the value you'll want your `LEAN_PATH` environment variable to be
   for `lean4-mode` to be able to find the various packages
   `reopt-vcg` uses. (E.g., add an `export LEAN_PATH=...` line in to
   your `~/.bashrc` or similar with the printed content).

2. Add the following (or similar) elisp to your emacs config file to
   enable `lean4-mode` whenever a `*.lean` file is opened.

```
;; You need to modify the following line if your directory structure differs
(setq lean4-rootdir "/home/vagrant/reopt-vcg/lean4/deps/lean4")

(setq lean4-mode-required-packages '(dash dash-functional f flycheck s))

(require 'package)
(add-to-list 'package-archives '("melpa" . "http://melpa.org/packages/"))
(package-initialize)
(let ((need-to-refresh t))
  (dolist (p lean4-mode-required-packages)
    (when (not (package-installed-p p))
      (when need-to-refresh
        (package-refresh-contents)
        (setq need-to-refresh nil))
      (package-install p))))

(setq load-path (cons (concat lean4-rootdir "/lean4-mode") load-path))
(require 'lean4-mode)
```
