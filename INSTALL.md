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

7. Get the built lean4 files now in the `local` directory within the `reopt-vcg` repo directory structure into your PATH, e.g. `sudo rsync -a ./local/ /usr/local/` (N.B., that copies and I believes overwrites conflicting files, which may not be what you want)

8. (Optional) Install lean4-mode for emacs by adding something like the following to your config file:

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


## Building `reopt-vcg`

Assuming you're in the `reopt-vcg` repo top level directory:

1. `cd lean4/`
2. `LEAN_CXX=clang-8 make LEAN=$PWD/../local/bin/lean LEANC=$PWD/../local/bin/leanc LLVM_CONFIG=llvm-config-8 CXX=clang-8`
