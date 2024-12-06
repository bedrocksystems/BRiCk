OCaml bindings for SWI-Prolog
=============================

Currently supported versions are 9.0.0 to 9.3.8.

## Installing SWI-Prolog From Source

The following instructions will install SWI-Prolog in your `$HOME` directory,
under the `.local` prefix.
```
mkdir swipl; cd swipl
SWIPLVER=9.2.7
curl -O -L https://github.com/SWI-Prolog/swipl/archive/refs/tags/V${SWIPLVER}.tar.gz
tar -xf V${SWIPLVER}.tar.gz
mkdir swipl-${SWIPLVER}-build; cd swipl-${SWIPLVER}-build
cmake -DCMAKE_INSTALL_PREFIX=$HOME/.local -DSWIPL_PACKAGES=OFF \
  -DINSTALL_DOCUMENTATION=OFF -G Ninja -DCMAKE_BUILD_TYPE=Release \
  ../swipl-${SWIPLVER}
ninja
ninja install
```
After installation, you need to set the following environment variables (for
example, in your `.bashrc` file):
```
export PATH=$HOME/.local/bin:$PATH
export PKG_CONFIG_PATH=$HOME/.local/share/pkgconfig
export SWI_HOME_DIR=$HOME/.local/lib/swipl 
```
