#!/usr/bin/env bash

#------------------------------------------------------------------------------
# Skip to the end for main flow of script
#------------------------------------------------------------------------------

# See the Readme.md file for details on how it works and for the user guide.

#------------------------------------------------------------------------------
# TODO
#------------------------------------------------------------------------------

# FORCE_TOOL_INSTALL: an option to not use cached installs, force fresh
# installs of tools What if we are using a tool from system path -
# invert path?
# NO_TOOL_INSTALL: do not download/install any tools
# cabal build can use stack installed ghc if GHCVER is not specified

#------------------------------------------------------------------------------
# Utility functions
#------------------------------------------------------------------------------

PACKCHECK_VERSION=0.4.1

show_version() {
  echo "packcheck version $PACKCHECK_VERSION"
}

# $1: varname
show_var() {
  echo "$1=$(eval \"echo \$$1\")"
}

# $1: varname
show_nonempty_var() {
  local var=$(eval "echo \$$1")
  if test -n "$var"
  then
    printf "%q\n" "$1=$var"
  fi
}

# $1: var name
# $2: default value
init_default() {
  local var=$(eval "echo \$$1")
  test -n "$var" || eval "export $1=\"$2\""
}

require_file () {
  if test ! -f "$1"
  then
    echo "Required file [$1] does not exist."
    exit 1
  fi
}

# $1: message
die () {
  >&2 echo -e "Error: $1"
  exit 1
}

retry_cmd() {
  cmd=$*
  $cmd || (sleep 2 && $cmd) || (sleep 10 && $cmd)
}

# MINGW 'which' does not seem to work when there are spaces in the
# PATH.  Note that "type" returns a cached path, so if something got
# deleted we might still be returning a stale value (we can use hash -r
# to clear the cache if needed).

which_cmd() {
  hash -r && type -P "$1" || true
}

require_cmd () {
  if test -z "$(which_cmd $1)"
  then
    echo "Required command [$1] not found in PATH [$PATH]."
    exit 1
  else
    echo "Using [$1] at [$(which_cmd $1)]"
  fi
}

# $1: command
function run_verbose() {
  echo "$*"
  bash -c "$*"
}

function run_verbose_errexit() {
  run_verbose "$*" || die "Command [$*] failed. Exiting."
}

# $1: msg
show_step1() {
  echo
  echo "--------------------------------------------------"
  echo "$1"
  echo "--------------------------------------------------"
}

# $1: msg
show_step() {
  local reltime
  local disptime
  reltime=$(get_rel_time)
  if test -n "$reltime"
  then
    disptime="[$reltime sec]"
  fi
  show_step1 "$disptime $1"
}

# $1: file to ungztar
win_ungztar() {
  local output=$(basename ${1%.gz})
  run_verbose_errexit 7z e -y $1 && run_verbose_errexit 7z x -y $output
  run_verbose_errexit rm -f $output
}

set_os_specific_vars() {
  local os=$(uname)
  case "$os" in
    Darwin|Linux)
      OS_HAS_TOOLS=tar
      OS_UNGZTAR_CMD="run_verbose_errexit tar xzvf"
      OS_LOCAL_DIR=.local
      OS_CABAL_DIR=.cabal
      OS_APP_HOME=$HOME ;;
    MINGW*)
      require_cmd cygpath
      require_envvar APPDATA
      OS_HAS_TOOLS=cygpath
      OS_UNGZTAR_CMD=win_ungztar
      OS_LOCAL_DIR=local
      OS_CABAL_DIR=cabal
      OS_APP_HOME=`cygpath $APPDATA` ;;
    *) die "Unknown OS [$os]" ;;
  esac
}

show_machine_info() {
  local os=$(uname)
  case "$os" in
    Linux)
      echo "OS: Linux"
      lscpu | grep "^Archi\|^CPU\|^Bogo\|^Hyper\|^Virtualiz"

      echo "Memory:"
      run_verbose free -h || true

      show_step "Container/cgroup information"
      # See https://stackoverflow.com/questions/20010199/determining-if-a-process-runs-inside-lxc-docker
      # For comprehensive detection see container-detect.conf in ubuntu
      #if test -f /.dockerenv
      #then
      #  echo "Running inside Docker (found /.dockerenv)";
      #fi
      #run_verbose head -n 1 /proc/1/cgroup
      sudo cat /proc/1/environ | tr '\0' '\n' | grep "^container=" || true
      run_verbose cat /sys/fs/cgroup/cpu/cpu.cfs_period_us || true
      run_verbose cat /sys/fs/cgroup/cpu/cpu.cfs_quota_us || true
      run_verbose cat /sys/fs/cgroup/memory/memory.limit_in_bytes || true ;;
    Darwin)
      echo "OS: MacOS" ;;
    MINGW*)
      echo "OS: Windows (MINGW)" ;;
    *) die "OS: Unknown OS [$os]" ;;
  esac
}

#------------------------------------------------------------------------------
# Build config show and determine
#------------------------------------------------------------------------------

SAFE_ENVVARS="\
  RESOLVER \
  ENABLE_GHCJS \
  GHCVER \
  CABALVER \
  GHC_OPTIONS \
  SDIST_OPTIONS \
  DISABLE_SDIST_BUILD \
  DISABLE_BENCH \
  DISABLE_TEST \
  DISABLE_DOCS \
  DISABLE_DIST_CHECKS \
  PATH \
  TOOLS_DIR \
  STACKVER \
  STACK_YAML \
  STACK_OPTIONS \
  STACK_BUILD_OPTIONS \
  CABAL_CHECK_RELAX \
  CABAL_USE_STACK_SDIST \
  CABAL_CONFIGURE_OPTIONS \
  CABAL_NEWBUILD_OPTIONS \
  CABAL_NEWBUILD_TARGETS \
  COVERAGE \
  COVERALLS_OPTIONS \
  HLINT_COMMANDS \
  CHECK_ENV \
  LANG \
  LC_ALL \
  BASE_TIME \
"

UNSAFE_ENVVARS="\
  ENABLE_INSTALL \
  STACK_UPGRADE \
  CABAL_REINIT_CONFIG \
  CABAL_NO_SANDBOX \
  CABAL_HACKAGE_MIRROR \
"

ENVVARS="$SAFE_ENVVARS $UNSAFE_ENVVARS"

# $1: varname
# $2: list of vars to find in
find_var() {
  for v in $2
  do
   test $v != "$1" || return 0
  done
  return 1
}

error_novar() {
  find_var "$1" "$ENVVARS" || die "Unknown parameter or environment variable [$1]"
}

error_clean_env() {
    echo "Error: Unknown parameter or environment variable [$1]."
    die "Please check spelling mistakes and use a clean environment (e.g. env -i) with CHECK_ENV."
}

ALLOW_ENVVARS="STACK_ROOT APPDATA PWD SHLVL _"

check_clean_env() {
  local vars=$(env | cut -f1 -d=)
  for i in $vars
  do
    find_var $i "$ENVVARS $ALLOW_ENVVARS" || error_clean_env "$i"
  done
}

# $1: varname
require_envvar() {
  local var=$(eval "echo \$$1")
  test -n "$var" || die "Parameter or environment variable [$1] must be set. Try --help for usage."
}

# $1: envvar
check_boolean_var() {
  error_novar "$1"
  local var=$(eval "echo \$$1")
  if test -n "$var" -a "$var" != y
  then
    die "Boolean parameter or environment variable [$1] can only be empty or 'y'"
  fi
}

# $1: cmdname
# $2: help text
help_cmd() {
  printf "%-24s: %s\n" "$1" "$2"
}

# $1: varname
# $2: help text
help_envvar() {
  error_novar $1
  printf "%-24s: %s\n" "$1" "$2"
}

short_help() {
  echo "$0 COMMAND [PARAMETER=VALUE ...]"
  echo
  echo "For example:"
  echo "$0 stack RESOLVER=lts GHC_OPTIONS=\"-O0 -Werror\""
  echo "$0 cabal-new GHC_OPTIONS=\"-O0 -Werror\""
  echo
  echo "Control parameters can either be passed on command line or exported"
  echo "as environment variables. Parameters marked DESTRUCTIVE may modify"
  echo "your global user config or state."
}

show_help() {
  show_step1 "Usage"
  short_help

  show_step1 "Commands and flags"
  help_cmd cabal-new "build using cabal new-build (GHCVER >= 8.2.2)"
  help_cmd cabal "build using cabal"
  help_cmd stack "build using stack"
  # TODO add hlint as a tool
  help_cmd clean "remove the .packcheck directory"
  help_cmd cleanall "remove .packcheck, .stack-work, .cabal-sandbox directories"
  help_cmd "help | --help | -h" "show this help message"
  help_cmd "--version" "show packcheck version"

  show_step1 "Selecting tool versions"
  help_envvar ENABLE_GHCJS "[y] Use GHCJS instead of GHC to build"
  help_envvar GHCVER "[a.b.c] GHC version prefix (may not be enforced when using stack)"
  help_envvar CABALVER "[a.b.c.d] Cabal version (prefix) to use"
  help_envvar RESOLVER "Stack resolver to use for stack builds or cabal builds using stack"
  help_envvar STACKVER "[a.b.c.d] Stack version (prefix) to use"
  help_envvar STACK_UPGRADE "[y] DESTRUCTIVE! Upgrades stack to latest version"

  show_step1 "Where to find the required tools"
  help_envvar PATH "[path] Set PATH explicitly for predictable builds"
  help_envvar TOOLS_DIR "[dir] Find ghc|cabal by version as in TOOLS_DIR/ghc/<version>/bin"

  show_step1 "Specifying common tool options"
  # TODO
  # help_envvar TOOL_OPTIONS "Specify the tool specific (stack or cabal) options to use."
  # help_envvar BUILD_OPTIONS "Specify the tool specific build (stack build or cabal new-build) options to use."
  help_envvar GHC_OPTIONS "Specify GHC options to use"
  help_envvar SDIST_OPTIONS "Arguments to stack/cabal sdist command"
  # XXX this applies to both stack and cabal builds
  help_envvar CABAL_REINIT_CONFIG "[y] DESTRUCTIVE! Remove old config to avoid incompatibility issues"

  show_step1 "Specifying what to build"
  help_envvar DISABLE_BENCH "[y] Do not build benchmarks, default is to build but not run"
  help_envvar DISABLE_TEST "[y] Do not run tests, default is to run tests"
  help_envvar DISABLE_DOCS "[y] Do not build haddocks, default is to build docs"
  help_envvar DISABLE_SDIST_BUILD "[y] Do not build from source distribution"
  help_envvar DISABLE_DIST_CHECKS "[y] Do not perform source distribution checks"
  help_envvar ENABLE_INSTALL "[y] DESTRUCTIVE! Install the package after building"

  show_step1 "stack options"
  help_envvar STACK_YAML "Alternative stack config, cannot be a path, just the file name"
  help_envvar STACK_OPTIONS "ADDITIONAL stack global options (e.g. -v) to append"
  help_envvar STACK_BUILD_OPTIONS "ADDITIONAL stack build command options to append"

  show_step1 "cabal options"
  #help_envvar CABAL_USE_STACK_SDIST "[y] Use stack sdist (to use --pvp-bounds)"
  help_envvar CABAL_NEWBUILD_OPTIONS "ADDITIONAL cabal new-build options to append"
  help_envvar CABAL_NEWBUILD_TARGETS "cabal new-build targets, default is 'all'"
  help_envvar CABAL_CONFIGURE_OPTIONS "ADDITIONAL cabal old style configure options to append"
  help_envvar CABAL_CHECK_RELAX "[y] Do not fail if cabal check fails on the package."
  # The sandbox mode is a bit expensive because a sandbox is used and
  # dependencies have to be installed twice in two separate sandboxes, once to
  # create an sdist and once to build the sdist. For a CI NO sandbox mode
  # makes more sense as long as multiple builds running simultaneously will not
  # try to install conflicting packages.
  help_envvar CABAL_NO_SANDBOX "[y] DESTRUCTIVE! Clobber (force install) global cabal ghc package db"
  help_envvar CABAL_HACKAGE_MIRROR "[y] DESTRUCTIVE! Specify an alternative mirror, modifies the cabal config file."

  show_step1 "Coverage options"
  help_envvar COVERALLS_OPTIONS "hpc-coveralls args and options, usually just test suite names"
  help_envvar COVERAGE "[y] Just generate coverage information"

  show_step1 "hlint options"
  help_envvar HLINT_COMMANDS "hlint commands e.g.'hlint lint src; hlint lint test'"

  show_step1 "Diagnostics options"
  # To catch spelling mistakes in envvar names passed, otherwise they will be
  # silently ignored and we will be wondering why the script is not working.
  help_envvar CHECK_ENV "[y] Treat unknown env variables as error, used with env -i"
  help_envvar BASE_TIME "System time to be used as base for timeline reporting"
}

check_all_boolean_vars () {
  check_boolean_var STACK_UPGRADE
  check_boolean_var DISABLE_SDIST_BUILD
  check_boolean_var DISABLE_DIST_CHECKS
  check_boolean_var CABAL_USE_STACK_SDIST
  # check_boolean_var CABAL_REINIT_CONFIG
  # check_boolean_var CABAL_CHECK_RELAX
  # check_boolean_var CABAL_NO_SANDBOX
  if test -n "$TEST_INSTALL"
  then
    echo "WARNING! TEST_INSTALL is deprecated. Please use ENABLE_INSTALL instead"
    ENABLE_INSTALL="$TEST_INSTALL"
    unset TEST_INSTALL
  fi
  # check_boolean_var ENABLE_GHCJS
  # check_boolean_var ENABLE_INSTALL
  # check_boolean_var DISABLE_BENCH
  # check_boolean_var DISABLE_TEST
  # check_boolean_var DISABLE_DOCS
  # check_boolean_var COVERAGE
}

show_build_command() {
  check_all_boolean_vars

  echo "You can use the following command to reproduce this build:"
  echo
  echo -n "$0 $BUILD "
  for i in $SAFE_ENVVARS
  do
    local val="$(show_nonempty_var $i)"
    test -z "$val" || echo -n "$val "
  done
  echo

  local unsafe
  for i in $UNSAFE_ENVVARS
  do
    if test -n "$(show_nonempty_var $i)"
    then
      unsafe=y
    fi
  done

  if test -n "$unsafe"
  then
    echo
    echo "The above command has omitted the following unsafe options."
    echo "If you know what you are doing, you can also add these to the"
    echo "above command to reproduce this build more faithfully."
    echo
    echo "Unsafe options may modify your config and "
    echo "are usually meant to be used in a CI setup:"
    for i in $UNSAFE_ENVVARS
    do
      show_nonempty_var $i
    done
    echo
  fi
}

show_build_config() {
  check_all_boolean_vars
  for i in $ENVVARS
  do
    show_nonempty_var $i
  done
}

show_build_env() {
  show_nonempty_var HOME
  show_nonempty_var APPDATA
  show_nonempty_var STACK_ROOT
}

need_stack() {
  if test "$BUILD" = stack -o -n "$RESOLVER" -o -n "$CABAL_USE_STACK_SDIST"
  then
    echo true
  fi
}

# $1: be verbose about why we need cabal
dont_need_cabal() {
  if test "$BUILD" = cabal -o "$BUILD" = "cabal-new"
  then
    test -z "$1" || echo "Need cabal-install because 'BUILD=$BUILD'"
    return 1
  fi

  if test -z "$DISABLE_SDIST_BUILD"
  then
    test -z "$1" || echo "Need cabal-install because 'DISABLE_SDIST_BUILD=$DISABLE_SDIST_BUILD'"
    return 1
  fi

  if test -n "$ENABLE_INSTALL"
  then
    test -z "$1" || echo "Need cabal-install because 'ENABLE_INSTALL=$ENABLE_INSTALL'"
    return 1
  fi

  return 0
}

# $1: varname
cabal_only_var() {
  error_novar $1
  local var=$(eval "echo \$$1")
  test -z "$var" || die "[$1] is meaningful only for cabal build"
}

# $1: varname
stack_only_var() {
  error_novar $1
  local var=$(eval "echo \$$1")
  test -z "$var" || die "[$1] is meaningful only when stack is used"
}

verify_build_config() {
  test -z "$COVERALLS_OPTIONS" || COVERAGE=y
  if test -n "$ENABLE_GHCJS"
  then
    test "$BUILD" = "cabal-new" || die "ENABLE_GHCJS works only with build type 'cabal-new'"
    COMPILER=ghcjs
    GHCJS_FLAG=--ghcjs
  else
    COMPILER=ghc
  fi

  if test "$BUILD" = stack
  then
    STACK_DEP_OPTIONS="--only-dependencies"
    test -n "$DISABLE_TEST" || STACK_DEP_OPTIONS="$STACK_DEP_OPTIONS --test"
    test -n "$DISABLE_BENCH" || STACK_DEP_OPTIONS="$STACK_DEP_OPTIONS --bench"

    STACK_BUILD_OPTIONS_ORIG=$STACK_BUILD_OPTIONS
    STACK_BUILD_OPTIONS=$(cat << EOF
      $(test -n "$DISABLE_DOCS" || echo "--haddock --no-haddock-deps")
      $(test -n "$DISABLE_TEST" || echo "--test")
      $(test -n "$DISABLE_BENCH" || echo "--bench --no-run-benchmarks")
      $(test -z "${COVERAGE}" || echo --coverage)
      $(test -z "${GHC_OPTIONS}" || echo --ghc-options=\"$GHC_OPTIONS\")
      $STACK_BUILD_OPTIONS
EOF
)
  elif test "$BUILD" = cabal
  then
    CABAL_DEP_OPTIONS="--only-dependencies --reorder-goals --max-backjumps=-1"
    test -n "$DISABLE_TEST" || \
      CABAL_DEP_OPTIONS="$CABAL_DEP_OPTIONS --enable-tests"
    test -n "$DISABLE_BENCH" || \
      CABAL_DEP_OPTIONS="$CABAL_DEP_OPTIONS --enable-benchmarks"

    CABAL_CONFIGURE_OPTIONS=$(cat << EOF
      $(test -n "$DISABLE_TEST" || echo "--enable-tests")
      $(test -n "$DISABLE_BENCH" || echo "--enable-benchmarks")
      $(test -z "$COVERAGE" || echo --enable-coverage)
      $(test -z "$GHC_OPTIONS" || echo --ghc-options=\"$GHC_OPTIONS\")
      $CABAL_CONFIGURE_OPTIONS
EOF
)
  else
    #CABAL_DEP_OPTIONS="--only-dependencies"
    #test -n "$DISABLE_TEST" || \
    #  CABAL_DEP_OPTIONS="$CABAL_DEP_OPTIONS --enable-tests"
    #test -n "$DISABLE_BENCH" || \
    #  CABAL_DEP_OPTIONS="$CABAL_DEP_OPTIONS --enable-benchmarks"
    #CABAL_DEP_OPTIONS="$CABAL_DEP_OPTIONS $CABAL_NEWBUILD_OPTIONS"

    test -n "$CABAL_NEWBUILD_TARGETS" || CABAL_NEWBUILD_TARGETS=all
    CABAL_NEWBUILD_OPTIONS=$(cat << EOF
      $(test -n "$DISABLE_TEST" || echo "--enable-tests")
      $(test -n "$DISABLE_BENCH" || echo "--enable-benchmarks")
      $(test -z "${COVERAGE}" || echo --enable-coverage)
      $(test -z "${GHC_OPTIONS}" || echo --ghc-options=\"$GHC_OPTIONS\")
      $CABAL_NEWBUILD_OPTIONS
EOF
)
  fi

  # These variables are now combined with other options so clear them
  # so that we do not show them in the effective config
  COVERAGE=
  GHC_OPTIONS=

  test "$BUILD" = stack -o "$BUILD" = cabal -o "$BUILD" = "cabal-new" || \
    die "build [$BUILD] can only be 'stack','cabal' or 'cabal-new'"

  if test -n "$CHECK_ENV"
  then
    if test "$BUILD" != cabal -a "$BUILD" != "cabal-new"
    then
      cabal_only_var CABALVER
      cabal_only_var CABAL_USE_STACK_SDIST
      cabal_only_var CABAL_CHECK_RELAX
      cabal_only_var CABAL_CONFIGURE_OPTIONS
      cabal_only_var CABAL_NEWBUILD_OPTIONS
      cabal_only_var CABAL_NEWBUILD_TARGETS
      cabal_only_var CABAL_NO_SANDBOX
      cabal_only_var CABAL_HACKAGE_MIRROR
    fi

    if test -z "$(need_stack)"
    then
      stack_only_var STACK_YAML
      stack_only_var STACK_UPGRADE
      stack_only_var STACK_OPTIONS
      stack_only_var STACK_BUILD_OPTIONS
    fi
  fi
}

#------------------------------------------------------------------------------
# Stack fetch and install etc.
#------------------------------------------------------------------------------

ensure_msys_tools() {
  if [[ `uname` = MINGW* ]]
  then
    # retry??
    for i in "$1"
    do
      if test -z "$(which_cmd $i)"
      then
        stack exec pacman -- -S --noconfirm $i
      fi
    done
  fi
}

fetch_stack_osx() {
  curl -sSkL https://www.stackage.org/stack/osx-x86_64 \
    | tar xz --strip-components=1 -C $1 --include '*/stack'
}

fetch_stack_linux() {
  curl -sSkL https://www.stackage.org/stack/linux-x86_64 \
    | tar xz --strip-components=1 -C $1 --wildcards '*/stack'
}

fetch_stack_windows() {
  curl -sSkL http://www.stackage.org/stack/windows-i386 \
    | 7z x -si stack.exe
}

# $1: directory to place stack executable in
fetch_stack() {
  mkdir -p $1
  local os=$(uname)
  case "$os" in
    Darwin) retry_cmd fetch_stack_osx $1 ;;
    Linux)  retry_cmd fetch_stack_linux $1 ;;
    MINGW*) retry_cmd fetch_stack_windows $1 ;;
    *) die "Unknown OS [$os]" ;;
  esac
}

# $1: directory to place stack executable in
ensure_stack() {
  if test -z "$(which_cmd stack)"
  then
    echo "Downloading stack to [$1]..."
    fetch_stack $1
  fi
  require_cmd stack

  if test -n "$STACK_UPGRADE"
  then
    echo "Upgrading stack to the required version"
    if test -n "$STACKVER"
    then
      local curver=$(stack --numeric-version)
      if test "${curver#$STACKVER}" = ${curver}
      then
        run_verbose stack --no-terminal upgrade --binary-only --binary-version $STACKVER
      fi
    else
      run_verbose stack --no-terminal upgrade --binary-only || fetch_stack $1
    fi
  fi

  test -z "$STACKVER" || check_version_die stack $STACKVER
  # Set the real version of stack
  STACKVER=$(stack --numeric-version) || exit 1

  STACKCMD="stack --no-terminal $STACK_OPTIONS"
  STACKCMD_TOOL_INSTALL="$STACKCMD"
  $STACKCMD --version

  if test -n "$RESOLVER"
  then
    STACKCMD="$STACKCMD --resolver $RESOLVER"
  fi
}

use_stack_paths() {
  # Need the bin path (not just compiler-path) on mingw to find gcc
  # some packages may have a configure script looking for gcc, so we need to
  # use bin path so that on windows we will find the stack installed mingw gcc
  run_verbose_errexit $STACKCMD path --bin-path
  local BINPATH=`$STACKCMD path --bin-path`
  if [[ `uname` = MINGW* ]]
  then
    # Need for 7z on windows
    local GHCPATHS=`$STACKCMD path --programs`
    # Convert the path to MINGW format from windows native format
    BINPATH=$(cygpath -u -p $BINPATH)
    GHCPATHS=$(cygpath -u -p $GHCPATHS)
    if test -n "$GHCPATHS"
    then
      export PATH=$GHCPATHS:$PATH
    fi
  fi
  if test -n "$BINPATH"
  then
    export PATH=$BINPATH:$PATH
  fi
}

#------------------------------------------------------------------------------
# Ensure ghc, cabal are available and the right versions when requested
#------------------------------------------------------------------------------

# $1: tool name (used only for ghc, cabal and stack)
# $2: expected version
check_version() {
  local real_ver=$($1 --numeric-version)

  # Match that the expected version is a prefix of real
  # Do not check when the expected version is head
  if test "${real_ver#$2}" != ${real_ver} -o $2 = head
  then
    return 0
  else
    echo "Found $1 version [$real_ver] expecting [$2]"
    return 1
  fi
}

# $1: tool name (used only for ghc, cabal and stack)
# $2: expected version
check_version_die() {
  check_version $1 $2 || \
    die "Wrong $1 version [$($1 --numeric-version)] expected [$2]"
}

# Remove a path from the PATH envvar
# $1: path component to remove
function path_remove {
  # Delete path by parts so we can never accidentally remove sub paths
  PATH=${PATH//":$1:"/":"} # delete any instances in the middle
  PATH=${PATH/#"$1:"/} # delete any instance at the beginning
  PATH=${PATH/%":$1"/} # delete any instance at the end
}

# Find ghc/cabal having the given version prefix in PATH or in a version
# suffixed directory at TOOLS_DIR, and check if it matches the requested
# version. If we found the requested binary we make sure that it is in the
# PATH.
#
# $1: binary name (e.g. ghc or cabal)
# $2: binary version prefix (e.g. 8 or 8.0 or 8.0.1)
find_binary () {
  local binary
  local path=$PATH
  local removed_path

  binary=$(which_cmd $1)
  while test -n "$binary"
  do
    if test -z "$2" || check_version $binary $2
    then
      PATH=$PATH$removed_path
      return 0
    else
      # remove it from the path and search again
      echo "Mismatching $1 version found at [$(dirname $binary)], removing it from PATH and trying again"
      removed_path=$removed_path:$(dirname $binary)
      path_remove $(dirname $binary)
      binary="$(which_cmd $1)"
    fi
  done

  # If we did not find the binary, restore the PATH for better error reporting
  PATH=$path

  test -n "$TOOLS_DIR" || return 0

  # Find if we have a binary in TOOLS_DIR
  local dir
  if test -n "$2"
  then
    dir=$(echo ${TOOLS_DIR}/$1/$2*/ | tr ' ' '\n' | sort | tail -1)
  else
    dir=$(echo ${TOOLS_DIR}/$1/[0-9]*/ | tr ' ' '\n' | sort | tail -1)
    test -x "${dir}/bin/$1" || dir="${TOOLS_DIR}/$1/head"
  fi

  if test -x "${dir}/bin/$1"
  then
    if test -z "$2" || check_version "${dir}/bin/$1" $2
    then
      if [[ $dir != /* ]]
      then
        dir=`pwd`/$dir
      fi
      PATH=$dir/bin:$PATH
      export PATH
      return 0
    fi
  fi
  # This command never fails even if we could not find the binary.
  return 0
}

ensure_ghc() {
  local found
  local compiler
  # If there is a ghc in PATH then use that otherwise install it using stack
  find_binary "$COMPILER" "$GHCVER"
  found="$(which_cmd $COMPILER)"
  if test -n "$(need_stack)" -a -z "$found"
  then
    # Use stack supplied ghc
    echo "$STACKCMD setup"
    retry_cmd $STACKCMD setup || die "stack setup falied"
    use_stack_paths
    echo
  fi

  compiler="$(which_cmd $COMPILER)"
  if test -z "$compiler"
  then
    local msg="$COMPILER $GHCVER not found in PATH [$PATH]"
    if test -n "$TOOLS_DIR"
    then
      msg="$msg or in $TOOLS_DIR/$COMPILER/$GHCVER*/bin"
    fi
    die msg
  fi

  if test -n "$GHCVER"
  then
    check_version_die $COMPILER $GHCVER
    # If the user specified GHCVER then use it as system-ghc
    # Stack will still silently choose its own ghc if the ghc does not match
    # the snapshot.
    STACKCMD="$STACKCMD --system-ghc"
  fi

  if test -n "$(need_stack)"
  then
    compiler=$($STACKCMD path --compiler-exe)
  fi

  echo "Using $COMPILER at $compiler"
  echo "$($compiler --version) [$($compiler --print-project-git-commit-id 2> /dev/null || echo '?')]"
  # Use the real version, the user might have specified a version prefix in
  # GHCVER
  GHCVER=$($compiler --numeric-version) || exit 1

  if test -n "$ENABLE_GHCJS"
  then
    local tmpdir
    local shebang
    local nodepath
    local output

    # XXX the temp file may not get removed on crash/interrupt
    tmpdir=`mktemp -d 2>/dev/null || mktemp -d -t 'packcheck'`
    echo "main=putStrLn \"hello\"" > $tmpdir/test.hs
    $compiler -build-runner -o ${tmpdir}/run $tmpdir/test.hs
    shebang=$(head -1 ${tmpdir}/run)
    nodepath=${shebang:2}
    echo "$compiler uses node at [${nodepath}] for executing js output"
    if test -x $nodepath
    then
      echo "$nodepath is version [$($nodepath --version)]" || die "Cannot determine node version"
    else
      rm -rf $tmpdir
      die "[$nodepath] not found or not executable"
    fi
    echo "Trying to run a test executable produced by [$compiler]..."
    output=$(${tmpdir}/run)
    rm -rf $tmpdir

    if test "$output" != "hello"
    then
      die "[$compiler] cannot produce executables runnable by [$nodepath]"
    else
      echo "[$compiler] produces executables runnable by [$nodepath]"
    fi
  fi
}

# XXX/TODO this may not work for cabal 1.24 config
# $1: mirror URL
cabal_use_mirror() {
  local CABAL_CONFIG=${OS_APP_HOME}/${OS_CABAL_DIR}/config
  if test -f $CABAL_CONFIG
  then
    local inplace
    if [ `uname` = "Darwin" ]
    then
      inplace="-i orig"
    else
      inplace="--in-place"
    fi
    echo "Adding hackage mirror [$1] to [$CABAL_CONFIG]"
    sed $inplace -e "s%^remote-repo:.*%remote-repo: $1%" $CABAL_CONFIG
  else
    die "cabal config file [$CABAL_CONFIG] not found."
  fi
}

# We need to ignore the project's stack.yaml when installing
# cabal-install, otherwise it may fail due to dependency conflicts.
#
# On CI machines if our repo is cloned in the top dir then there is no way to
# teach stack to ignore the project's stack.yaml. We cannot change our
# directory to go above it. Because we have a project stack.yaml, stack does
# not even create a global stack.yaml. So we work it around by creating a new
# package and installing cabal via that.
#
# $1 tool name
stack_install_tool () {
    rm -rf .packcheck/tool-install
    mkdir -p .packcheck/tool-install || exit 1
    cd .packcheck/tool-install || exit 1

    local res
    # Where possible we want to use the same resolver for build as well as
    # tools to share the snapshot when building.
    # But nightlies may not have cabal-install all the time
    if [[ "$RESOLVER" != "" && "$RESOLVER" != nightly* ]]
    then
      res="--resolver $RESOLVER"
    fi

    if test ! -e stack.yaml
    then
      run_verbose_errexit $STACKCMD_TOOL_INSTALL $res \
        new --bare tool-install
    fi
    run_verbose_errexit $STACKCMD_TOOL_INSTALL $res install $1
    cd ../..
}

# $1: Directory to install cabal in
# We are not using the param as currently it is always the dir where stack
# installs binaries.
ensure_cabal() {
  # We can only do this after ghc is installed.
  # We need cabal to retrieve the package version as well as for the solver
  # We are assuming CI cache will be per resolver so we can cache the bin

  find_binary cabal "$CABALVER"
  if test -z "$(which_cmd cabal)" -a -n "$(need_stack)"
  then
    stack_install_tool cabal-install
  fi

  require_cmd cabal
  cabal --version
  test -z "$CABALVER" || check_version_die cabal $CABALVER
  # Set the real version of cabal
  CABALVER=$(cabal --numeric-version) || exit 1
}

ensure_stack_yaml() {
  if test -n "$STACK_YAML"
  then
    require_file $STACK_YAML
  elif test ! -e stack.yaml
  then
    echo "Need cabal-install for 'stack init' to generate a stack.yaml"
    ensure_cabal $OS_APP_HOME/$OS_LOCAL_DIR/bin
    # solver seems to be broken with latest cabal
    echo "Trying to generate a stack.yaml"
    run_verbose $STACKCMD init --solver --ignore-subdirs || die "Solver failed to generate a stack.yaml.\n\
Please provide a working stack.yaml or use cabal build."
    require_file stack.yaml
  fi
  SDIST_STACKCMD=$STACKCMD
  test -z "$STACK_YAML" || SDIST_STACKCMD="$STACKCMD --stack-yaml $STACK_YAML"
  # We run the stack command from .packcheck/<package> dir after unpacking
  # sdist
  test -z "$STACK_YAML" || STACKCMD="$STACKCMD --stack-yaml ../../$STACK_YAML"
  echo "Using stack command [$STACKCMD]"
}

#------------------------------------------------------------------------------
# Create a dist, install deps and test
#------------------------------------------------------------------------------

get_pkg_name() {
  local name=$(echo *.cabal)
  test -f "$name" || die "One and only one .cabal file is required in the current directory."
  name=${name%.cabal}
  test -f "${name}.cabal" || \
    die "Cannot determine package name. File [${name}.cabal] does not exist"
  echo $name
}

get_pkg_full_name() {
  local pkgname
  local full_name
  pkgname=$(get_pkg_name) || exit 1
  full_name=$(cabal info . | awk '{ if ($1 == "*") {print $2; exit}}') || true
  if test -z "$full_name"
  then
    if test -n "$ENABLE_INSTALL"
    then
      die "'cabal info' command failed to determine package name.\nPlease disable install test by using 'ENABLE_INSTALL=' to avoid this issue."
    fi
    if test -z "$DISABLE_SDIST_BUILD"
    then
      die "'cabal info' command failed to determine package name.\nPlease use 'DISABLE_SDIST_BUILD=y' to avoid this issue."
    fi
  else
    if test "${pkgname}${full_name#$pkgname}" != "${full_name}"
    then
      die "Inconsistent package name [$pkgname] and package full name [$full_name]"
    fi
  fi

  echo $full_name
}

determine_build_type() {
  MULTI_PACKAGE_PROJECT=false
  echo "Looking for cabal or stack build files in the current directory..."
  local name=$(echo *.cabal)
  if test "$name" = "*.cabal"
  then
    if test -f "package.yaml" -a -n "$STACKCMD"
    then
        echo "No cabal file found but a package.yaml file found"
        echo "Generating cabal file from package.yaml"
        # Generate cabal file from package.yaml
        run_verbose "$STACKCMD query > /dev/null 2>&1"
    else
      if test $BUILD = "stack" -a -f "stack.yaml"
      then
        echo "No cabal file found but a stack.yaml file found, assuming a multipackage project."
        echo "Setting DISABLE_SDIST_BUILD=y, DISABLE_DIST_CHECKS=y, and clearing ENABLE_INSTALL"
        MULTI_PACKAGE_PROJECT=true
        DISABLE_SDIST_BUILD=y
        DISABLE_DIST_CHECKS=y
        ENABLE_INSTALL=
      else
        if test $BUILD = "cabal-new" -a -f "cabal.project"
        then
          echo "No cabal file found but a cabal.project file found, assuming a multipackage project."
          echo "Setting DISABLE_SDIST_BUILD=y, DISABLE_DIST_CHECKS=y, and clearing ENABLE_INSTALL"
          MULTI_PACKAGE_PROJECT=true
          DISABLE_SDIST_BUILD=y
          DISABLE_DIST_CHECKS=y
          ENABLE_INSTALL=
        else
          echo "No valid build config file cabal/cabal.project/package.yaml/stack.yaml found."
          die "Make sure you are using BUILD=cabal-new if you are using a cabal.project file"
        fi
      fi
    fi
  else
    if test ! -f "$name"
    then
      echo "Either there are multiple cabal files in the directory"
      echo "or the cabal file is not a regular file."
      die "cabal files: $name"
    else
      echo "Found [$name]"
    fi
  fi
}

ensure_cabal_config() {
  # When cabal versions change across builds on a CI host its safer to remove
  # the old config so that the build does not error out.
  local cfg="${OS_APP_HOME}/${OS_CABAL_DIR}/config"
  if test "$CABAL_REINIT_CONFIG" = y
  then
    echo "Removing old cabal config [$cfg]"
    run_verbose_errexit rm -f "$cfg"
  fi

  # cabal 1.22 and earlier do not support this command
  # We rely on the cabal info command to create the config.
  if test ! -e $cfg
  then
    run_verbose cabal user-config init || cabal info . > /dev/null || true
  fi

  if test "$BUILD" = cabal -o "$BUILD" = "cabal-new"
  then
    if test -n "$CABAL_HACKAGE_MIRROR"
    then
      cabal_use_mirror $CABAL_HACKAGE_MIRROR
    fi

    echo
    if test "$BUILD" = cabal 
    then
      echo "cabal update"
      retry_cmd cabal update
    else
      echo "cabal new-update"
      retry_cmd cabal new-update
    fi
  fi
}

# $1: dir where they are installed
remove_pkg_executables() {
  test -n "$(which_cmd cabal)" || return 0

  exes=$(cabal info . | awk '{if ($1 == "Executables:") { print $2; exit }}') || exit 1
  echo "Remove installed binaries"
  for i in $exes
  do
    # The executables may be under a cabal flag and may not have been installed
    # unless we used that flag. So just use "rm -f" to remove silently.
    run_verbose_errexit rm -f "$1"/"$i"
  done
}

install_cabal_deps() {
  if test "$CABAL_NO_SANDBOX" != "y"
  then
    run_verbose_errexit cabal sandbox init
  fi
  echo
  run_verbose_errexit cabal install $CABAL_DEP_OPTIONS
}

cabal_configure() {
    echo
    run_verbose_errexit cabal configure $CABAL_CONFIGURE_OPTIONS
}

# $1: package full name (name + ver)
create_and_unpack_pkg_dist() {
  local pkgtar=${1}.tar.gz
  local opts
  local SDIST_DIR
  local SDIST_CMD

  test -z "$SDIST_OPTIONS" || opts="$SDIST_OPTIONS"

  if test "$BUILD" = stack
  then
    # When custom setup is used we need to configure before we can use sdist.
    run_verbose_errexit $SDIST_STACKCMD build --only-configure
    SDIST_CMD="$SDIST_STACKCMD sdist $opts"
    SDIST_DIR=$($SDIST_STACKCMD path --dist-dir) || exit 1
  elif test -n "$CABAL_USE_STACK_SDIST"
  then
    # When custom setup is used we need to configure before we can use sdist.
    run_verbose_errexit $SDIST_STACKCMD --compiler=$COMPILER-$GHCVER build --only-configure
    SDIST_CMD="$SDIST_STACKCMD --compiler=$COMPILER-$GHCVER sdist $opts"
    SDIST_DIR=$($SDIST_STACKCMD --compiler=$COMPILER-$GHCVER path --dist-dir) || exit 1
  else
    # XXX We need to configure to use sdist and we need to install
    # dependencies to configure. So to just create the sdist we will
    # have to go through the whole process once and then again after
    # unpacking the sdist and to build it. If we use a sandbox then
    # we actually have to install the dependencies twice.
    if test "$BUILD" != "cabal-new"
    then
      install_cabal_deps
      cabal_configure
      SDIST_CMD="cabal sdist $opts"
      SDIST_DIR=dist
    else
      SDIST_CMD="cabal new-sdist $opts"
      SDIST_DIR=dist-newstyle/sdist
    fi
  fi

  # stack commands return path in windows format
  [[ `uname` != MINGW* ]] || SDIST_DIR=`cygpath ${SDIST_DIR}`

  local tarpath=${SDIST_DIR}/${pkgtar}
  rm -f $tarpath
  echo
  run_verbose_errexit $SDIST_CMD
  if test ! -f $tarpath
  then
    echo "$SDIST_CMD did not create [$tarpath]"
    exit 1
  fi

  # Unpack the tar inside .packcheck directory
  mkdir -p .packcheck || exit 1
  echo
  echo "cd .packcheck"
  cd .packcheck || exit 1
  test "${tarpath:0:1}" == / || tarpath=../$tarpath
  $OS_UNGZTAR_CMD $tarpath

  cd ${1}
  show_step "Package info [sdist $SDIST_OPTIONS]"
  run_verbose cabal info . || true

  if test -f "./configure.ac"
  then
    show_step "Run autoreconf"
    run_verbose_errexit autoreconf -i
  fi
}

install_deps() {
  case "$BUILD" in
    stack) run_verbose_errexit $STACKCMD build $STACK_DEP_OPTIONS ;;
    cabal-new) echo "No install dep step" ;;
    cabal) install_cabal_deps ;;
  esac
}

build_and_test() {
  case "$BUILD" in
    stack) run_verbose_errexit $STACKCMD build $STACK_BUILD_OPTIONS ;;
    cabal-new)
      run_verbose_errexit cabal new-build $GHCJS_FLAG $CABAL_NEWBUILD_OPTIONS $CABAL_NEWBUILD_TARGETS
      echo
      test -n "$DISABLE_DOCS" || run_verbose_errexit cabal new-haddock $GHCJS_FLAG $CABAL_NEWBUILD_OPTIONS $CABAL_NEWBUILD_TARGETS
      if test -z "$DISABLE_TEST"
      then
        local version
        local SHOW_DETAILS
        version=$(cabal --numeric-version|cut -f1,2 -d'.'|sed s/\\.//g)
        if test $version -ge 25
        then
          SHOW_DETAILS="--test-show-details=streaming"
        fi
        echo
        run_verbose_errexit cabal new-test $SHOW_DETAILS $GHCJS_FLAG $CABAL_NEWBUILD_OPTIONS $CABAL_NEWBUILD_TARGETS
      fi ;;
    cabal)
      cabal_configure
      echo
      run_verbose_errexit cabal build
      echo
      test -n "$DISABLE_DOCS" || run_verbose_errexit cabal haddock
      echo
      test -n "$DISABLE_TEST" || run_verbose_errexit cabal test --show-details=always ;;
  esac
}

dist_checks() {
  case "$BUILD" in
    stack) run_verbose_errexit $STACKCMD sdist ;;
    cabal|cabal-new)
      if test "$BUILD" != "cabal-new"
      then
        run_verbose_errexit cabal sdist
      else
        run_verbose_errexit cabal new-sdist
      fi

      echo
      if test "$CABAL_CHECK_RELAX" = y
      then
        run_verbose cabal check || true
      else
        run_verbose_errexit cabal check
      fi ;;
  esac
}

# $1 package name + ver
install_test() {
  case "$BUILD" in
    stack)
      run_verbose_errexit $STACKCMD install $STACK_BUILD_OPTIONS_ORIG
      # TODO test if the dist can be installed by cabal
      remove_pkg_executables $OS_APP_HOME/$OS_LOCAL_DIR/bin ;;
    cabal)
      run_verbose_errexit cabal copy
      (cd dist && run_verbose_errexit cabal install "${1}.tar.gz")
      remove_pkg_executables $OS_APP_HOME/$OS_CABAL_DIR/bin ;;
    cabal-new)
      echo "WARNING! Because of a cabal issue, ENABLE_INSTALL does not work with cabal-new" ;;
  esac
}

build_hlint() {
  if test -z "$(which_cmd hlint)"
  then
    show_step "Installing hlint..."
    if test -n "$(need_stack)"
    then
      ensure_stack ${OS_APP_HOME}/${OS_LOCAL_DIR}/bin
      ensure_ghc
      stack_install_tool hlint
    else
      ensure_cabal ${OS_APP_HOME}/${OS_LOCAL_DIR}/bin
      ensure_cabal_config
      ensure_ghc
      run_verbose_errexit cabal install hlint
    fi
  fi
  show_step "Running hlint commands..."
  run_verbose_errexit "$HLINT_COMMANDS"
}

# We run it only after a stack or cabal build so we are sure that stack or
# cabal are already installed.
coveralls_io() {
  if test -z "$(which_cmd hpc-coveralls)"
  then
    if test "$BUILD" = stack
    then
      stack_install_tool hpc-coveralls
    else
      run_verbose_errexit cabal install hpc-coveralls
    fi
  fi
  run_verbose_errexit hpc-coveralls $COVERALLS_OPTIONS
}

determine_package_full_name() {
  PACKAGE_FULL_NAME=$(get_pkg_full_name) || die "PACKAGE_FULL_NAME"
  echo "Package name and version: [$PACKAGE_FULL_NAME]"
}

# stack or cabal build (i.e. not hlint)
build_compile () {
  # ---------Install any tools needed--------
  show_step "Check and install build tools"

  test -z "$(need_stack)" \
    || ensure_stack ${OS_APP_HOME}/${OS_LOCAL_DIR}/bin \
    && echo
  # The tar installed by pacman does not seem to work. Maybe we need to have it
  # packed with msys itself.
  # ensure_msys_tools "tar" && require_cmd tar

  # This may use STACKCMD so happens after stack install
  determine_build_type && echo
  ensure_ghc && echo
  dont_need_cabal 'verbose' || ensure_cabal ${OS_APP_HOME}/${OS_LOCAL_DIR}/bin

  # use the stack installed 7z instead. depends on ensure ghc where we setup
  # stack paths.
  [[ `uname` != MINGW* ]] || require_cmd 7z

  show_step "Effective build config"
  show_build_config

  # ---------Create dist, unpack, install deps, test--------
  show_step "Build tools: package level and global configuration"
  dont_need_cabal || ensure_cabal_config
  if test -z "$DISABLE_SDIST_BUILD" -o -n "$ENABLE_INSTALL"
  then
    determine_package_full_name
  fi
  test -z "$(need_stack)" || ensure_stack_yaml

  if test -z "$DISABLE_SDIST_BUILD"
  then
    if test -f "./configure.ac"
    then
      echo "Package contains a 'configure.ac' file."
      echo "Checking for availability of 'autoreconf' command to regenerate "
      echo "the configure script before testing. Use DISABLE_SDIST_BUILD "
      echo "option if you do not have 'autoreconf' available"
      require_cmd autoreconf
    fi
    # Note this function leaves us in the package dir unpacked from sdist
    show_step "Prepare to build from source distribution"
    create_and_unpack_pkg_dist $PACKAGE_FULL_NAME
  fi

  show_step "Install package dependencies"
  install_deps

  show_step "Build and test"
  build_and_test

  if test -n "$COVERALLS_OPTIONS"
  then
      show_step "Send coverage info to coveralls.io"
      coveralls_io
  fi

  if test -z "$DISABLE_DIST_CHECKS"
  then
    show_step "Package distribution checks"
    dist_checks
  fi

  if test "$ENABLE_INSTALL" = y
  then
    show_step "Package install test"
    install_test $PACKAGE_FULL_NAME
  fi
}

eval_env() {
  while test -n "$1"
  do
    case "$1" in
      (*=*)
        key=${1%%=*}
        val=${1#*=}
        eval "$key=\"$val\""
        ;;
      (*)
        die "Expecting key=value pair, got [$1]"
        ;;
    esac
    shift
  done
}

# $1: prompt
get_confirmation()
{
  echo -n "$1"
  read -p "(y/n) :" ANSWER
  echo

  if test $ANSWER != "y"
  then
    echo "Aborted."
    exit
  fi
}

get_sys_time() {
  local os=$(uname)
  case "$os" in
    # Do not use floating point values so that we can avoid using bc for
    # computations.
    #Linux | MINGW*) date +%s.%N ;;
    Linux | MINGW*) date +%s ;;
    Darwin) date +%s ;;
    *) die "Unknown OS [$os]" ;;
  esac
}

get_rel_time() {
  echo $((`get_sys_time` - ${BASE_TIME}))
}

#------------------------------------------------------------------------------
# Main flow of script starts here
#------------------------------------------------------------------------------

set -e
set -o pipefail
test -n "$BASE_TIME" || BASE_TIME=$(get_sys_time)

test -n "$1" \
    || { short_help; echo -e "\nTry --help for detailed help"; exit 1; }

case $1 in
  cabal) shift; eval_env "$@"; BUILD=cabal;;
  cabal-new) shift; eval_env "$@"; BUILD=cabal-new;;
  stack) shift; eval_env "$@"; BUILD=stack;;
  clean) rm -rf .packcheck; exit;;
  cleanall)
    rm -rf .packcheck .stack-work
    if test -e cabal.sandbox.config
    then
      get_confirmation "Remove the cabal sandbox config? "
      rm -rf .cabal-sandbox
      rm -f cabal.sandbox.config
    else
      rm -rf .cabal-sandbox
    fi
    exit;;
  -h | --help | help) show_help; exit;;
  --version) show_version; exit;;
  *) short_help; exit 1 ;;
esac

test -z "$CHECK_ENV" || check_boolean_var CHECK_ENV
test -z "$CHECK_ENV" || check_clean_env

echo
bash --version

show_step "Build command"
show_build_command

TOOLS="awk cat curl cut date env head mkdir printf rm sleep tr which $OS_HAS_TOOLS"

show_step "Check basic tools"
require_cmd bash
for i in $TOOLS; do require_cmd $i; done

show_step "Build host machine information"
show_machine_info

# ---------Show, process and verify the config------------
show_step "Build environment"
show_build_env

# Determine home independent of the environment
export HOME=$(echo ~)
set_os_specific_vars # depends on HOME

# Set path for installed utilities, e.g. stack, cabal, hpc-coveralls
if test "$BUILD" = cabal -o "$BUILD" = "cabal-new"
then
  export PATH=$OS_APP_HOME/$OS_CABAL_DIR/bin:$PATH
fi
export PATH=$OS_APP_HOME/$OS_LOCAL_DIR/bin:$PATH

verify_build_config

# if we are running from a stack environment remove GHC_PACKAGE_PATH so that
# cabal does not complain
# XXX this should be done from outside via env
unset GHC_PACKAGE_PATH
# stack does not work well with empty STACK_YAML env var
test -n "$STACK_YAML" || unset STACK_YAML

if test -n "$HLINT_COMMANDS"
then
  build_hlint
else
  build_compile
fi

show_step "Done"

