# Run `source env_vars.sh` to load.
cp resources/planout.configs $HOME/.planout.configs
export PLANOUT=$HOME/dev/PlanOutRepos/planout/compiler/planout.js
export PLANALYZER_CONFIG=$HOME/.planout.configs
export PATH=$PATH:"`pwd`/z3-4.5.0-x64-ubuntu-14.04/bin"