{
  description = "abi-model: Lean model of Solcore's ABI encoding, differentially tested against Solcore";

  inputs = {
    solcore.url = "github:argotorg/solcore";
    nixpkgs.follows = "solcore/nixpkgs";
    flake-utils.follows = "solcore/flake-utils";
  };

  outputs = { self, solcore, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs { inherit system; };
        sc = solcore.packages.${system};
        evmoneLib = "${sc.evmone}/lib/libevmone${pkgs.stdenv.hostPlatform.extensions.sharedLibrary}";
        solcoreRev = solcore.rev or solcore.dirtyRev or "unknown";

        tools = [ sc.sol-core sc.testrunner pkgs.solc pkgs.jq pkgs.git pkgs.elan pkgs.coreutils ];

        env = ''
          export SOLCORE_SRC=${solcore}
          export SOLCORE_REV=${solcoreRev}
          export EVMONE=${evmoneLib}
        '';
      in {
        devShells.default = pkgs.mkShell {
          packages = tools;
          shellHook = env;
        };

        apps.diff = flake-utils.lib.mkApp {
          drv = pkgs.writeShellApplication {
            name = "abi-model-diff";
            runtimeInputs = tools;
            text = ''
              ${env}
              if [[ ! -f lakefile.lean || ! -x scripts/diff-solcore.sh ]]; then
                echo "run this from the abi-model repository root" >&2
                exit 2
              fi
              exec scripts/diff-solcore.sh "$@"
            '';
          };
        };
      });
}
