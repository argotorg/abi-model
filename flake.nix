{
  description = "abi-model: Lean model of Core Solidity's ABI encoding, differentially tested against solcore-rs";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url = "github:numtide/flake-utils";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    # The compiler under test. Only its sources are used: the `solcore` binary
    # is built below with the toolchain pinned by its rust-toolchain.toml.
    solcore-rs = {
      url = "github:argotorg/solcore-rs";
      flake = false;
    };
  };

  outputs = { self, nixpkgs, flake-utils, rust-overlay, solcore-rs, ... }:
    flake-utils.lib.eachDefaultSystem (system:
      let
        pkgs = import nixpkgs {
          inherit system;
          overlays = [ rust-overlay.overlays.default ];
        };
        rust = pkgs.rust-bin.fromRustupToolchainFile "${solcore-rs}/rust-toolchain.toml";
        rustPlatform = pkgs.makeRustPlatform { cargo = rust; rustc = rust; };
        solcoreRev = solcore-rs.rev or solcore-rs.dirtyRev or "unknown";

        solcore = rustPlatform.buildRustPackage {
          pname = "solcore";
          version = builtins.substring 0 7 solcoreRev;
          src = solcore-rs;
          cargoLock = {
            lockFile = "${solcore-rs}/Cargo.lock";
            allowBuiltinFetchGit = true;
          };
          cargoBuildFlags = [ "-p" "solcore-driver" "--bin" "solcore" ];
          doCheck = false;
        };

        tools = [ solcore pkgs.solc pkgs.foundry pkgs.curl pkgs.jq pkgs.git pkgs.elan pkgs.coreutils ];

        env = ''
          export SOLCORE=''${SOLCORE:-${solcore}/bin/solcore}
          export SOLCORE_STD=''${SOLCORE_STD:-${solcore-rs}/std}
          export SOLCORE_REV=''${SOLCORE_REV:-${solcoreRev}}
        '';
      in {
        packages.solcore = solcore;

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
