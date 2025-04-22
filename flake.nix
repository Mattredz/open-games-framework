{
  description = "Flake – ambiente Idris2 per la tesi (open‑games-framework)";

  inputs = {
    nixpkgs.url       = "github:NixOS/nixpkgs/nixos-unstable";
    flake-utils.url   = "github:numtide/flake-utils";
  };

  outputs = { self, nixpkgs, flake-utils, ... }:
    flake-utils.lib.eachDefaultSystem (system:
    let
      pkgs = import nixpkgs { inherit system; };
    in {
      # 'nix build' restituirà il compilatore idris2
      packages.default = pkgs.idris2;

      # dev‑shell condivisa
      devShell = pkgs.mkShell {
        name = "idris2-open-games-framework";
        buildInputs = with pkgs; [
          idris2
          gmp libffi zlib
        ];
        shellHook = ''
          echo "⇨ ambiente Idris2 attivo ($system)"
        '';
      };
    });
}
