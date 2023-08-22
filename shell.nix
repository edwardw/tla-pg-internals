with import <nixpkgs> {};

pkgs.mkShell {
	buildInputs = [
		tlaplus
		tlaplusToolbox
	];
}
