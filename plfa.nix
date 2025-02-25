{ agdaPackages
, lib
, ...
}:
agdaPackages.mkDerivation {
  pname = "plfa";
  version = "0.1.0";

  src = builtins.path {
    path = lib.sources.cleanSource ./.;
    name = "agda-playground";
  };

  buildInputs = [ agdaPackages.standard-library ];

  everythingFile = "./Everything.agda";

  meta = {
    description = "Programming Language Foundations in Agda book from @wadler";
    platforms = lib.platforms.all;
  };
}
