with (import <nixpkgs> {}).lib;
{
  ## DO NOT CHANGE THIS
  format = "1.0.0";
  ## unless you made an automated or manual update
  ## to another supported format.

  ## The attribute to build from the local sources,
  ## either using nixpkgs data or the overlays located in `.nix/rocq-overlays`
  ## and `.nix/coq-overlays`
  ## Will determine the default main-job of the bundles defined below
  attribute = "verified-extraction";

  ## The attribute for coq compat shim, default to attribute
  ## set this when you need both to differ
  ## (for instance "rocq-elpi" and "coq-elpi")
  # coq-attribute = "verified-extraction";

  ## If you want to select a different attribute (to build from the local sources as well)
  ## when calling `nix-shell` and `nix-build` without the `--argstr job` argument
  # shell-attribute = "{{nix_name}}";

  ## Maybe the shortname of the library is different from
  ## the name of the nixpkgs attribute, if so, set it here:
  # pname = "{{shortname}}";

  ## Lists the dependencies, phrased in terms of nix attributes.
  ## No need to list Coq, it is already included.
  ## These dependencies will systematically be added to the currently
  ## known dependencies, if any more than Coq.
  ## /!\ Remove this field as soon as the package is available on nixpkgs.
  ## /!\ Manual overlays in `.nix/rocq-overlays` or `.nix/coq-overlays`
  ##     should be preferred then.

  ## Indicate the relative location of your _CoqProject
  ## If not specified, it defaults to "_CoqProject"
  # coqproject = "_CoqProject";

  ## select an entry to build in the following `bundles` set
  ## defaults to "default"
  default-bundle = "default";
  no-rocq-yet = true;

  ## write one `bundles.name` attribute set per
  ## alternative configuration
  ## When generating GitHub Action CI, one workflow file
  ## will be created per bundle
  bundles.default = { coqPackages = {
      coq.override.version = "9.1";
        equations.override.version = "1.3.1+9.1";
        metarocq-utils.override.version = "1.5.1-9.1";
        metarocq-erasure-plugin.override.version = "1.5.1-9.1";
        ceres-bs.override.version = "1.0.0";
    }; rocqPackages = {
      rocq-core.override.version = "9.1";
    };
    push-branches = [ "master" "rocq-9.1" ];
  };

  ## Cachix caches to use in CI
  ## Below we list some standard ones
  cachix.coq = {};
  cachix.math-comp = {};
  cachix.coq-community = {};

  ## If you have write access to one of these caches you can
  ## provide the auth token or signing key through a secret
  ## variable on GitHub. Then, you should give the variable
  ## name here. For instance, coq-community projects can use
  ## the following line instead of the one above:
  cachix.metarocq.authToken = "CACHIX_AUTH_TOKEN";

  ## Or if you have a signing key for a given Cachix cache:
  # cachix.my-cache.signingKey = "CACHIX_SIGNING_KEY"

  ## Note that here, CACHIX_AUTH_TOKEN and CACHIX_SIGNING_KEY
  ## are the names of secret variables. They are set in
  ## GitHub's web interface.
}
